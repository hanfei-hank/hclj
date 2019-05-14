{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

-- TODO This is to hide a warning involving `enforceKeySet`, which has a typeclass
-- constraint unused in the function itself, but is critical for preventing misuse
-- by a caller. There is probably a better way to enforce this restriction,
-- allowing us to remove this warning suppression.
-- See: https://github.com/kadena-io/pact/pull/206/files#r215468087
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

-- |
-- Module      :  Seal.Lang.Clj.Eval
--
-- clj interpreter.
--

module Seal.Lang.Clj.Eval
    ( reduce,reduceBody
    , resolveFreeVars,resolveArg
    , checkUserType
    , deref
    , instantiate'
    , liftTerm,apply,apply'
    , loadModule
    , evalUse, enscope
    , compile
    , parseCompile
    , expToTerm
    ) where

import Seal.Prelude hiding (getCallStack)
import Bound
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import Safe
import Control.Arrow hiding (app)
import Data.Graph

import Seal.Lang.Clj.Types.Runtime

import Data.List (elemIndex)
import qualified Data.Text as T
import Text.Megaparsec hiding (dbg)
import qualified Text.Megaparsec as P
import Seal.Lang.Common.Compiler
import Seal.Lang.Clj.Types.Compiler
import Seal.Lang.Clj.Parse (exprsOnly, parseString)

parseCompile :: String -> Either String [Term Name]
parseCompile s = do
  exps <- parseString exprsOnly s
  let ei = fmap (mkStringInfo s <$>) exps
  mapLeft show $ compile ei

compile :: [Exp Info] -> Either (Info, Text) [Term Name]
compile [] = return []
compile ei@(e:_) = runCompile (topTerms <* eof) (initParseState Nothing e) ei
  where
    initParseState :: Maybe ModuleName -> Exp Info -> ParseState Exp CompileState
    initParseState name e = ParseState e $ CompileState 0 name 

reserved :: [Text]
reserved = T.words "use defn true false let def ns"

currentModule :: Compile ModuleName
currentModule = use (psUser . csModule) >>= \case
  Just cm -> return cm  
  Nothing -> context >>= tokenErr' "Must be declared after ns"

freshTyVar :: Compile (Type (Term Name))
freshTyVar = do
  c <- state (view (psUser . csFresh) &&& over (psUser . csFresh) succ)
  return $ mkTyVar (cToTV c) []

cToTV :: Int -> TypeVarName
cToTV n | n < 26 = fromString [toC n]
        | n <= 26 * 26 = fromString [toC (pred (n `div` 26)), toC (n `mod` 26)]
        | otherwise = fromString $ toC (n `mod` 26) : show ((n - (26 * 26)) `div` 26)
  where toC i = toEnum (fromEnum 'a' + i)

term :: Compile (Term Name)
term =
  literal
  <|> varAtom
  <|> withList' Parens
    ((specialForm <|> app <|> keyget) <* eof)
  <|> listLiteral
  <|> objectLiteral

topTerms :: Compile [Term Name]
topTerms = 
        P.try ((:[]) <$> ns) 
   <|>  P.some (withList' Parens (specialForm <|> app <|> keyget))
  
-- parse ns module
ns :: Compile (Term Name)
ns = do
  modName' <- dbg "ns name" (withList' Parens nsDecl) 
  (psUser . csModule) .= Just (ModuleName modName')
  cs <- dbg "ns body" (P.many $ withList' Parens nsContent)
  m <- meta ModelAllowed
  i <- contextInfo
  let code = case i of
        Info Nothing -> "<code unavailable>"
        Info (Just (c,_)) -> c
      modName = ModuleName modName'
  return $ TModule
    (Module modName m code)
    (abstract (const Nothing) (TList cs TyAny i)) i
  where
    nsDecl = do
      vatom <- bareAtom
      n <- case _atomAtom vatom of
        "ns" -> _atomAtom <$> userAtom
        _    -> expected "ns form"
      return n

    nsContent = do
      AtomExp{..} <- dbg "atom" bareAtom
      case _atomAtom of
        "def" -> commit >> dbg "def" defconst
        "defn"  -> commit >> defn PUBLIC
        "defn-" -> commit >> defn PRIVATE
        _ -> expected "ns content"

keyget :: Compile (Term Name)
keyget = do
  body <- P.many term
  case body of
    [k@(TLiteral (LKeyword _) _), o@TObject {}] ->
      TApp (TVar (Name "get" def) def) [o, k] <$> contextInfo
    [o@TObject {}, k@(TLiteral (LKeyword _) _)] ->
      TApp (TVar (Name "get" def) def) [o, k] <$> contextInfo
    [k@(TLiteral (LKeyword _) _), o@TObject {}, defValue] ->
      TApp (TVar (Name "get" def) def) [o, k, defValue] <$> contextInfo
    [o@TObject {}, k@(TLiteral (LKeyword _) _), defValue] ->
      TApp (TVar (Name "get" def) def) [o, k, defValue] <$> contextInfo
    _ -> expected "special key get"

-- | User-available atoms (excluding reserved words).
userAtom :: Compile (AtomExp Info)
userAtom = do
  a@AtomExp{..} <- bareAtom
  when (_atomAtom `elem` reserved) $ unexpected' "reserved word"
  pure a

specialForm :: Compile (Term Name)
specialForm = do
  vatom <- bareAtom 
  return vatom >>= \AtomExp{..} -> case _atomAtom of
    -- "use" -> commit >> useForm
    -- "ns" -> commit >> nsForm
    "let" -> commit >> letForm
    -- "def" -> commit >> defconst
    -- "deftable" -> commit >> deftable
    -- "defn" -> commit >> defn PUBLIC
    -- "defn-" -> commit >> defn PRIVATE
    -- _ -> sf _atomAtom
    _ -> expected "special form"

expToTerm :: AtomExp Info -> Term Name
expToTerm AtomExp{..} = TVar (Name _atomAtom _atomInfo) _atomInfo

app :: Compile (Term Name)
app = do
  v <- varAtom
  body <- P.many term
  TApp v body <$> contextInfo

varAtom :: Compile (Term Name)
varAtom = do
  AtomExp{..} <- atom
  -- _ <- expected  (show _atomAtom)

  if _atomAtom `elem` division
    then do
      let n = Name _atomAtom _atomInfo
      commit 
      return $ TVar n _atomInfo
    else do
      let divi = "/"
      let as = T.splitOn divi _atomAtom
      case as of 
        [sa] -> do 
          -- let sa = pack $ reverse (unpack ssa) 
          when (sa `elem` reserved) $ unexpected' "reserved word"
          let n = Name sa _atomInfo
          commit
          return $ TVar n _atomInfo
        [q,a] -> do 
          when (q `elem` reserved) $ unexpected' "reserved word"
          when (a `elem` reserved) $ unexpected' "reserved word"
          let n = QName (ModuleName q) a _atomInfo
          commit
          return $ TVar n _atomInfo
        _ -> expected "single qualifier"

division :: [Text]
division = T.words "/"

listLiteral :: Compile (Term Name)
listLiteral = withList Brackets $ \ListExp{..} -> do
  ls <- P.many term
  let lty = case nub (map typeof ls) of
              [Right ty] -> ty
              _ -> TyAny
  pure $ TList ls lty _listInfo
  
objectLiteral :: Compile (Term Name)
objectLiteral =
  withList Braces $ \ListExp {..} -> do
    let pair = do
          key <- term
          val <- term
          return (key, val)
    ps <- P.many pair
    return $ TObject ps TyAny _listInfo

literal :: Compile (Term Name)
literal = lit >>= \LiteralExp{..} ->
  commit >> return (TLiteral _litLiteral _litInfo)


defconst :: Compile (Term Name)
defconst = do
  modName <- currentModule
  a <- arg
  v <- term

  m <- meta ModelNotAllowed
  TConst a modName (CVRaw v) m <$> contextInfo

data ModelAllowed
  = ModelAllowed
  | ModelNotAllowed

meta :: ModelAllowed -> Compile Meta
meta modelAllowed = atPairs <|> P.try docStr <|> return def
  where
    docStr = Meta <$> (Just <$> str) <*> pure []
    docPair = symbol "@doc" >> str
    modelPair = do
      symbol "@model"
      (ListExp exps _ _i, _) <- list' Brackets
      pure exps
    atPairs = do
      doc <- optional (P.try docPair)
      model <- optional (P.try modelPair)
      case (doc, model, modelAllowed) of
        (Nothing, Nothing    , ModelAllowed   ) -> expected "@doc or @model declarations"
        (Nothing, Nothing    , ModelNotAllowed) -> expected "@doc declaration"
        (_      , Just model', ModelAllowed   ) -> return (Meta doc model')
        (_      , Just _     , ModelNotAllowed) -> syntaxError "@model not allowed in this declaration"
        (_      , Nothing    , _              ) -> return (Meta doc [])

defn :: DefVisibility -> Compile (Term Name)
defn visibility = do
  modName <- currentModule
  (defname,returnTy) <- first _atomAtom <$> typedAtom
  args <- withList' Brackets $ P.many arg --[]
  m <- meta ModelAllowed
  TDef visibility defname modName (FunType args returnTy)
    <$> abstractBody args <*> pure m <*> contextInfo


letBindings :: Compile [(Arg (Term Name),Term Name)]
letBindings = withList' Brackets $ -- []
              P.some $
              (,) <$> arg <*> term

abstractBody :: [Arg (Term Name)] -> Compile (Scope Int Term Name)
abstractBody args = abstractBody' args <$> bodyForm

abstractBody' :: [Arg (Term Name)] -> Term Name -> Scope Int Term Name
abstractBody' args = abstract (`elemIndex` bNames)
  where bNames = map arg2Name args


-- | let* is a macro to nest lets for referencing previous
-- bindings.
letForm :: Compile (Term Name)
letForm = do
  bindings <- letBindings
  let nest (binding:rest) = do
        let bName = [arg2Name (fst binding)]
        scope <- abstract (`elemIndex` bName) <$> case rest of
          [] -> bodyForm
          _ -> do
            rest' <- nest rest
            pure $ TList [rest'] TyAny def
        TBinding [binding] scope BindLet <$> contextInfo
      nest [] =  syntaxError "letForm: invalid state (bug)"
  nest bindings
  
typedAtom :: Compile (AtomExp Info,Type (Term Name))
typedAtom = flip (,) <$> (typed <|> freshTyVar) <*> userAtom

arg :: Compile (Arg (Term Name))
arg = typedAtom >>= \(AtomExp{..},ty) ->
  return $ Arg _atomAtom ty _atomInfo

arg2Name :: Arg n -> Name
arg2Name Arg{..} = Name _aName _aInfo


typed :: Compile (Type (Term Name))
typed = sep SCaret *> parseType

parseType :: Compile (Type (Term Name))
parseType = msum
  [ parseListType
  , parseUserSchemaType
  , parseSchemaType tyObject TyObject
  , TyPrim TyInteger <$ symbol tyInteger
  , TyPrim TyDecimal <$ symbol tyDecimal
  , TyPrim TyTime    <$ symbol tyTime
  , TyPrim TyBool    <$ symbol tyBool
  , TyPrim TyString  <$ symbol tyString
  , TyList TyAny     <$ symbol tyList
  , TyPrim TyKeyword  <$ symbol tyKeyword
  ]

parseListType :: Compile (Type (Term Name))
parseListType = withList' Brackets $ TyList <$> parseType

parseSchemaType :: Text -> SchemaType -> Compile (Type (Term Name))
parseSchemaType tyRep sty = symbol tyRep >>
  (TySchema sty <$> (parseUserSchemaType <|> pure TyAny))


parseUserSchemaType :: Compile (Type (Term Name))
parseUserSchemaType = withList Braces $ \ListExp{..} -> do
  AtomExp{..} <- userAtom
  return $ TyUser (return $ Name _atomAtom _listInfo)

bodyForm :: Compile (Term Name)
bodyForm = do
  (bs,i) <- bodyForm'
  return $ TList bs TyAny i

bodyForm' :: Compile ([Term Name],Info)
bodyForm' = (,) <$> P.some term <*> contextInfo

------------------------ Eval ------------------------------
-- Hoist Name back to ref
liftTerm :: Term Name -> Term Ref
liftTerm a = TVar (Direct a) def

-- | Re-application of 'f as' with additional args.
apply :: HasEval env => Term Ref -> [Term Ref] -> Info -> [Term Name] ->  RIO env (Term Name)
apply f as i as' = reduce (TApp f (as ++ map liftTerm as') i)

-- | Unsafe version of 'apply' where first arg is assumed to be a 'TApp',
-- to which additional args are applied.
apply' :: HasEval env => Term Ref -> [Term Name] -> RIO env (Term Name)
apply' app as' = apply (_tAppFun app) (_tAppArgs app) (_tInfo app) as'

evalUse :: HasEval env => ModuleName -> Info -> RIO env ()
evalUse mn i = do
  mm <- preview (rsModules . ix mn) <$> getRefStore
  case mm of
    Nothing -> evalError i $ "Contract " ++ show mn ++ " not found"
    Just md -> do
      installModule md

-- | Make table of contract definitions for storage in namespace/RefStore.
loadModule :: HasEval env => Module -> Scope n Term Name -> Info -> RIO env (HM.HashMap Text (Term Name))
loadModule m@Module{..} bod1 mi = do
  modDefs1 <-
    case instantiate' bod1 of
      (TList bd _ _bi) -> do
        let doDef rs t = do
              dnm <- case t of
                TDef {..} -> return $ Just _tDefName
                TConst {..} -> return $ Just $ _aName _tConstArg
                -- TUse {..} -> evalUse _tModuleName _tInfo >> return Nothing
                _ -> evalError (_tInfo t) "Invalid contract member"
              case dnm of
                Nothing -> return rs
                Just dn -> do
                  -- g' <- computeGas (Left (_tInfo t,dn)) (GModuleMember m)
                  return ((dn,t):rs)
        HM.fromList <$> foldM doDef [] bd
      t -> evalError (_tInfo t) "Malformed contract"
  evaluatedDefs <- evaluateDefs mi modDefs1
  let md = ModuleData m $ filterOutPrivateDefs modDefs1 evaluatedDefs
  installModule md
  modifyRefState $ rsNewModules %~ HM.insert _mName md
  return modDefs1


-- 过滤掉private函数
filterOutPrivateDefs :: HM.HashMap Text (Term Name) -> HM.HashMap Text Ref -> HM.HashMap Text Ref
filterOutPrivateDefs defs = HM.filterWithKey isNotPrivateDef
  where
    isNotPrivateDef dn _ =
      case HM.lookup dn defs of
        Nothing -> False
        Just (TDef PRIVATE _ _ _ _ _ _) -> False
        _ -> True

-- | Definitions are transformed such that all free variables are resolved either to
-- an existing ref in the refstore/namespace ('Right Ref'), or a symbol that must
-- resolve to a definition in the contract ('Left String'). A graph is formed from
-- all 'Left String' entries and enforced as acyclic, proving the definitions
-- to be non-recursive. The graph is walked to unify the Either to
-- the 'Ref's it already found or a fresh 'Ref' that will have already been added to
-- the table itself: the topological sort of the graph ensures the reference will be there.
evaluateDefs :: HasEval env => Info -> HM.HashMap Text (Term Name) -> RIO env (HM.HashMap Text Ref)
evaluateDefs info defs = do
  cs <- traverseGraph defs
  sortedDefs <- forM cs $ \case
        AcyclicSCC v -> return v
        CyclicSCC vs -> evalError (case vs of [] -> info; v:_ -> _tInfo $ view _1 v) $
          "Recursion detected: " ++ show vs
  let dresolve ds (d,dn,_) = HM.insert dn (Ref $ unify ds <$> d) ds
      unifiedDefs = foldl dresolve HM.empty sortedDefs
  traverse (evalConsts) unifiedDefs

traverseGraph :: HasEval env => HM.HashMap Text (Term Name) -> RIO env [SCC (Term (Either Text Ref), Text, [Text])]
traverseGraph defs = fmap stronglyConnCompR $ forM (HM.toList defs) $ \(dn,d) -> do
  d' <- forM d $ \(f :: Name) -> do
    dm <- resolveRef f
    case (dm, f) of
      (Just t, _) -> return (Right t)
      (Nothing, Name fn _) ->
        case HM.lookup fn defs of
          Just _ -> return (Left fn)
          Nothing -> evalError (_nInfo f) $ "Cannot resolve \"" ++ show f ++ "\""
      (Nothing, _) -> evalError (_nInfo f) $ "cannot resolve \"" ++ show f ++ "\""
  return (d', dn, mapMaybe (either Just (const Nothing)) $ toList d')

-- | Compare implemented member signatures with their definitions.
-- At this stage, we have not merged consts, so we still check for overlap
solveConstraint
  :: HasEval env => Info -> HM.HashMap Text Ref -> Text -> Ref -> RIO env () -> RIO env ()
solveConstraint info _ refName (Direct t) _ =
  evalError info $ "found native reference " ++ show t ++ " while resolving contract contraints: " ++ show refName
solveConstraint info em refName (Ref t) _ =
  case HM.lookup refName em of
    Nothing -> pure ()
    Just (Direct s) ->
      evalError info $ "found native reference " ++ show s ++ " while resolving contract contraints: " ++ show t
    Just (Ref s) ->
      case (t, s) of
        (TDef _ _n _mn (FunType args rty) _ _ _,
          TDef _ _n' _mn' (FunType args' rty') _ _ _) -> do
          -- when (dt /= dt') $ evalError info $ "deftypes mismatching: " ++ show dt ++ "\n" ++ show dt'
          when (rty /= rty') $ evalError info $ "return types mismatching: " ++ show rty ++ "\n" ++ show rty'
          when (length args /= length args') $ evalError info $ "mismatching argument lists: " ++ show args ++ "\n" ++ show args'
          forM_ (args `zip` args') $ \((Arg n ty _), (Arg n' ty' _)) -> do
            when (n /= n') $ evalError info $ "mismatching argument names: " ++ show n ++ " and " ++ show n'
            when (ty /= ty') $ evalError info $ "mismatching types: " ++ show ty ++ " and " ++ show ty'
        _ -> evalError info $ "found overlapping const refs - please resolve: " ++ show t


-- | This should be impure. See 'evaluateDefs'. Refs are
-- expected to exist, and if they don't, it is a serious bug
unify :: HM.HashMap Text Ref -> Either Text Ref -> Ref
unify _ (Right r) = r
unify m (Left t) = m HM.! t

evalConsts :: HasEval env => Ref -> RIO env Ref
evalConsts (Ref r) = case r of
  c@TConst {..} -> case _tConstVal of
    CVRaw raw -> do
      v <- reduce =<< traverse evalConsts raw
      traverse reduce _tConstArg >>= \a -> typecheck [(a,v)]
      return $ Ref (TConst _tConstArg _tModule (CVEval raw $ liftTerm v) _tMeta _tInfo)
    _ -> return $ Ref c
  _ -> Ref <$> traverse evalConsts r
evalConsts r = return r


deref :: HasEval env => Ref -> RIO env (Term Name)
deref (Direct n) = return n
deref (Ref r) = reduce r

-- | Only can be used by "static" terms with no refs/variables in them
unsafeReduce :: HasEval env => Term Ref -> RIO env (Term Name)
unsafeReduce t = return (t >>= const (tStr "Error: unsafeReduce on non-static term"))


-- | Main function for reduction/evaluation.
reduce :: HasEval env => Term Ref ->  RIO env (Term Name)
reduce (TApp f as ai) = reduceApp f as ai
reduce (TVar t _) = deref t
reduce t@TLiteral {} = unsafeReduce t
reduce TList {..} = TList <$> mapM reduce _tList <*> traverse reduce _tListType <*> pure _tInfo
reduce t@TDef {} = return $ tStr $ toText $ show t
reduce t@TNative {} = return $ tStr $ toText $ show t
reduce TConst {..} = case _tConstVal of
  CVEval _ t -> reduce t
  CVRaw a -> evalError _tInfo $ "internal error: reduce: unevaluated const: " ++ show a
reduce (TObject ps t i) =
  TObject <$> forM ps (\(k,v) -> (,) <$> reduce k <*> reduce v) <*> traverse reduce t <*> pure i
reduce (TBinding ps bod c i) = case c of
  BindLet -> reduceLet ps bod i
reduce t@TModule{} = evalError (_tInfo t) "Modules and Interfaces only allowed at top level"
reduce t@TUse {} = evalError (_tInfo t) "Use only allowed at top level"

mkDirect :: Term Name -> Term Ref
mkDirect = (`TVar` def) . Direct

reduceBody :: HasEval env => Term Ref -> RIO env (Term Name)
reduceBody (TList bs' _ i) = case nonEmpty bs' of
  Nothing -> evalError i "Expected non empty body"
  Just bs -> last <$> mapM reduce bs
reduceBody t = evalError (_tInfo t) "Expected body forms"

reduceLet :: HasEval env => [(Arg (Term Ref),Term Ref)] -> Scope Int Term Ref -> Info -> RIO env (Term Name)
reduceLet ps bod i = do
  ps' <- mapM (\(a,t) -> (,) <$> traverse reduce a <*> reduce t) ps
  typecheck ps'
  reduceBody (instantiate (resolveArg i (map (mkDirect . snd) ps')) bod)


{-# INLINE resolveArg #-}
resolveArg :: Info -> [Term n] -> Int -> Term n
resolveArg ai as i = fromMaybe (appError ai $ toText $ "Missing argument value at index " ++ show i) $
                     as `atMay` i

appCall :: HasEval env => Show t => FunApp -> Info -> [Term t] -> RIO env a -> RIO env a
appCall fa ai as = call (StackFrame (_faName fa) ai (Just (fa,map (toText.abbrev) as)))

reduceApp :: HasEval env => Term Ref -> [Term Ref] -> Info ->  RIO env (Term Name)
reduceApp (TVar (Direct t) _) as ai = reduceDirect t as ai
reduceApp (TVar (Ref r) _) as ai = reduceApp r as ai
reduceApp TDef {..} as ai = do
  -- g <- computeGas (Left (_tInfo, toText _tDefName)) GUser
  as' <- mapM reduce as
  ft' <- traverse reduce _tFunType
  typecheck (zip (_ftArgs ft') as')
  let bod' = instantiate (resolveArg ai (map mkDirect as')) _tDefBody
      fa = FunApp _tInfo _tDefName (Just _tModule) (funTypes ft') (_mDocs _tMeta)
  appCall fa ai as $ reduceBody bod'
      -- Defpact -> applyPact bod'
reduceApp (TLitString errMsg) _ i = evalError i $ toString errMsg
reduceApp r _ ai = evalError ai $ "Expected def: " ++ show r

reduceDirect :: HasEval env => Term Name -> [Term Ref] -> Info ->  RIO env (Term Name)
reduceDirect TNative {..} as ai =
  let fa = FunApp ai (toText _tNativeName) Nothing _tFunTypes (Just _tNativeDocs)
      -- toplevel: only empty callstack or non-contract-having callstack allowed
      enforceTopLevel = traverse_ $ \c ->
        case preview (sfApp . _Just . _1 . faModule . _Just) c of
          Nothing -> return ()
          Just m -> evalError ai $ "Top-level call used in contract " ++ show m ++
            ": " ++ show _tNativeName
  in do
    when _tNativeTopLevelOnly $ getCallStack >>= enforceTopLevel
    appCall fa ai as $ _nativeFun _tNativeFun fa as

reduceDirect (TLitString errMsg) _ i = evalError i $ toString errMsg
reduceDirect r _ ai = evalError ai $ "Unexpected non-native direct ref: " ++ show r


-- | Create special error form handled in 'reduceApp'
appError :: Info -> Text -> Term n
appError i errMsg = TApp (tStr errMsg) [] i

resolveFreeVars ::  HasEval env => Info -> Scope d Term Name ->  RIO env (Scope d Term Ref)
resolveFreeVars i b = traverse r b where
    r fv = resolveRef fv >>= \case
             Nothing -> evalError i $ "Cannot resolve " ++ show fv
             Just d -> return d

installModule :: HasEval env => ModuleData ->  RIO env ()
installModule ModuleData{..} = do
  modifyRefState $ rsLoaded %~ HM.union (HM.fromList . map (first (`Name` def)) . HM.toList $ _mdRefMap)
  let n = case _mdModule of
        Module{..} -> _mName
  modifyRefState $ rsLoadedModules %~ HM.insert n _mdModule

enscope ::  HasEval env => Term Name ->  RIO env (Term Ref)
enscope t = instantiate' <$> (resolveFreeVars (_tInfo t) . abstract (const Nothing) $ t)

instantiate' :: Scope n Term a -> Term a
instantiate' = instantiate1 (tStr ("No bindings" :: Text))

-- | Runtime input typecheck, enforced on let bindings, consts, user defun app args.
-- Output checking -- app return values -- left to static TC.
-- Native funs not checked here, as they use pattern-matching etc.
typecheck :: HasEval env => [(Arg (Term Name),Term Name)] -> RIO env ()
typecheck ps = void $ foldM tvarCheck M.empty ps where
  tvarCheck m (Arg {..},t) = do
    r <- typecheckTerm _aInfo _aType t
    case r of
      Nothing -> return m
      Just (v,ty) -> case M.lookup v m of
        Nothing -> return $ M.insert v ty m
        Just prevTy | prevTy == ty -> return m
                    | otherwise ->
                        evalError (_tInfo t) $ "Type error: values for variable " ++ show _aType ++
                        " do not match: " ++ show (prevTy,ty)

-- | 'typecheckTerm i spec t' checks a Term 't' against a specified type 'spec'.
-- Returns `Nothing` on successful check against concrete/untyped,
-- or `Just` a pair for successful check against a type variable, where
-- the pair is the type variable itself and the term type.
typecheckTerm 
  :: HasEval env => Info -> Type (Term Name) -> Term Name -> RIO env (Maybe (TypeVar (Term Name),Type (Term Name)))
typecheckTerm i spec t = do

  ty <- case typeof t of
    Left s -> evalError i $ "Invalid type in value location: " ++ toString s
    Right r -> return r

  let

    -- tcFail :: Show a => a -> RIO env b
    tcFail found = evalError i $
      "Type error: expected " ++ show spec ++ ", found " ++ show found

    tcOK = return Nothing

    -- | check container parameterized type.
    -- 'paramCheck pspec pty check' check specified param ty 'pspec' with
    -- value param ty 'pty'. If not trivially equal, use 'check'
    -- to determine actual container value type, and compare for equality
    -- with specified.
    -- paramCheck :: Type (Term Name)
    --            -> Type (Term Name)
    --            -> (Type (Term Name) -> RIO env (Type (Term Name)))
    --            -> RIO env (Maybe (TypeVar (Term Name),Type (Term Name)))
    paramCheck TyAny _ _ = tcOK -- no spec
    paramCheck pspec pty check
      | pspec == pty = tcOK -- equality OK
      | otherwise = do
          -- run check function to get actual content type
          checked <- check pspec
          -- final check expects full match with toplevel 'spec'
          if checked == spec then tcOK else tcFail checked

    -- | infer list value type
    checkList es lty = return $ TyList $
                    case nub (map typeof es) of
                      [Right a] -> a -- uniform value type: return it
                      [] -> lty -- empty: return specified
                      _ -> TyAny -- otherwise untyped

  case (spec,ty,t) of
    (_,_,_) | spec == ty -> tcOK -- identical types always OK
    (TyAny,_,_) -> tcOK -- var args are untyped
    (TyVar {..},_,_) ->
      if spec `canUnifyWith` ty
      then return $ Just (_tyVar,ty) -- collect found types under vars
      else tcFail ty -- constraint failed
    -- check list
    (TyList lspec,TyList lty,TList {..}) ->
      paramCheck lspec lty (checkList _tList)
    -- check object
    (TySchema TyObject ospec,TySchema TyObject oty,TObject {..}) ->
      paramCheck ospec oty (checkUserType True i _tObject)
    _ -> tcFail ty

-- | check object args. Used in 'typecheckTerm' above and also in DB writes.
-- Total flag allows for partial row types if False.
checkUserType :: HasEval env => Bool -> Info  -> [(Term Name,Term Name)] -> Type (Term Name) -> RIO env (Type (Term Name))
checkUserType _ i _ t = evalError i $ "Invalid reference in user type: " ++ show t

