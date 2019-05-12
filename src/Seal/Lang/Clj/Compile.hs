{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
-- |
-- Module      :  Seal.Lang.Clj.Compile
--
-- Compiler from 'Exp' -> 'Term Name'
--

module Seal.Lang.Clj.Compile
    (
     compile
    ,parseCompile
    ,expToTerm
    )

where

import Seal.Prelude
import Text.Megaparsec hiding (dbg)
import qualified Text.Megaparsec as P
import Control.Arrow ((&&&),first)
import Bound
import Data.List (elemIndex)
import Data.Text (Text,pack)
import qualified Data.Text as T

import Seal.Lang.Common.Compiler
import Seal.Lang.Clj.Types.Compiler
import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Clj.Types.Term
import Seal.Lang.Common.Type
import Seal.Lang.Clj.Types.Type
import Seal.Lang.Clj.Parse (exprsOnly, parseString)

initParseState :: Maybe ModuleName -> Exp Info -> ParseState Exp CompileState
initParseState name e = ParseState e $ CompileState 0 name 

reserved :: [Text]
reserved = T.words "use defn true false let def ns"

compile :: [Exp Info] -> Either (Info, Text) [Term Name]
compile [] = return []
compile ei@(e:_) = runCompile (topTerms <* eof) (initParseState Nothing e) ei

parseCompile :: String -> Either String [Term Name]
parseCompile s = do
  exps <- parseString exprsOnly s
  let ei = fmap (mkStringInfo s <$>) exps
  mapLeft show $ compile ei

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
  body <- P.many (term)
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
      let divi = pack "/"
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

-- emptyDef :: Compile (Term Name)
-- emptyDef = do
--   modName <- currentModule
--   (defName, returnTy) <- first _atomAtom <$> typedAtom
--   args <- withList' Parens $ many arg
--   m <- meta ModelAllowed
--   info <- contextInfo
--   return $
--     TDef PUBLIC defName modName Defun
--     (FunType args returnTy) (abstract (const Nothing) (TList [] TyAny info)) m info


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
