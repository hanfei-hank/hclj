{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      :  Seal.Lang.Clj.Native
--
-- clj builtins/standard library.
--

module Seal.Lang.Clj.Native
    (natives
    ,langDefs
    ,moduleToMap
    ,lengthDef
    ,cljVersionDef
    ,formatDef
    ,ifDef
    ,lookupObj
    ) where

import Control.Lens hiding (parts,Fold,contains)
import Prelude (read)
import Seal.Prelude hiding (contains, identity, list)
import qualified Seal.Prelude.Unsafe as Unsafe
import Unsafe.Coerce

import Data.Char (isHexDigit, digitToInt)
import Data.Decimal
import qualified Data.Foldable as Foldable
import Data.List (elemIndex, lookup)
import qualified Data.Attoparsec.Text as AP
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T (isInfixOf, length, all, splitOn, null, foldl', append)
import Safe
import Control.Arrow hiding (app)
import Data.Function (on)

import Seal.Lang.Clj.Eval
import Seal.Lang.Clj.Native.Internal
import Seal.Lang.Clj.Native.Time
import Seal.Lang.Clj.Native.Ops
import Seal.Lang.Clj.Types.Runtime

cljVersion :: Text
cljVersion = "1.0.0"

-- | All production native modules.
natives :: HasEval env => [NativeModule env]
natives = [
  langDefs,
  timeDefs,
  opDefs]


moduleToMap :: NativeModule env -> M.HashMap Name Ref
moduleToMap = M.fromList . map (((`Name` def) . toText) *** Direct) . map f .  snd
  where f (n, isTop, fun, ftype, docs) = (n, TNative n (NativeDFun n (unsafeCoerce fun)) ftype docs isTop def)

lengthDef :: HasEval env => NativeDef env
lengthDef = defRNative "count" count' (funType tTyInteger [("x",listA)])
 "Compute length of X, which can be a list, a string, or an object.\
 \`(count [1 2 3])` `(count \"abcdefgh\")` `(count { \"a\": 1, \"b\": 2 })`"

listA :: Type n
listA = mkTyVar "a" [TyList (mkTyVar "l" []),TyPrim TyString,TySchema TyObject (mkSchemaVar "o")]

cljVersionDef :: HasEval env => NativeDef env
cljVersionDef = setTopLevelOnly $ defRNative "seal-version"
  (\_ _ -> return $ toTerm $ toLiteral cljVersion)
  (funType tTyString [])
  "Obtain current seal build version. `(seal-version)`"


format' :: HasEval env => FunApp -> Text -> [Term Name] -> RIO env (Term Name)
format' i s es = do
      let parts = T.splitOn "{}" s
          plen = length parts
          rep (TLitString t) = t
          rep t = toText $ show t
      if plen == 1
      then return $ tStr s
      else if plen - length es > 1
           then evalError' i "format: not enough arguments for template"
           else return $ tStr $
                foldl'
                  (\r (e,t) -> r <> rep e <> t)
                  (Unsafe.head parts)
                  (zip es (Unsafe.tail parts))


formatDef :: HasEval env => NativeDef env
formatDef =
  defRNative "format" format
  (funType tTyString [("template",tTyString),("vars",TyList TyAny)])
  "Interpolate VARS into TEMPLATE using {}. \
  \`(format \"My {} has {}\" [\"dog\" \"fleas\"])`"
  where

    format i (TLitString s : es) = format' i s es
    format i as = argsError i as

printfDef :: HasEval env => NativeDef env
printfDef =
  defRNative "printf" printf
  (funType tTyString [("template",tTyString),("vars",TyList TyAny)])
  "Interpolate VARS into TEMPLATE using {}. \
  \`(printf \"My {} has {}\" [\"dog\" \"fleas\"])`"
  where

    -- printf i [TLitString s] = putTextLn s >> return (tStr "")
    printf i (TLitString s : es) = do
        msg <- format' i s es 
        putStrLn $ show msg
        return msg
    printf i as = argsError i as



ifDef :: HasEval env => NativeDef env
ifDef = defNative "if" if' (funType a [("cond",tTyBool),("then",a),("else",a)])
  "Test COND. If true, evaluate THEN. Otherwise, evaluate ELSE. \
  \`(if (= (+ 2 2) 4) \"Sanity prevails\" \"Chaos reigns\")`"
  where

    if' i [cond,then',else'] = reduce cond >>= \case
               TLiteral (LBool False) _ -> reduce else'
               t -> reduce then'
              --  t -> evalError' i $ "if: conditional not boolean: " ++ show t
    if' i as = argsError' i as

-- do 
do' i = go
  where
    go [exp] = reduce exp
    go (exp:as) = reduce exp >> go as

doDef :: HasEval env => NativeDef env
doDef = defNative "do" do' (funType a []) "do"

whenDef :: HasEval env => NativeDef env
whenDef = defNative "when" when' (funType a []) "when"
  where
    when' i (cond:as) = reduce cond >>= \case
        TLiteral (LBool False) _ -> return $ toTermLiteral False
        t -> do' i as
        -- t -> evalError' i $ "when: conditinal not boolean: " ++ show t
    when' i as = argsError' i as

whileDef :: HasEval env => NativeDef env
whileDef = defNative "while" while' (funType a []) "while"
  where
    while' i (cond:as) = reduce cond >>= \case
        TLiteral (LBool c) _ 
          | c == True -> do' i as >> while' i (cond:as)
          | otherwise -> return $ toTermLiteral False
        t -> evalError' i $ "while: conditinal not boolean: " ++ show t
    while' i as = argsError' i as

-- atom support TODO: seperate file
atomDef :: HasEval env => NativeDef env
atomDef = defRNative "atom" atom' (funType a []) "atom"
  where
    atom' i [v] = do
        -- putStrLn $ "new atom" <> show v
        ref <- newIORef v
        return $ TAtom ref def
    atom' i as = argsError i as

derefDef :: HasEval env => NativeDef env
derefDef = defRNative "deref" deref' (funType a []) "deref"
  where
    deref' i [TAtom ref _] = readIORef ref
    deref' i as = argsError i as

resetAtomDef :: HasEval env => NativeDef env
resetAtomDef = defRNative "reset!" reset' (funType a []) "reset"
  where
    reset' i [TAtom ref _, !v] = do
        putStrLn $ "reset " <> show v
        writeIORef ref v
        return v
    reset' i as = argsError i as

langDefs :: HasEval env => NativeModule env
langDefs =
    ("General",[
     ifDef,doDef,whenDef,whileDef
    ,atomDef, derefDef, resetAtomDef
    ,defNative "map" map'
     (funType (TyList a) [("app",lam b a),("list",TyList b)])
     "Apply APP to each element in LIST, returning a new list of results. \
     \`(map (+ 1) [1 2 3])`"

     ,defRNative "empty?" empty'
     (funType (TyList a) [("app",lam b a),("list",TyList b)])
     "Apply APP to each element in LIST, returning a new list of results. \
     \`(map (+ 1) [1 2 3])`"

    ,defNative "reduce" reduce'
     (funType a [("app",lam2 a b a),("init",a),("list",TyList b)])
     "Iteratively reduce LIST by applying APP to last result and element, starting with INIT. \
     \`(reduce (+) 0 [100 10 5])`"

    ,defRNative "list" list
     (funType (TyList TyAny) [("elems",TyAny)])
     "Create list from ELEMS. Deprecated in clj 2.1.1 with literal list support. `(list 1 2 3)`"

    ,defRNative "make-array" makeArray (funType (TyList a) [("value",a),("length",tTyInteger)])
     "Create list by repeating VALUE LENGTH times. `(make-array true 5)`"

    ,defRNative "reverse" reverse' (funType (TyList a) [("list",TyList a)])
     "Reverse LIST. `(reverse [1 2 3])`"

    ,defNative "filter" filter'
     (funType (TyList a) [("app",lam a tTyBool),("list",TyList a)])
     "Filter LIST by applying APP to each element. For each true result, the original value is kept.\
     \`(filter (comp (count) (< 2)) [\"my\" \"dog\" \"has\" \"fleas\"])`"

    ,defRNative "sort" sort'
     (funType (TyList a) [("values",TyList a)] <>
      funType (TyList (tTyObject (mkSchemaVar "o"))) [("fields",TyList tTyString),("values",TyList (tTyObject (mkSchemaVar "o")))])
     "Sort a homogeneous list of primitive VALUES, or objects using supplied FIELDS list. \
     \`(sort [3 1 2])` `(sort ['age] [{'name: \"Lin\",'age: 30} {'name: \"Val\",'age: 25}])`"

     ,defNative "comp" comp' (funType a [("value",a)] <>
                             funType b [("appA", lam a b),("value",a)] <>
                             funType c [("appA", lam b c),("appB",lam a b),("value",a)] <>
                             funType d [("appA", lam c d),("appB", lam b c),("appC",lam a b),("value",a)]
                             )
     "Compose X and Y, such that X operates on VALUE, and Y on the results of X. \
     \`(filter (comp (count) (< 2)) [\"my\" \"dog\" \"has\" \"fleas\"])`"

     ,lengthDef

    ,defRNative "take" take' takeDrop
     "Take COUNT values from LIST (or string), or entries having keys in KEYS from OBJECT. If COUNT is negative, take from end. \
     \`(take 2 \"abcd\")` `(take (- 3) [1 2 3 4 5])` `(take ['name] { 'name: \"Vlad\", 'active: false})`"

    ,defRNative "drop" drop' takeDrop
     "Drop COUNT values from LIST (or string), or entries having keys in KEYS from OBJECT. If COUNT is negative, drop from end.\
     \`(drop 2 \"vwxyz\")` `(drop (- 2) [1 2 3 4 5])` `(drop ['name] { 'name: \"Vlad\", 'active: false})`"

     ,defRNative "assoc" assoc' (funType (tTyObject (mkSchemaVar "o")) [("object",tTyObject (mkSchemaVar "o")),("key",tTyString),("value",a)])
     "Remove entry for KEY from OBJECT. `(assoc { :foo 1 } :bar 2)`"

    ,defRNative "dissoc" dissoc' (funType (tTyObject (mkSchemaVar "o")) [("object",tTyObject (mkSchemaVar "o")),("key",tTyString)])
     "Remove entry for KEY from OBJECT. `(dissoc { :foo 1, :bar 2 } :bar)`"

    ,defRNative "get" get' (funType a [("list",TyList (mkTyVar "l" [])),("idx",tTyInteger)] <>
                            funType a [("list",TyList (mkTyVar "l" [])),("idx",tTyInteger),("defValue",a)] <>
                            funType a [("object",tTyObject (mkSchemaVar "o")),("idx",tTyString)]<>
                            funType a [("object",tTyObject (mkSchemaVar "o")),("idx",tTyString),("defValue",a)])
     "Index LIST at IDX, or get value with key IDX from OBJECT. \
     \`(get [1 2 3] 1)` `(get { :foo 1, :bar 2 } :bar)`"


    ,formatDef, printfDef

    -- ,defRNative "tx-hash" txHash (funType tTyString [])
    --  "Obtain hash of current transaction as a string. `(tx-hash)`"
    
    ,defRNative "type" typeof'' (funType tTyString [("x",a)])
     "Returns type of X as string. `(type \"hello\")`"
    ,setTopLevelOnly $ defRNative "list-modules" listModules
     (funType (TyList tTyString) []) "List modules available for loading."

    ,cljVersionDef

    ,setTopLevelOnly $ defRNative "enforce-seal-version" enforceVersion
     (funType tTyBool [("min-version",tTyString)] <>
      funType tTyBool [("min-version",tTyString),("max-version",tTyString)])
    "Enforce runtime seal version as greater than or equal MIN-VERSION, and less than or equal MAX-VERSION. \
    \Version values are matched numerically from the left, such that '2', '2.2', and '2.2.3' would all allow '2.2.3'. \
    \`(enforce-seal-version \"2.3\")`"

    ,defRNative "contains?" contains
    (funType tTyBool [("list",TyList a),("value",a)] <>
     funType tTyBool [("object",tTyObject (mkSchemaVar "o")),("key",a)] <>
     funType tTyBool [("string",tTyString),("value",tTyString)])
    "Test that LIST or STRING contains VALUE, or that OBJECT has KEY entry. \
    \`(contains? [1 2 3] 2)` `(contains? { :name \"Ted\", :age 72 } :name)` `(contains? \"foobar\" \"foo\")`"

    ,defNative "constantly" constantly
     (funType a [("value",a),("ignore1",b)] <>
      funType a [("value",a),("ignore1",b),("ignore2",c)] <>
      funType a [("value",a),("ignore1",b),("ignore2",c),("ignore3",d)])
     "Lazily ignore arguments IGNORE* and return VALUE. `(filter (constantly true) [1 2 3])`"
    ,defRNative "identity" identity (funType a [("value",a)])
     "Return provided value. `(map (identity) [1 2 3])`"

     ,defRNative "str-to-int" strToInt
     (funType tTyInteger [("str-val", tTyString)] <>
      funType tTyInteger [("base", tTyInteger), ("str-val", tTyString)])
     "Compute the integer value of STR-VAL in base 10, or in BASE if specified. STR-VAL must be <= 128 \
     \chars in length and BASE must be between 2 and 16. `(str-to-int 16 \"123456\")` `(str-to-int \"abcdef123456\")`"

     ,defRNative "str-to-decimal" strToDecimal
     (funType tTyDecimal [("str-val", tTyString)])
     "to decimal"
    ])
    where b = mkTyVar "b" []
          c = mkTyVar "c" []
          d = mkTyVar "d" []
          -- rowTy = TySchema TyObject row
          obj = tTyObject (mkSchemaVar "o")
          listStringA = mkTyVar "a" [TyList (mkTyVar "l" []),TyPrim TyString]
          takeDrop = funType listStringA [("count",tTyInteger),("list",listStringA)] <>
                     funType obj [("keys",TyList tTyString),("object",obj)]
          lam x y = TyFun $ funType' y [("x",x)]
          lam2 x y z = TyFun $ funType' z [("x",x),("y",y)]

a :: Type n
a = mkTyVar "a" []

map' :: HasEval env => NativeFun env
map' i [app@TApp {},l] = reduce l >>= \l' -> case l' of
           TList ls _ _ -> (\b -> TList b TyAny def) <$> forM ls (apply' app . pure)
           t -> evalError' i $ "map: expecting list: " ++ abbrev t
map' i as = argsError' i as

list :: RNativeFun env
list i as = return $ TList as TyAny (_faInfo i) -- TODO, could set type here

makeArray :: HasEval env => RNativeFun env
makeArray i [value,TLitInteger len] = case typeof value of
  Right ty -> return $ toTList ty def $ replicate (fromIntegral len) value
  Left ty -> evalError' i $ "make-array: invalid value type: " ++ show ty
makeArray i as = argsError i as

reverse' :: HasEval env => RNativeFun env
reverse' _ [l@TList{}] = return $ over tList reverse l
reverse' i as = argsError i as

empty' :: HasEval env => RNativeFun env
empty' _i [TList ls _ _] = return $ toTerm $ toLiteral $ length ls <= 0
empty' _i [TObject ps _ _] = return $ toTerm $ toLiteral $ length ps <= 0
empty' _i [TLitString s] = return $ toTerm $ toLiteral $ (length $ toString s) <= 0
empty' i as = argsError i as


reduce' :: HasEval env => NativeFun env
reduce' i [app@TApp {},initv,l] = reduce l >>= \case
           TList ls _ _ -> reduce initv >>= \initv' ->
                         foldM f initv' ls
           t -> evalError' i $ "fold: expecting list: " ++ abbrev t
  where
    f !r !a' = apply' app [r,a']
reduce' i as = argsError' i as


filter' :: HasCallStack => HasEval env => NativeFun env
filter' i [app@TApp {},l] = reduce l >>= \l' -> case l' of
           TList ls lt _ -> ((\b -> TList b lt def) . concat) <$>
                         forM ls (\a' -> do
                           t <- apply' app [a']
                           case t of
                             (TLiteral (LBool True) _) -> return [a']
                             _ -> return []) -- hmm, too permissive here, select is stricter
           t -> evalError' i $ "filter: expecting list: " ++ abbrev t
filter' i as = argsError' i as

count' :: HasEval env => RNativeFun env
count' _ [TList ls _ _] = return $ toTerm $ toLiteral (length ls)
count' _ [TLitString s] = return $ toTerm $ toLiteral (T.length s)
count' _ [TObject ps _ _] = return $ toTerm $ toLiteral (length ps)
count' i as = argsError i as

take' :: HasEval env => RNativeFun env
take' _ [TLitInteger c,TList l t _] = return $ TList (tord take c l) t def
take' _ [TLitInteger c,TLitString l] = return $ toTerm $ toLiteral $ toText $ tord take c (toString l)
take' _ [l@TList {},TObject {..}] =
  return $ toTObject _tObjectType def $ (`filter` _tObject) $ \(k,_) -> searchTermList k (_tList l)

take' i as = argsError i as

drop' :: HasEval env => RNativeFun env
drop' _ [TLitInteger c,TList l t _] = return $ TList (tord drop c l) t def
drop' _ [TLitInteger c,TLitString l] = return $ toTerm $ toLiteral $ toText $ tord drop c (toString l)
drop' _ [l@TList {},TObject {..}] =
  return $ toTObject _tObjectType def $ (`filter` _tObject) $ \(k,_) -> not $ searchTermList k (_tList l)
drop' i as = argsError i as

tord :: (Int -> [a] -> [a]) -> Integer -> [a] -> [a]
tord f c l | c >= 0 = f (fromIntegral c) l
           | otherwise = reverse $ f (fromIntegral (negate c)) (reverse l)

get' :: HasEval env => RNativeFun env
get' _ [TList ls _ _, li@(TLitInteger idx)] =
  case ls `atMay` fromIntegral idx of
    Just t -> return t
    Nothing ->
      evalError (_tInfo li) $
      "get: bad index " ++ show idx ++ ", length " ++ show (length ls)
get' _ [TList ls _ _, (TLitInteger idx), defValue] =
  case ls `atMay` fromIntegral idx of
    Just t -> return t
    Nothing -> return defValue
get' _ [TObject ls _ _, idx] = lookupObj idx ls
get' _ [TObject ls _ _, idx, defValue] =
  case lookup (unsetInfo idx) (map (first unsetInfo) ls) of
    Just v -> return v
    Nothing -> return defValue
get' i as = argsError i as


lookupObj :: HasEval env => (Eq n, Show n) => Term n -> [(Term n, Term n)] -> RIO env (Term n)
lookupObj idx ls = case lookup (unsetInfo idx) (map (first unsetInfo) ls) of
  Just v -> return v
  Nothing -> evalError (_tInfo idx) $ "get: key not found: " ++ show idx


updateObj :: (Eq n) => [(Term n, Term n)]-> [(Term n, Term n)] -> [(Term n, Term n)]
updateObj _ [] = []
updateObj [] ps = ps
updateObj [p] ps = case elemIndex ((unsetInfo . fst) p) (map (unsetInfo . fst) ps) of
    Just n -> take n ps ++ [p] ++ drop (n + 1) ps
    Nothing -> ps ++ [p]
updateObj (p:px) ps = updateObj px $ updateObj [p] ps

filterObj :: (Eq n) => [Term n] -> [(Term n, Term n)] -> [(Term n, Term n)]
filterObj _ [] = []
filterObj [] ps = ps
filterObj [key] ps = filter (\(k, _) -> unsetInfo key /= unsetInfo k) ps
filterObj (k:ks) ps = filterObj ks $ filterObj [k] ps

updateList :: (Eq n, Show n) => [(Term n, Term n)] -> [Term n] -> Maybe [Term n]
updateList [] ls = Just ls
updateList [(TLitInteger idx, e)] ls =
  let n = fromIntegral idx
   in if length ls >= n
        then Just $ take n ls ++ [e] ++ drop (n + 1) ls
        else Nothing
updateList (p:ps) ls = do
  ls' <- updateList [p] ls
  updateList ps ls'



-- dissoc :: RNativeFun e
-- dissoc _ [TObject ps t _, key] = return $ TObject (filterObj [key] ps) t def
-- dissoc _ [TObject ps t _, key1, key2] =
--   return $ TObject (filterObj [key1, key2] ps) t def
-- dissoc _ [TObject ps t _, key1, key2, key3] =
--   return $ TObject (filterObj [key1, key2, key3] ps) t def
-- dissoc _ [TObject ps t _, key1, key2, key3, key4] =
--   return $ TObject (filterObj [key1, key2, key3, key4] ps) t def
-- dissoc _ [TObject ps t _, key1, key2, key3, key4, key5] =
--   return $ TObject (filterObj [key1, key2, key3, key4, key5] ps) t def
-- dissoc i as = argsError i as

dissoc' :: HasEval env => RNativeFun env
-- dissoc' _ [l@TList {}] = return l
-- dissoc' i as@[TList ls t _, TLitInteger idx] =
--   let n = fromIntegral idx
--    in if length ls >= n
--         then return $ TList (take n ls ++ drop (n + 1) ls) t def
--         else argsError i as
-- dissoc' i (l@TList {}:x:xs) = do
--   ls <- dissoc' i [l, x]
--   dissoc' i (ls : xs)
dissoc' _ [(TObject ps t _)] = return $ TObject ps t def
dissoc' _ ((TObject ps t _):ks) = return $ TObject (filterObj ks ps) t def
dissoc' i as = argsError i as




-- assoc :: RNativeFun 
-- assoc _ [TObject ps t _, key, value] =
--   return $ TObject (updateObj [(key, value)] ps) t def
-- assoc _ [TObject ps t _, key1, value1, key2, value2] =
--   return $ TObject (updateObj [(key1, value1), (key2, value2)] ps) t def
-- assoc _ [TObject ps t _, key1, value1, key2, value2, key3, value3] =
--   return $ TObject (updateObj [(key1, value1), (key2, value2), (key3, value3)] ps) t def
-- assoc _ [TObject ps t _, key1, value1, key2, value2, key3, value3, key4, value4] =
--   return $ TObject (updateObj [(key1, value1), (key2, value2), (key3, value3), (key4, value4)] ps) t def
-- assoc _ [TObject ps t _, key1, value1, key2, value2, key3, value3, key4, value4, key5, value5] =
--   return $ TObject (updateObj [(key1, value1), (key2, value2), (key3, value3), (key4, value4), (key5, value5)] ps) t def
-- assoc i as = argsError i as

-- 支持可变参数
assoc' :: HasEval env => RNativeFun env
assoc' _ [l@TList {}] = return l
assoc' i as@(TList ls t _:ivs) =
  case updateList (buildKVPairs ivs) ls of
    Just ls' -> return $ TList ls' t def
    Nothing -> argsError i as
assoc' _ [o@TObject {}] = return o
assoc' _ (TObject ps t _:kvs) =
  return $ TObject (updateObj (buildKVPairs kvs) ps) t def
assoc' i as = argsError i as




buildKVPairs :: (Eq n) => [Term n] -> [(Term n, Term n)]
buildKVPairs [] = []
buildKVPairs [_] = []
buildKVPairs [k, v] = [(k, v)]
buildKVPairs (k:v:kvs) = buildKVPairs [k, v] ++ buildKVPairs kvs

-- comp :: HasEval env => NativeFun env
-- comp i as@[appA@TApp {},appB@TApp {},v] = do
--   v' <- reduce v
--   b' <- apply' appB [v']
--   apply' appA [b']
-- comp i as = argsError' i as

-- 支持可变参数
comp' :: HasEval env => NativeFun env
comp' i as@[] = argsError' i as
comp' i as =
    case reverse as of
        [v] -> reduce v
        (v:funs) -> do
            v' <- reduce v
            applyComp funs v'
        _ -> argsError' i as

applyComp :: HasEval env => [Term Ref] -> Term Name -> RIO env (Term Name)
applyComp [] _ = throwString "applyComp failure"
applyComp [x] v = apply' x [v]
applyComp (x:xs) v = do
  v' <- apply' x [v]
  applyComp xs v'


typeof'' :: HasEval env => RNativeFun env
typeof'' _ [t] = return $ tStr $ typeof' t
typeof'' i as = argsError i as

listModules :: HasEval env => RNativeFun env
listModules _ _ = do
  mods <- view rsModules <$> getRefStore
  return $ toTermList tTyString $ map (toLiteral . toText) $ M.keys mods

unsetInfo :: Term a -> Term a
unsetInfo a' = set tInfo def a'
{-# INLINE unsetInfo #-}


sort' :: HasEval env => RNativeFun env
sort' _ [TList{..}] = case nub (map typeof _tList) of
  [ty] -> case ty of
    Right rty@(TyPrim _) -> do
        sl <- forM _tList $ \e -> case firstOf tLiteral e of
          Nothing -> evalError _tInfo $ "Unexpected type error, expected literal: " ++ show e
          Just lit -> return (lit,e)
        return $ TList (map snd $ sortBy (compare `on` fst) sl) rty def
    _ -> badTy (show ty)
  ts -> evalError _tInfo $ "sort: non-uniform list: " ++ show ts
  where badTy s = evalError _tInfo $ "sort: bad list type: " ++ s
sort' _ [fields@TList{},l@TList{}]
  | null (_tList fields) = evalError (_tInfo fields) "Empty fields list"
  | otherwise = do
      sortPairs <- forM (_tList l) $ \el -> case firstOf tObject el of
        Nothing -> evalError (_tInfo l) $ "Non-object found: " ++ show el
        Just o -> fmap ((,el) . reverse) $ (\f -> foldM f [] (_tList fields)) $ \lits fld -> do
          v <- lookupObj fld o
          case firstOf tLiteral v of
            Nothing -> evalError (_tInfo l) $ "Non-literal found at field " ++ show fld ++ ": " ++ show el
            Just lit -> return (lit:lits)
      return $ TList (map snd $ sortBy (compare `on` fst) sortPairs) (_tListType l) def

sort' i as = argsError i as


enforceVersion :: HasEval env => RNativeFun env
enforceVersion i as = case as of
  [TLitString minVersion] -> doMin minVersion >> return (toTerm $ toLiteral True)
  [TLitString minVersion,TLitString maxVersion] ->
    doMin minVersion >> doMax maxVersion >> return (toTerm $ toLiteral True)
  _ -> argsError i as
  where
    doMin = doMatch "minimum" (>) (<)
    doMax = doMatch "maximum" (<) (>)
    doMatch msg failCmp succCmp fullV =
      foldM_ matchPart False $ zip (T.splitOn "." cljVersion) (T.splitOn "." fullV)
      where
        parseNum orgV s = case AP.parseOnly (AP.many1 AP.digit) s of
          Left _ -> evalError' i $ "Invalid version component: " ++ show (orgV,s)
          Right v -> return v
        matchPart True _ = return True
        matchPart _ (pv,mv)  = do
          pv' <- parseNum cljVersion pv
          mv' <- parseNum fullV mv
          when (mv' `failCmp` pv') $ evalError' i $
            "Invalid seal version " ++ show cljVersion ++ ", " ++ msg ++ " allowed: " ++ show fullV
          return (mv' `succCmp` pv')


contains :: HasEval env => RNativeFun env
contains _i [TList {..}, val] = return $ toTerm $ toLiteral $ searchTermList val _tList
contains _i [TObject {..}, k] = return $ toTerm $ toLiteral $ foldl search False _tObject
  where
    search True _ = True
    search _ (t, _) = t `termEq` k
contains _i [TLitString t, TLitString s] = return $ toTerm $ toLiteral $ T.isInfixOf s t
contains i as = argsError i as


searchTermList :: (Foldable t, Eq n) => Term n -> t (Term n) -> Bool
searchTermList val = Foldable.foldl search False
  where search True _ = True
        search _ t = t `termEq` val


constantly :: HasEval env => NativeFun env
constantly _ (v:_) = reduce v
constantly i as = argsError' i as

identity :: HasEval env => RNativeFun env
identity _ [a'] = return a'
identity i as = argsError i as

strToInt :: HasEval env => RNativeFun env
strToInt i as =
  case as of
    [TLitString s] -> go 10 s
    [TLitInteger base, TLitString s] -> go base s
    _ -> argsError i as
  where
    go base' txt =
      if T.all isHexDigit txt
      then
        if T.length txt <= 128
        then case baseStrToInt base' txt of
          Left _ -> argsError i as
          Right n -> return (toTerm $ toLiteral n)
        else evalError' i $ "Invalid input: unsupported string length: " ++ (toString txt)
      else evalError' i $ "Invalid input: supplied string is not hex: " ++ (toString txt)

strToDecimal :: HasEval env => RNativeFun env
strToDecimal i as =
  case as of
    [TLitString s] -> return $ toTermLiteral $ Prelude.read @Decimal $ toString s
    _ -> argsError i as

-- txHash :: RNativeFun 
-- txHash _ [] = (tStr . txHash1) <$> view eeHash
-- txHash i as = argsError i as

-- txHash1 :: Hash -> Text
-- txHash1 (Hash h) = toText $ BSC.unpack h

-- msgValue :: RNativeFun 
-- msgValue _ [] = (tStr . asString) <$> view eeHash
-- msgValue i as = argsError i as

-- | Change of base for Text-based representations of integrals. Only bases
-- 2 through 16 are supported, for non-empty text of length <= 128
--
-- e.g.
--   -- hexadecimal to decimal
--   baseStrToInt 10 "abcdef123456" = 188900967593046
--
baseStrToInt :: Integer -> Text -> Either Text Integer
baseStrToInt base t =
  if base <= 1 || base > 16
  then Left $ "baseStrToInt - unsupported base: " `T.append` tShow base
  else
    if T.null t
    then Left $ "baseStringToInt - empty text: " `T.append` toText t
    else Right $ T.foldl' go 0 t
  where
    go :: Integer -> Char -> Integer
    go acc w = base * acc + (fromIntegral . digitToInt $ w)
{-# INLINE baseStrToInt #-}

