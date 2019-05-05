{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      :  Seal.Lang.Clj.Native.Ops
--
-- Operators and math built-ins.
--
module Seal.Lang.Clj.Native.Ops
  ( opDefs
  , orDef
  , andDef
  , notDef
  , modDef
  , addDef
  , subDef
  , mulDef
  , divDef
  , powDef
  , logDef
  , sqrtDef
  , lnDef
  , expDef
  , absDef
  , roundDef
  , ceilDef
  , floorDef
  , gtDef
  , ltDef
  , gteDef
  , lteDef
  , eqDef
  , neqDef
  ) where

import           Data.Decimal
import qualified Data.Map.Strict               as M

import           Seal.Lang.Clj.Native.Internal
import           Seal.Lang.Clj.Types.Runtime

import           Seal.Lang.Clj.Eval
import Seal.Prelude hiding (assert)
import qualified Seal.Prelude.Unsafe as Unsafe
import qualified Prelude

modDef :: HasEval env => NativeDef env
modDef =
  defRNative
    "mod"
    mod'
    (binTy tTyInteger tTyInteger tTyInteger)
    "X modulo Y. `(mod 13 8)`"
  where
    -- mod' :: RNativeFun 
    mod' _ [TLitInteger a, TLitInteger b] = return $ toTerm $ a `mod` b
    mod' i as = argsError i as

addDef :: HasEval env => NativeDef env
addDef =
  defRNative
    "+"
    plus
    plusTy
    "Add numbers, concatenate strings/lists, or merge objects. \
     \`(+ 1 2)` `(+ 5.0 0.5)` `(+ \"every\" \"body\")` `(+ [1 2] [3 4])` \
     \`(+ { \"foo\": 100 } { \"foo\": 1, \"bar\": 2 })`"
  where
    -- plus :: RNativeFun 
    plus _ [TLitString a, TLitString b] = return (tStr $ a <> b)
    plus _ [TList a aty _, TList b bty _] =
      return $
      TList
        (a <> b)
        (if aty == bty
           then aty
           else TyAny)
        def
    plus _ [TObject as aty _, TObject bs bty _] =
      let reps (a, b) = (abbrev a, (a, b))
          mapit = M.fromList . map reps
       in return $
          TObject
            (M.elems $ M.union (mapit as) (mapit bs))
            (if aty == bty
               then aty
               else TyAny)
            def
    plus i as@[_, _] = binop' (+) (+) i as
    plus i (x:y:zs) = do
      x' <- plus i [x, y]
      plus i (x' : zs)
    plus i as = argsError i as
    {-# INLINE plus #-}
    plusTy :: FunTypes n
    plusTy = coerceBinNum <> binTy plusA plusA plusA

subDef :: HasEval env => NativeDef env
subDef =
  defRNative
    "-"
    minus
    (coerceBinNum <> unaryNumTys)
    "Negate X, or subtract Y from X. `(- 1.0)` `(- 3 2)`"
  where
    -- minus :: RNativeFun 
    minus _ [TLiteral (LInteger n) _] = return (toTerm (negate n))
    minus _ [TLiteral (LDecimal n) _] = return (toTerm (negate n))
    minus i as@[_, _] = binop' (-) (-) i as
    minus i (x:y:zs) = do
      x' <- minus i [x, y]
      minus i (x' : zs)
    minus i as = argsError i as
    {-# INLINE minus #-}
    unaryNumTys :: FunTypes n
    unaryNumTys = unaryTy numA numA

mulDef :: HasEval env => NativeDef env
mulDef =
  defRNative "*" mul coerceBinNum "Multiply X by Y. `(* 0.5 10.0)` `(* 3 5)`"
  where
    -- mul :: RNativeFun 
    mul i as@[_, _] = binop' (*) (*) i as
    mul i (x:y:zs) = do
      x' <- mul i [x, y]
      mul i (x' : zs)
    mul i as = argsError i as
    {-# INLINE mul #-}

divDef :: HasEval env => NativeDef env
divDef =
  defRNative "/" divide' coerceBinNum "Divide X by Y. `(/ 10.0 2.0)` `(/ 8 3)`"
  where
    -- divide' :: RNativeFun 
    divide' i as@[_, _] =
      binop
        (\a b -> assert (b /= 0) "Division by 0" $ liftOp (/) a b)
        (\a b -> assert (b /= 0) "Division by 0" $ liftOp div a b)
        i
        as
    divide' i (x:y:zs) = do
      x' <- divide' i [x, y]
      divide' i (x' : zs)
    divide' i as = argsError i as
    {-# INLINE divide' #-}

powDef :: HasEval env => NativeDef env
powDef = defRNative "^" pow coerceBinNum "Raise X to Y power. `(^ 2 3)`"
  where
    -- pow :: RNativeFun 
    pow =
      binop
        (\a b -> liftDecF (**) a b)
        (\a b -> assert (b >= 0) "Integral power must be >= 0" $ liftOp (^) a b)

logDef :: HasEval env => NativeDef env
logDef = defRNative "log" log' coerceBinNum "Log of Y base X. `(log 2 256)`"
  where
    -- log' :: RNativeFun 
    log' = binop (\a b -> liftDecF logBase a b) (\a b -> liftIntF logBase a b)

sqrtDef :: HasEval env => NativeDef env
sqrtDef = defRNative "sqrt" (unopd sqrt) unopTy "Square root of X. `(sqrt 25)`"

lnDef :: HasEval env => NativeDef env
lnDef =
  defRNative "ln" (unopd Prelude.log) unopTy "Natural log of X. `(round (ln 60) 6)`"

expDef :: HasEval env => NativeDef env
expDef = defRNative "exp" (unopd exp) unopTy "Exp of X. `(round (exp 3) 6)`"

absDef :: HasEval env => NativeDef env
absDef =
  defRNative
    "abs"
    abs'
    (unaryTy tTyDecimal tTyDecimal <> unaryTy tTyInteger tTyInteger)
    "Absolute value of X. `(abs (- 10 23))`"
  where
    -- abs' :: RNativeFun 
    abs' _ [TLitInteger a] = return $ toTerm $ abs a
    abs' _ [TLiteral (LDecimal n) _] = return $ toTerm $ abs n
    abs' i as = argsError i as

roundDef :: HasEval env => NativeDef env
roundDef = defTrunc "round" "Performs Banker's rounding" round

ceilDef :: HasEval env => NativeDef env
ceilDef = defTrunc "ceiling" "Rounds up" ceiling

floorDef :: HasEval env => NativeDef env
floorDef = defTrunc "floor" "Rounds down" floor

gtDef :: HasEval env => NativeDef env
gtDef = defCmp ">" (cmp (== GT))

ltDef :: HasEval env => NativeDef env
ltDef = defCmp "<" (cmp (== LT))

gteDef :: HasEval env => NativeDef env
gteDef = defCmp ">=" (cmp (`elem` [GT, EQ]))

lteDef :: HasEval env => NativeDef env
lteDef = defCmp "<=" (cmp (`elem` [LT, EQ]))

eqDef :: HasEval env => NativeDef env
eqDef =
  defRNative
    "="
    (eq id)
    eqTy
    "True if X equals Y. `(= [1 2 3] [1 2 3])` `(= 'foo \"foo\")` `(= { 1: 2 } { 1: 2})`"

neqDef :: HasEval env => NativeDef env
neqDef =
  defRNative
    "not="
    (eq not)
    eqTy
    "True if X does not equal Y. `(not= \"hello\" \"goodbye\")`"

eqTy :: FunTypes n
eqTy = binTy tTyBool eqA eqA

eqA :: Type n
eqA =
  mkTyVar
    "a"
    [ tTyInteger
    , tTyString
    , tTyTime
    , tTyDecimal
    , tTyBool
    , TyList (mkTyVar "l" [])
    , TySchema TyObject (mkSchemaVar "o")
    ]

orDef :: HasEval env => NativeDef env
orDef = defLogic "or" (||) True

andDef :: HasEval env => NativeDef env
andDef = defLogic "and" (&&) False

notDef :: HasEval env => NativeDef env
notDef =
    defNative
        "not"
        not'
        (unaryTy tTyBool tTyBool)
        "Boolean logic. `(not (> 1 2))`"
  where
    -- r = mkTyVar "r" []
    -- not' :: NativeFun 
    -- not' [TLiteral (LBool a) _] = return $ toTerm $ not a
    not' i as =
        case as of
            [app@TApp {}, v'] ->
                reduce v' >>= \v ->
                    apply' app [v] >>= \r ->
                        case r of
                            TLitBool b -> return $ toTerm $ not b
                            _ -> delegateError "not" app r
            [v'] ->
                reduce v' >>= \case
                    TLitBool b -> return $ toTerm $ not b
                    _ -> argsError' i as
            _ -> argsError' i as


opDefs :: HasEval env => NativeModule env
opDefs =
  ( "Operators"
  , [ 
    -- liftLogic "or?" (||) "or" True
    -- , liftLogic "and?" (&&) "and" False
    -- , 
    -- defNative
    --     "not?"
    --     liftNot
    --     (funType tTyBool [("app", logicLam r), ("value", r)])
    --     ("Apply logical 'not' to the results of applying VALUE to APP. " <>
    --      "`(not? (> 20) 15)`")
    -- , 
    orDef
    , andDef
    , notDef
    , gtDef
    , ltDef
    , gteDef
    , lteDef
    , eqDef
    , neqDef
    , addDef
    , subDef
    , mulDef
    , divDef
    , powDef
    , logDef
    , modDef
    , sqrtDef
    , lnDef
    , expDef
    , absDef
    , roundDef
    , ceilDef
    , floorDef
    ])
  -- where
  --   r = mkTyVar "r" []

unopTy :: FunTypes n
unopTy = unaryTy numA numA

numA :: Type n
numA = numV "a"

numV :: TypeVarName -> Type n
numV a = mkTyVar a [tTyInteger, tTyDecimal]

coerceBinNum :: FunTypes n
coerceBinNum = binTy numA numA numA <> binTy tTyDecimal numA (numV "b")

plusA :: Type n
plusA =
  mkTyVar
    "a"
    [tTyString, TyList (mkTyVar "l" []), TySchema TyObject (mkSchemaVar "o")]

defTrunc :: HasEval env => NativeDefName -> Text -> (Decimal -> Integer) -> NativeDef env
defTrunc n desc op =
  defRNative
    n
    fun
    (funType tTyDecimal [("x", tTyDecimal), ("prec", tTyInteger)] <>
     unaryTy tTyInteger tTyDecimal)
    (desc <> " value of decimal X as integer, or to PREC precision as decimal. " <>
     "`(" <>
     toText n <>
     " 3.5)` `(" <>
     toText n <>
     " 100.15234 2)`")
  where
    -- fun :: RNativeFun 
    fun _ [TLiteral (LDecimal d) _] = return $ toTerm $ op d
    fun i [TLiteral (LDecimal d) _, TLitInteger p]
      | p >= 0 =
        let p10 = (10 ^ p :: Decimal)
         in return $ toTerm (fromIntegral (op (d * p10)) / p10)
      | otherwise = evalError' i "Negative precision not allowed"
    fun i as = argsError i as

defLogic :: HasEval env => NativeDefName -> (Bool -> Bool -> Bool) -> Bool -> NativeDef env
defLogic n bop shortC =
  defNative n fun (binTy tTyBool tTyBool tTyBool)
    $  "Boolean logic with short-circuit. `("
    <> toText n
    <> " true false)`"
 where
  -- fun :: NativeFun 
  fun i as = catch (logicFun' as) (\(_ :: SomeException) -> (reduce (Unsafe.last as) >>= liftFun' (Unsafe.init as))) >>= \case 
      Just a -> return a
      _      -> argsError' i as
  -- logicFun' :: [Term Ref] -> Eval (Maybe (Term Name))
  logicFun' [a] = reduce a >>= \case
    TLitBool x -> return $ Just $ toTerm x
    _          -> return Nothing
  logicFun' (a : xs) = logicFun' [a] >>= \case
    Just (TLitBool x)
      | x == shortC -> return $ Just $ toTerm x
      | otherwise -> logicFun' xs >>= \case
        Just (TLitBool y) -> return $ Just $ toTerm $ x `bop` y
        _                 -> return Nothing
    _ -> return Nothing
  logicFun' _ = return Nothing
  -- liftFun' :: [Term Ref] -> Term Name -> Eval (Maybe (Term Name))
  liftFun' [x] v = apply' x [v] >>= \v' -> case v' of
    TLitBool ab -> return $ Just $ toTerm ab
    _           -> delegateError (show n) x v'
  liftFun' (x : xs) v = liftFun' [x] v >>= \case
    Just (TLitBool ab)
      | ab == shortC -> return $ Just $ toTerm shortC
      | otherwise -> liftFun' xs v >>= \case
          Just (TLitBool bb) -> return $ Just $ toTerm $ bop ab bb
          _                  -> return Nothing
    _ -> return Nothing
  liftFun' _ _ = return Nothing


-- logicLam :: Type v -> Type v
-- logicLam argTy = TyFun $ funType' tTyBool [("x", argTy)]

delegateError :: HasEval env => String -> Term Ref -> Term Name -> RIO env a
delegateError desc app r =
  evalError (_tInfo app) $
  desc ++ ": Non-boolean result from delegate: " ++ show r


eq :: HasEval env => (Bool -> Bool) -> RNativeFun env
eq f _ [a, b] = return $ toTerm $ f (a `termEq` b)
eq _ i as = argsError i as

{-# INLINE eq #-}
unaryTy :: Type n -> Type n -> FunTypes n
unaryTy rt ta = funType rt [("x", ta)]

binTy :: Type n -> Type n -> Type n -> FunTypes n
binTy rt ta tb = funType rt [("x", ta), ("y", tb)]

defCmp :: HasEval env => NativeDefName -> RNativeFun env -> NativeDef env
defCmp o f =
  let o' = toText o
      ex a' b = " `(" <> o' <> " " <> a' <> " " <> b <> ")`"
      a = mkTyVar "a" [tTyInteger, tTyDecimal, tTyString, tTyTime]
   in defRNative o f (binTy tTyBool a a) $
      "True if X " <> o' <> " Y." <> ex "1" "3" <> ex "5.24" "2.52" <>
      ex "\"abc\"" "\"def\""

-- | Monomorphic compare.
cmp :: HasEval env => (Ordering -> Bool) -> RNativeFun env
cmp cmpFun fi as@[TLiteral a _, TLiteral b _] = do
  c <-
    case (a, b) of
      (LInteger i, LInteger j) -> return $ i `compare` j
      (LDecimal i, LDecimal j) -> return $ i `compare` j
      (LString i, LString j) -> return $ i `compare` j
      (LTime i, LTime j) -> return $ i `compare` j
      _ -> argsError fi as
  return $ toTerm (cmpFun c)
cmp _ fi as = argsError fi as

{-# INLINE cmp #-}
liftOp :: (a -> a -> a) -> a -> a -> Either b a
liftOp f a b = Right (f a b)

binop' :: HasEval env
  => (Decimal -> Decimal -> Decimal)
  -> (Integer -> Integer -> Integer)
  -> RNativeFun env
binop' dop iop = binop (liftOp dop) (liftOp iop)

-- | Perform binary math operator with coercion to Decimal as necessary.
binop :: HasEval env 
  => (Decimal -> Decimal -> Either String Decimal)
  -> (Integer -> Integer -> Either String Integer)
  -> RNativeFun env
binop dop iop fi as@[TLiteral a _, TLiteral b _] = do
  let hdl (Right v) = return v
      hdl (Left err) = evalError' fi $ err <> ": " <> show (a, b)
  case (a, b) of
    (LInteger i, LInteger j) -> hdl $ fmap toTerm (i `iop` j)
    (LDecimal i, LDecimal j) -> hdl $ fmap toTerm (i `dop` j)
    (LInteger i, LDecimal j) -> hdl $ fmap toTerm (fromIntegral i `dop` j)
    (LDecimal i, LInteger j) -> hdl $ fmap toTerm (i `dop` fromIntegral j)
    _ -> argsError fi as
binop _ _ fi as = argsError fi as

{-# INLINE binop #-}
assert :: Bool -> String -> Either String a -> Either String a
assert test msg act
  | test = act
  | otherwise = Left msg

dec2F :: Decimal -> Double
dec2F = fromRational . toRational

f2Dec :: Double -> Decimal
f2Dec = fromRational . toRational

int2F :: Integer -> Double
int2F = fromIntegral

f2Int :: Double -> Integer
f2Int = round

liftDecF ::
     (Double -> Double -> Double) -> Decimal -> Decimal -> Either String Decimal
liftDecF f a b = Right $ f2Dec (dec2F a `f` dec2F b)

liftIntF ::
     (Double -> Double -> Double) -> Integer -> Integer -> Either String Integer
liftIntF f a b = Right $ f2Int (int2F a `f` int2F b)

unopd :: HasEval env => (Double -> Double) -> RNativeFun env
unopd op _ [TLitInteger i] = return $ toTerm $ f2Dec $ op $ int2F i
unopd op _ [TLiteral (LDecimal n) _] = return $ toTerm $ f2Dec $ op $ dec2F n
unopd _ i as = argsError i as
