{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      :  Seal.Lang.Clj.Native.Internal
--
-- Internal functions for built-ins.
--

module Seal.Lang.Clj.Native.Internal
  (NativeFun, RNativeFun, NativeDef, NativeModule
  ,success
  -- ,parseMsgKey
  ,bindReduce
  ,defNative,defRNative
  ,setTopLevelOnly
  ,foldDefs
  ,funType,funType'
  ,getModule
  ,tTyInteger,tTyDecimal,tTyTime,tTyBool,tTyString,tTyObject
  ) where

import Seal.Prelude
import Seal.Lang.Clj.Eval
import Control.Arrow
import Bound
import qualified Data.HashMap.Strict as HM

import Seal.Lang.Clj.Types.Runtime

-- | Native function with un-reduced arguments that computes gas. Must fire call stack.
type NativeFun env = FunApp -> [Term Ref] -> RIO env (Term Name)

-- | Native function with reduced arguments, final gas pre-compute, call stack fired.
type RNativeFun env = FunApp -> [Term Name] -> RIO env (Term Name)

type NativeDef env = (NativeDefName,Bool,NativeFun env, FunTypes (Term Name), Text)
type NativeModule env = (ModuleName,[NativeDef env])
success :: Functor m => Text -> m a -> m (Term Name)
success = fmap . const . tStr



bindReduce :: HasEval env => [(Arg (Term Ref),Term Ref)] -> Scope Int Term Ref -> Info -> (Text -> Maybe (Term Ref)) -> RIO env (Term Name)
bindReduce ps bd bi lkpFun = do
  !(vs :: [(Arg (Term Ref),Term Ref)]) <- forM ps $ mapM $ \var -> do
          var' <- reduce var
          case var' of
            (TLitString s) -> case lkpFun s of
                                Nothing -> evalError bi $ "Bad column in binding: " ++ toString s
                                Just v -> return v
            (TLitKeyword s) -> case lkpFun s of
                                Nothing -> evalError bi $ "Bad column in binding: " ++ toString s
                                Just v -> return v                    
            t -> evalError bi $ "Invalid column identifier in binding: " ++ show t
  let bd'' = instantiate (resolveArg bi (map snd vs)) bd
  -- NB stack frame here just documents scope, but does not incur gas
  call (StackFrame (toText $ "(bind: " ++ show (map (second abbrev) vs) ++ ")") bi Nothing) $!
    reduceBody bd''

setTopLevelOnly :: NativeDef env -> NativeDef env
setTopLevelOnly = set _2 True

-- | Specify a 'NativeFun'
defNative :: NativeDefName -> NativeFun env -> FunTypes (Term Name) -> Text -> NativeDef env
defNative n fun ftype docs =
  -- (n, TNative n (NativeDFun n (unsafeCoerce fun)) ftype docs False def)
  (n, False, fun, ftype, docs)

-- | Specify a 'RNativeFun'
defRNative :: HasEval env => NativeDefName -> RNativeFun env -> FunTypes (Term Name) -> Text -> NativeDef env
defRNative name fun = defNative name (reduced fun)
    where reduced f fi as = mapM reduce as >>= f fi

foldDefs :: Monad m => [m a] -> m [a]
foldDefs = foldM (\r d -> d >>= \d' -> return (d':r)) []

funType :: Type n -> [(Text,Type n)] -> FunTypes n
funType t as = funTypes $ funType' t as


funType' :: Type n -> [(Text,Type n)] -> FunType n
funType' t as = FunType (map (\(s,ty) -> Arg s ty def) as) t


getModule :: HasEval env => Info -> ModuleName -> RIO env Module
getModule i n = do
  lm <- HM.lookup n . view rsLoadedModules <$> getRefState
  case lm of
    Just m -> return m
    Nothing -> do
      rm <- HM.lookup n . view rsModules <$> getRefStore 
      case rm of
        Just ModuleData{..} -> return _mdModule
        Nothing -> evalError i $ "Unable to resolve contract " ++ show n

tTyInteger :: Type n; tTyInteger = TyPrim TyInteger
tTyDecimal :: Type n; tTyDecimal = TyPrim TyDecimal
tTyTime :: Type n; tTyTime = TyPrim TyTime
tTyBool :: Type n; tTyBool = TyPrim TyBool
tTyString :: Type n; tTyString = TyPrim TyString
tTyObject :: Type n -> Type n; tTyObject = TySchema TyObject
