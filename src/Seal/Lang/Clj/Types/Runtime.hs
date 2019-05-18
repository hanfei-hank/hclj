{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      :  Seal.Lang.Clj.Types.Runtime
--
-- 'Eval' monad and utilities.
-- Exports Lang and Util, so this is the "default import" for most clj things.
--

module Seal.Lang.Clj.Types.Runtime
 ( 
   evalError,evalError',argsError,argsError', 
   etArgsError, etEvalError, etSyntaxError,
   ModuleData(..), mdModule, mdRefMap,
   RefStore(..),rsNatives,rsModules,installNative,
   updateRefStore,
   StackFrame(..),sfName,sfLoc,sfApp,
   RefState(..),rsLoaded,rsLoadedModules,rsNewModules,
   HasEval(..),
   resolveRef,
   call,
   module Seal.Lang.Common.Util,
   module Seal.Lang.Common.Type,
   module Seal.Lang.Clj.Types.Exp,
   module Seal.Lang.Clj.Types.Term,
   module Seal.Lang.Clj.Types.Type
   ) where

import Seal.Prelude 
import GHC.TypeLits
import Data.Generics.Product.Typed
import qualified Data.HashMap.Strict as HM

import Seal.Lang.Common.Type
import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Clj.Types.Type
import Seal.Lang.Clj.Types.Term
import Seal.Lang.Common.Orphans ()
import Seal.Lang.Common.Util

data StackFrame = StackFrame {
      _sfName :: !Text
    , _sfLoc :: !Info
    , _sfApp :: Maybe (FunApp,[Text])
    }
instance Show StackFrame where
    show (StackFrame n i app) = renderInfo i ++ ": " ++ case app of
      Nothing -> toString n
      Just (_,as) -> "(" ++ toString n ++ concatMap (\a -> " " ++ toString (toText a)) as ++ ")"
makeLenses ''StackFrame


-- | Module ref store
data ModuleData = ModuleData
  { _mdModule :: Module
  , _mdRefMap :: HM.HashMap Text Ref
  } deriving (Eq, Show)
makeLenses ''ModuleData

-- | Storage for loaded modules, interfaces, and natives.
data RefStore = RefStore {
      _rsNatives :: HM.HashMap Name Ref
    , _rsModules :: HM.HashMap ModuleName ModuleData
    } deriving (Eq, Show)
makeLenses ''RefStore

instance Semigroup RefStore where
  (RefStore n1 m1) <> (RefStore n2 m2) = RefStore (n1 <> n2) (m1 <> m2)

instance Monoid RefStore where
  mempty = RefStore mempty mempty

installNative :: Text -> Ref -> RefStore -> RefStore
installNative n r = over rsNatives $ HM.insert (Name n def) r

-- | Dynamic storage for namespace-loaded modules, and new modules compiled in current tx.
data RefState = RefState {
      -- | Namespace-local defs.
      _rsLoaded :: HM.HashMap Name Ref
      -- | Modules that were loaded.
    , _rsLoadedModules :: HM.HashMap ModuleName Module
      -- | Modules that were compiled and loaded in this tx.
    , _rsNewModules :: HM.HashMap ModuleName ModuleData
    } deriving (Eq,Show)
makeLenses ''RefState
instance Default RefState where def = RefState HM.empty HM.empty HM.empty

-- | Update for newly-loaded modules and interfaces.
updateRefStore :: RefState -> RefStore -> RefStore
updateRefStore RefState {..}
  | HM.null _rsNewModules = id
  | otherwise = over rsModules (HM.union _rsNewModules)

class HasEval env where
  getRefStore :: RIO env RefStore
  default getRefStore :: HasType (IORef RefStore) env => RIO env RefStore
  getRefStore = view typed >>= readIORef

  getRefState :: RIO env RefState
  default getRefState :: HasType (IORef RefState) env => RIO env RefState
  getRefState = view typed >>= readIORef

  modifyRefState :: (RefState -> RefState) -> RIO env ()
  default modifyRefState :: HasType (IORef RefState) env => (RefState -> RefState) -> RIO env ()
  modifyRefState f = view typed >>= \ref -> modifyIORef ref f

  getCallStack :: RIO env [StackFrame]
  default getCallStack :: HasType (IORef [StackFrame]) env => RIO env [StackFrame]
  getCallStack = view typed >>= readIORef

  modifyCallStack :: ([StackFrame] -> [StackFrame]) -> RIO env ()
  default modifyCallStack :: HasType (IORef [StackFrame]) env => ([StackFrame] -> [StackFrame]) -> RIO env ()
  modifyCallStack f = view typed >>= \ref -> modifyIORef ref f

  -- report error, with category
  throwEvalErr :: KnownSymbol n => Proxy n -> Info -> Text -> RIO env a
  throwEvalErr _ _ m = throwString $ toString m

  reduceNativeVar :: Text -> RIO env (Term Name)


etEvalError :: Proxy "EvalError"; etEvalError = Proxy
etArgsError :: Proxy "ArgsError"; etArgsError = Proxy
etSyntaxError :: Proxy "SyntaxError"; etSyntaxError = Proxy

-- | Bracket interpreter action pushing and popping frame on call stack.
call :: HasEval env => StackFrame -> RIO env a -> RIO env a
call s act = do
  modifyCallStack (s :)
  r <- act -- TODO opportunity for per-call gas logging here
  modifyCallStack $  \case (_:as) -> as; [] -> []
  return r
{-# INLINE call #-}



throwArgsError :: HasEval env => FunApp -> [Term Name] -> Text -> RIO env a
throwArgsError FunApp {..} args s = throwEvalErr etArgsError _faInfo $ toText $
  toString s ++ ", received [" ++ intercalate "," (map abbrev args) ++ "] for " ++
            showFunTypes _faTypes

evalError ::  HasEval env => Info -> String -> RIO env a
evalError i = throwEvalErr etEvalError i . toText

evalError' :: HasEval env => FunApp -> String -> RIO env a
evalError' = evalError . _faInfo


argsError :: HasEval env => FunApp -> [Term Name] -> RIO env a
argsError i as = throwArgsError i as "Invalid arguments"

argsError' :: HasEval env => FunApp -> [Term Ref] -> RIO env a
argsError' i as = throwArgsError i (map (tStr.toText.abbrev) as) "Invalid arguments"


resolveRef :: HasEval env => Name -> RIO env (Maybe Ref)
resolveRef qn@(QName q n _) = do
  dsm <- preview (rsModules . ix q . mdRefMap . ix n) <$> getRefStore
  case dsm of
    d@Just {} -> return d
    Nothing -> preview (rsLoaded . ix qn) <$> getRefState
resolveRef nn@(Name _ _) = do
  nm <- preview (rsNatives . ix nn) <$> getRefStore
  case nm of
    d@Just {} -> return d
    Nothing -> preview (rsLoaded . ix nn) <$> getRefState

