{-# LANGUAGE ScopedTypeVariables #-}

module Seal.Lang.Clj.Simple where

import Seal.Prelude
import qualified Seal.Prelude.Unsafe as Unsafe
import Seal.Lang.Clj.Types.Runtime
import Seal.Lang.Clj.Compile
import Seal.Lang.Clj.Eval
import Seal.Lang.Clj.Native.Internal
import Seal.Lang.Clj.Native

data SimpleCljEnv = SimpleCljEnv {
    eRefStore :: !RefStore
  , eRefState :: IORef RefState
  , eCallStack :: IORef [StackFrame]
}

instance HasEval SimpleCljEnv where
  getRefStore = asks eRefStore

  getRefState = asks eRefState >>= readIORef
  modifyRefState f = asks eRefState >>= \ref -> modifyIORef ref f

  getCallStack = asks eCallStack >>= readIORef
  modifyCallStack f = asks eCallStack >>= \ref -> modifyIORef ref f

  throwEvalErr _ _ m = throwString $ toString m

type Repl a = RIO SimpleCljEnv a

simpleNatives :: [NativeModule SimpleCljEnv]
simpleNatives = natives

refStore :: RefStore
refStore = RefStore (foldMap moduleToMap simpleNatives) mempty

newSimpleCljEnv :: MonadIO m => m SimpleCljEnv
newSimpleCljEnv = SimpleCljEnv refStore <$> newIORef def <*> newIORef def


eval :: Term Name -> Repl (Term Name)
eval t = enscope t >>= reduce

evalString :: String -> Repl ()
evalString src = do
  let exps = parseCompile src

  case exps of
    Left err -> putStrLn err
    Right ts -> evalTerms ts


evalTerms :: [Term Name] -> Repl ()
evalTerms ts =
  catch (do
    result <- forM ts $ \e -> eval e
    print (Unsafe.last result)
    )
    $ \(e :: SomeException) -> print e

data Clj m = Clj {
    evalClj :: String -> m ()
}

new :: IO (Clj IO)
new = do
    env <- newSimpleCljEnv
    return $ Clj $ \src -> runRIO env (evalString src)