{-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE TemplateHaskell #-}

module Seal.Lang.Clj.Simple where

import Seal.Prelude
import qualified Seal.Prelude.Unsafe as Unsafe
import Seal.TH (merge, (.<))
import qualified Seal.TH as TH
import Seal.Lang.Clj.Types.Runtime
import Seal.Lang.Clj.Eval
import Seal.Lang.Clj.Parse
import Seal.Lang.Clj.Native
import Seal.Lang.Clj.Native.Internal
import Seal.Lang.Clj.TH

data SimpleCljEnv = SimpleCljEnv {
    eRefStore :: IORef RefStore
  , eRefState :: IORef RefState
  , eCallStack :: IORef [StackFrame]
} deriving (Generic)

instance HasEval SimpleCljEnv

newSimpleCljEnv :: MonadIO m => m SimpleCljEnv
newSimpleCljEnv = SimpleCljEnv <$> newIORef refStore <*> newIORef def <*> newIORef def 
  where
    refStore :: RefStore
    refStore = RefStore (foldMap moduleToMap preloadModules) mempty
    preloadModules :: [NativeModule SimpleCljEnv]
    preloadModules = natives

type Repl a = RIO SimpleCljEnv a

loadNativeModule :: NativeModule SimpleCljEnv -> Repl ()
loadNativeModule m = do
    ref <- asks eRefStore 
    modifyIORef ref (<> RefStore (moduleToMap m) mempty)


  -- makeNativeModule "user" ns <>


eval :: Term Name -> Repl (Term Name)
eval t = enscope t >>= reduce

evalString :: String -> Repl ()
evalString src = do
  let exps' = do
        exps <- parseString exprsOnly src
        let ei = fmap (mkStringInfo src <$>) exps
        mapLeft show $ compile ei

  case exps' of
    Left err -> putStrLn err
    Right ts -> evalTerms ts


evalTerms :: [Term Name] -> Repl ()
evalTerms ts =
  catch (do
    result <- forM ts $ \e -> eval e
    print (Unsafe.last result)
    )
    $ \(e :: SomeException) -> print e

new :: NativeModule SimpleCljEnv -> IO (String -> IO ())
new userModule = do
    env <- newSimpleCljEnv 
    runRIO env $ loadNativeModule userModule
    return $ \src -> runRIO env (evalString src)

