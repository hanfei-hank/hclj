{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-- {-# LANGUAGE TemplateHaskell #-}

module Seal.Lang.Clj.Repl where

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

data ReplEnv = ReplEnv {
    eRefStore :: IORef RefStore
  , eRefState :: IORef RefState
  , eCallStack :: IORef [StackFrame]
  , eNativeVarReducer :: IORef (Text -> RIO ReplEnv (Term Name))
} deriving (Generic)

instance HasEval ReplEnv where
  reduceNativeVar n = do
    f <- asks eNativeVarReducer >>= readIORef
    f n

newReplEnv :: MonadIO m => m ReplEnv
newReplEnv = ReplEnv <$> newIORef refStore <*> newIORef def <*> newIORef def <*> newIORef undefined
  where
    refStore :: RefStore
    refStore = RefStore (foldMap moduleToMap preloadModules) mempty
    preloadModules :: [NativeModule ReplEnv]
    preloadModules = natives

type Repl a = RIO ReplEnv a

loadNativeModule :: NativeModule ReplEnv -> Repl ()
loadNativeModule m = do
    ref <- asks eRefStore 
    modifyIORef' ref (<> RefStore (moduleToMap m) mempty)

defNativeVar :: Text -> Type (Term Name) -> Repl ()
defNativeVar n t = do
    ref <- asks eRefStore
    modifyIORef' ref $ installNative n $ Direct $ TNativeVar (NativeDefName n) t def 

installNativeVarReducer :: (Text -> Repl (Term Name)) -> Repl ()
installNativeVarReducer r = do
    ref <- asks eNativeVarReducer
    writeIORef ref r

eval :: Term Name -> Repl (Term Name)
eval (TModule m@Module{..} bod i) = do
  _defs <- loadModule m bod i
  return $ toTermLiteral @Text "load ok"
  
eval t = do
  tref <- enscope t
  -- putStrLn $ show tref
  reduce tref

evalString :: String -> Repl ()
evalString src = do
  let exps' = do
        exps <- parseString exprsOnly src
        let ei = fmap (mkStringInfo src <$>) exps
        mapLeft show $ compile ei

  case exps' of
    Left err -> putStrLn err
    Right ts -> evalTerms ts

evalFile :: FilePath -> Repl ()
evalFile path = do
  code <- toString <$> readFileUtf8 path
  evalString code
  -- call run method
  -- evalString "(run)"

evalTerms :: [Term Name] -> Repl ()
evalTerms ts =
  catch (do
    result <- forM ts $ \e -> eval e
    print (Unsafe.last result)
    )
    $ \(e :: SomeException) -> print e

new :: Repl () -> IO (String -> IO ())
new init = do
    env <- newReplEnv 
    runRIO env init
    return $ \src -> runRIO env (evalString src)

