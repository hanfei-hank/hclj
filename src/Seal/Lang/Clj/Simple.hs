{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Seal.Lang.Clj.Simple where

import Seal.Prelude
import qualified Seal.Prelude.Unsafe as Unsafe
import Seal.TH (merge, (.<))
import qualified Seal.TH as TH
import Seal.Lang.Clj.Types.Runtime
import Seal.Lang.Clj.Compile
import Seal.Lang.Clj.Eval
import Seal.Lang.Clj.Parse
import Seal.Lang.Clj.Native
import Seal.Lang.Clj.Native.Internal
import Seal.Lang.Clj.TH

data SimpleCljEnv = SimpleCljEnv {
    eRefStore :: !RefStore
  , eRefState :: IORef RefState
  , eCallStack :: IORef [StackFrame]
} deriving (Generic)

instance HasEval SimpleCljEnv


type Repl a = RIO SimpleCljEnv a

makeRepl :: [TH.Name] -> TH.DecsQ
makeRepl ns = 
  makeNativeModule "user" ns <>

  [d|

  simpleNatives :: [NativeModule SimpleCljEnv]
  simpleNatives = userModule : natives

  refStore :: RefStore
  refStore = RefStore (foldMap moduleToMap simpleNatives) mempty

  newSimpleCljEnv :: MonadIO m => m SimpleCljEnv
  newSimpleCljEnv = SimpleCljEnv refStore <$> newIORef def <*> newIORef def 

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

  new :: IO (String -> IO ())
  new = do
      env <- newSimpleCljEnv 
      return $ \src -> runRIO env (evalString src)

  |]
