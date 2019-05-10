{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Seal.Lang.Clj.Simple where

import Seal.Prelude
import qualified Seal.Prelude.Unsafe as Unsafe
import qualified Seal.Prelude.TH as TH
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
          mapLeft show $ compile $ fmap cmdExpTransfer ei

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

  data Clj m = Clj {
      evalClj :: String -> m ()
  }

  new :: IO (Clj IO)
  new = do
      env <- newSimpleCljEnv 
      return $ Clj $ \src -> runRIO env (evalString src)

  -- 将命令行参数转换成clj表达式
  cmdExpTransfer :: Exp i -> Exp i
  cmdExpTransfer = go
    where
      go' (EAtom (AtomExp n qs i)) = ELiteral (LiteralExp (LString n) i)
      go' e = go e
      go (EList (ListExp (e:es) Parens i2)) = 
          EList (ListExp (e: fmap go' es) Parens i2)
      go e = e
      
  |]
