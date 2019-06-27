{-# LANGUAGE TemplateHaskell    #-}

module Seal.Lang.Clj.TH (
  exps, terms, expsF, termsF, 
  makeNativeModule, nativePat, nativeCall,
  defRNativeQ,
  defRNative, funType,
  ) where

import Universum hiding (Type)
import Data.Decimal
import qualified Universum.Unsafe as Unsafe
import Seal.TH as TH
import Text.Casing
import Data.Aeson (Value)

import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Clj.Types.Runtime (argsError)
import Seal.Lang.Clj.Types.Term
import Seal.Lang.Clj.Parse
import Seal.Lang.Clj.Eval (parseCompile)
import Seal.Lang.Clj.Native.Internal

exps :: QuasiQuoter
exps = QuasiQuoter {
    quoteExp  = compile
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where 
    compile s = case parseString exprsOnly s of
        Left e -> fail $ "compile error : " ++ e
        Right _ -> do 
          let src = mkName "src"
          [|  let $(varP src) = $(TH.lift s) 
              in case parseString exprsOnly $(varE src) of
                  Left _ -> error "impossable"
                  Right es -> fmap (mkInfo $(varE src) <$>) es
            |]


terms :: QuasiQuoter
terms = QuasiQuoter {
    quoteExp  = compile
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where 
    compile s = case parseCompile s of
        Left e -> fail $ "compile error : " ++ e
        Right _ -> do 
          let src = mkName "src"
          [|  let $(varP src) = $(TH.lift s) 
              in case parseCompile ($(varE src) :: String) of
                  Left _ -> error "impossable"
                  Right es -> es
            |]

expsF, termsF :: QuasiQuoter
expsF = quoteFile exps
termsF = quoteFile exps

notHandled :: String -> String -> Q a
notHandled things _ = fail $
      things ++ " are not handled by the contract quasiquoter."

-- 简化native函数的声明
makeNativeModule :: String -> [TH.Name] -> DecsQ
makeNativeModule name ns = do
  let body = [| ($(stringE name), $(listE $ map nativeCall ns)) |]
      mn = mkName $ name ++ "Module"
  sequence [funD mn [clause [] (normalB body) []]]

nativePat :: PatQ -> Type -> PatQ
nativePat v (ConT n)
  | n == ''Text = [p| TLiteral (LString $v) _ |]
  | n == ''Integer    = [p| TLiteral (LInteger $v) _ |]
  | n == ''Decimal = [p| TLiteral (LDecimal $v) _ |]
nativePat _ t = fail $ "unsupport native param type" <> show t

nativeCall :: TH.Name -> ExpQ
nativeCall f = do
  VarI _ t _ <- reify f
  defRNativeQ (kebab $ nameBase f) (pure t) (varE f)

defRNativeQ :: String -> TypeQ -> ExpQ -> ExpQ
defRNativeQ n tq exp = do
  pts <- uncurryType tq
  (ps, es) <- genPE "a" $ length pts - 1
  let nCall = mkName "_native"
      c = clause [wildP , listP (zipWith nativePat ps $ Unsafe.init pts)] (normalB [| toTermLiteral <$> $(appExp $ exp : es) |]) []
      caller = funD nCall [c, argsErrCall]
  letE [caller] [|defRNative $(TH.lift n) $(varE nCall) $(nativeFunType pts) "desc"|]

  where
    argsErrCall :: ClauseQ
    argsErrCall = do
      (ps, es) <- genPE "a" 2
      clause ps (normalB $ appExp $ varE 'argsError : es) []

nativeType :: Type -> ExpQ
nativeType (ConT n)
  | n == ''Bool = [|tTyBool|]
  | n == ''Text = [|tTyString|]
  | n == ''Integer    = [| tTyInteger|]
  | n == ''Decimal = [| tTyDecimal |]
  | otherwise = fail $ "unsupported native type :" <> show n

nativeReturnType :: Type -> ExpQ
nativeReturnType t = nativeType $ Unsafe.last $ unappConT' t 

nativeFunType :: [Type] -> ExpQ
nativeFunType ts = do
  let pt = map (\t -> [|("p", $(nativeType t))|]) $ Unsafe.init ts
      rt = Unsafe.last ts
  appExp [[| funType |], nativeReturnType rt, listE pt]


