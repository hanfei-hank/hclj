{-# LANGUAGE TemplateHaskell    #-}

module Seal.Lang.Clj.TH (
  exps, terms, expsF, termsF, 
  makeNativeDef, makeNativeModule, nativePat, nativeCall,
  ) where

import Universum hiding (Type)
import qualified Universum.Unsafe as Unsafe
import Seal.Prelude.TH as TH

import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Clj.Types.Runtime (argsError)
import Seal.Lang.Clj.Types.Term
import Seal.Lang.Clj.Parse
import Seal.Lang.Clj.Compile (parseCompile)
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
  let toDefE n = varE $ rename' n (++ "Def")
  let body = [| ($(stringE name), $(listE $ map toDefE ns)) |]
      mn = mkName $ name ++ "Module"
  defs <- makeNativeDef ns
  sequence [funD mn [clause [] (normalB body) (map return defs)]]

makeNativeDef :: [TH.Name] -> DecsQ
makeNativeDef = mapM $ \f -> do
  VarI _ t _ <- reify f
  nativeCall f (pure t)

nativePat :: PatQ -> Type -> PatQ
nativePat v (ConT n)
  | n == ''Text = [p| TLiteral (LString $v) _ |]
  | n == ''Int    = [p| TLiteral (LInteger $v) _ |]
nativePat _ t = fail "unsupport native param type"

nativeCall :: TH.Name -> TypeQ -> DecQ
nativeCall f t = do
  pts <- uncurryType t
  (ps, es) <- genPE "a" $ length pts - 1
  let nCall = rename' f (++ "'")
      c = clause [wildP , listP (zipWith nativePat ps $ Unsafe.init pts)] (normalB [| toTerm <$> $(appExp $ varE f : es) |]) []
      caller = funD nCall [c, argsErrCall]
      d = [|defRNative $(nameToExp id f) $(varE nCall) $(nativeFunType pts) "desc"|]
  funD (rename' f (++ "Def")) [clause [] (normalB d) [caller]]

argsErrCall :: ClauseQ
argsErrCall = do
  (ps, es) <- genPE "a" 2
  clause ps (normalB $ appExp $ varE 'argsError : es) []

nativeType :: Type -> ExpQ
nativeType (ConT n)
  | n == ''Text = [|tTyString|]
  | n == ''Int    = [| tTyInteger|]

nativeReturnType :: Type -> ExpQ
nativeReturnType t = nativeType $ Unsafe.last $ unappConT' t 

nativeFunType :: [Type] -> ExpQ
nativeFunType ts = do
  let pt = map (\t -> [|("p", $(nativeType t))|]) $ Unsafe.init ts
      rt = Unsafe.last ts
  appExp [[| funType |], nativeReturnType rt, listE pt]
