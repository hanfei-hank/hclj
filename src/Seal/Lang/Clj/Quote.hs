{-# LANGUAGE TemplateHaskell    #-}

module Seal.Lang.Clj.Quote (exps, terms, expsF, termsF) where

import Universum hiding (Type)
import Seal.Prelude.TH as TH

import Seal.Lang.Clj.Parse
import Seal.Lang.Clj.Compile (parseCompile)

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
