{-# LANGUAGE TemplateHaskell #-}

module Seal.Prelude.TH (
    _reify
  , module Language.Haskell.TH
  , module Language.Haskell.TH.Syntax
  , module Language.Haskell.TH.Quote
) where

import Prelude 
import Language.Haskell.TH 
import Language.Haskell.TH.Syntax 
import Language.Haskell.TH.Quote

-- for ghci debug
_reify :: Name -> Q Exp
_reify n = stringE . show =<< reify n