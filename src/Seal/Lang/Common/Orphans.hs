{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      :  Seal.Lang.Common.Orphans
--
-- Various orphans.
--
module Seal.Lang.Common.Orphans where

import Text.Trifecta.Combinators (DeltaParsing(..))
import Text.Trifecta.Delta
import qualified Data.Attoparsec.Text as AP
import qualified Data.Attoparsec.Internal.Types as APT
import Data.Text (Text)
import qualified Data.Text as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Default
import Control.DeepSeq
import Prelude

instance NFData Delta


-- | Atto DeltaParsing instance provides 'position' only (with no support for
-- hidden chars like Trifecta).
instance DeltaParsing AP.Parser where
    line = return mempty
    position = attoPos >>= \(APT.Pos p) -> let p' = fromIntegral p in return $ Columns p' p'  -- p p
    slicedWith f a = (`f` mempty) <$> a
    rend = return mempty
    restOfLine = return mempty

-- | retrieve pos from Attoparsec.
attoPos :: APT.Parser n APT.Pos
attoPos = APT.Parser $ \t pos more _lose win -> win t pos more pos

instance PP.Pretty Text where pretty = PP.text . T.unpack
instance Default Text where def = ""