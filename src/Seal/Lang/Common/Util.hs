{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}

-- |
-- Module      :  Seal.Lang.Common.Util
--
-- Utility types and functions.
--
module Seal.Lang.Common.Util where

import Data.ByteString (ByteString)
import qualified Data.ByteString.Base16 as B16
import Data.Text (Text,pack)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Seal.Prelude


toB16Text :: ByteString -> Text
toB16Text s = decodeUtf8 $ B16.encode s



data RenderColor = RColor | RPlain

renderString :: Pretty a => (Doc -> SimpleDoc) -> RenderColor -> a -> String
renderString renderf colors p = displayS (renderf ((case colors of RColor -> id; RPlain -> plain) (pretty p))) ""

renderCompactString :: Pretty a => a -> String
renderCompactString = renderString renderCompact RPlain

renderPrettyString :: Pretty a => RenderColor -> a -> String
renderPrettyString = renderString (renderPretty 0.4 100)


-- | Prelude-friendly replacement for <$>
infixr 5 <$$>
(<$$>) :: Doc -> Doc -> Doc
(<$$>) = (PP.<$>)

-- | Pretty show.
pshow :: Show a => a -> Doc
pshow = text . show

tShow :: Show a => a -> Text
tShow = pack . show


maybeDelim :: Show a => String -> Maybe a -> String
maybeDelim d = maybe "" ((d ++) . show)
