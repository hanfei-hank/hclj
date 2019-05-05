{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE Rank2Types #-}
-- |
-- Module      :  Seal.Lang.Common.Parser
--

module Seal.Lang.Common.Parser where

import Text.Trifecta as TF
import Text.Trifecta.Delta (bytes)
import Control.Applicative
import Data.List
import Control.Monad
import Prelude
import Data.Decimal
import qualified Data.Attoparsec.Text as AP
import Data.Char (digitToInt)
import Data.Text (Text)
import Seal.Lang.Common.Type

newtype LangParser p a = LangParser { unLangParser :: p a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, Parsing, CharParsing)

{-# INLINE withParsed #-}
withParsed :: (DeltaParsing m) => (m Parsed -> m a) -> m a
withParsed p = do
  delt <- position
  p do
      end <- position
      let len = bytes end - bytes delt
      return $ Parsed delt (fromIntegral len)

-- TODO As number parsing is a solved problem, consider something like:
-- http://hackage.haskell.org/package/megaparsec-7.0.0/docs/Text-Megaparsec-Char-Lexer.html#v:float
number :: (Monad m, TokenParsing m, DeltaParsing m) => m (Either Integer Decimal)
number = do
  -- Tricky: note that we use `char :: CharParsing m => Char -> m Char` rather
  -- than `symbolic :: TokenParsing m => Char -> m Char` here. We use the char
  -- parser because we want to disallow whitespace following the negative sign
  -- (token parsers apply `whiteSpace` after every token). With a whitespace we
  -- consider this an expression rather than a literal.
  neg <- maybe id (const negate) <$> optional (char '-')
  num <- some digit
  dec <- optional (dot *> some digit)
  let strToNum = foldl' (\x d -> 10*x + toInteger (digitToInt d))
  case dec of
    Nothing -> return $ Left (neg (strToNum 0 num))
    Just d -> return $ Right $ Decimal
              (fromIntegral (length d))
              (neg (strToNum (strToNum 0 num) d))
{-# INLINE number #-}


-- | "Production" parser: atto, parse multiple exps. 
parseText :: LangParser AP.Parser a -> Text -> Either String a
parseText m = AP.parseOnly (unLangParser m)

parseString :: LangParser TF.Parser a -> String -> Either String a
parseString m src = case TF.parseString (unLangParser m) mempty src of
    TF.Success es -> Right es
    TF.Failure er -> Left $ show er

parseFile :: LangParser TF.Parser a -> FilePath -> IO (Either String a)
parseFile p fp = do
  r <- TF.parseFromFileEx (unLangParser p) fp
  case r of
    TF.Success a -> return $ Right a
    TF.Failure er -> return $ Left $ show er
