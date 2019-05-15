{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
--
-- Parser to 'Exp's.
--

module Seal.Lang.Clj.Parse
    (
      exprs, exprsOnly
    , parseString
    ,numberLiteral
    ,LangParser(unLangParser)
    )

where

import Seal.Prelude
import Text.Trifecta hiding (parseString)
import qualified Text.Trifecta as TF
import qualified Data.Text as T
import qualified Data.HashSet as HS

import Text.Parser.Token.Highlight
import Text.Parser.Token.Style

import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Common.Type
import Seal.Lang.Common.Parser

deriving instance DeltaParsing p => DeltaParsing (LangParser p)

instance TokenParsing p => TokenParsing (LangParser p) where
  someSpace   = LangParser $ buildSomeSpaceParser someSpaceOrComma $ CommentStyle "" "" ";" False
  nesting     = LangParser . nesting . unLangParser
  semi        = token $ char ';' <?> ";"
  highlight h = LangParser . highlight h . unLangParser
  token p     = p <* whiteSpace

style :: CharParsing m => IdentifierStyle m
style = IdentifierStyle "atom"
        firstC
        (letter <|> digit <|> symbols)
        (HS.fromList ["true","false","/"])
        Symbol
        ReservedIdentifier
  where
    firstC = letter <|> oneOf "*+!-_?<>="
    symbols = oneOf "+-_<>=?*!./"

isSpaceOrComma :: Char -> Bool
isSpaceOrComma ',' = True
isSpaceOrComma c = isSpace c

someSpaceOrComma :: CharParsing m => m ()
someSpaceOrComma = skipSome (satisfy isSpaceOrComma)

-- | Main parser for clj expressions.
expr :: (Monad m, TokenParsing m, DeltaParsing m) => LangParser m (Exp Parsed)
expr = withParsed \inf -> do
  let separator t s = symbol t >> (ESeparator . SeparatorExp s <$> inf)
  msum
    [ TF.try (ELiteral <$> (LiteralExp <$> token numberLiteral <*> inf)) <?> "number"
    , ELiteral <$> (LiteralExp . LString <$> stringLiteral <*> inf) <?> "string"
    , ELiteral <$> (LiteralExp . LString <$> (symbolic '\'' >> ident style) <*> inf) <?> "symbol"
    , ELiteral <$> (LiteralExp . LKeyword <$> (char ':' >> ident style) <*> inf) <?> "keyword"
    , ELiteral <$> (LiteralExp <$> boolLiteral <*> inf) <?> "bool"
    ,(qualifiedAtom3 >>= \(a,qs) ->EAtom . AtomExp a qs <$> inf) <?> "atom"
    , EList <$> (ListExp <$> parens (many expr) <*> pure Parens <*> inf) <?> "(list)"
    , EList <$> (ListExp <$> braces (many expr) <*> pure Braces <*> inf) <?> "[list]"
    , EList <$> (ListExp <$> brackets (many expr) <*> pure Brackets <*> inf) <?> "{list}"
    , reserveText style "/" >> (EAtom . AtomExp "/" [] <$> inf) <?> "/"
    , separator ":" Colon
    , separator "^" SCaret 
    ]
{-# INLINE expr #-}

numberLiteral :: (Monad m, DeltaParsing m) => LangParser m Literal
numberLiteral = either LInteger LDecimal <$> number

qualifiedAtom3 ::(Monad p, TokenParsing p) => p (Text,[Text])
qualifiedAtom3 = ident style >>= \case
  [] -> error "qualifiedAtom3"
  q -> return (T.pack q,[])

boolLiteral :: (Monad m, DeltaParsing m) => LangParser m Literal
boolLiteral = msum
  [ LBool True  <$ symbol "true"
  , LBool False <$ symbol "false"
  ]
{-# INLINE boolLiteral #-}


-- | Parse one or more clj expressions.
exprs :: (TokenParsing m, DeltaParsing m) => LangParser m [Exp Parsed]
exprs = some expr

-- | Parse one or more clj expressions and EOF.
-- Unnecessary with Atto's 'parseOnly'.
exprsOnly :: (Monad m, TokenParsing m, DeltaParsing m) => LangParser m [Exp Parsed]
exprsOnly = whiteSpace *> exprs <* TF.eof
