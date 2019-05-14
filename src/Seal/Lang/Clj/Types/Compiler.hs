{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
--
-- Parser combinator over 'Exp'.
--

module Seal.Lang.Clj.Types.Compiler
   where

import Control.Applicative hiding (some,many)
import Text.Megaparsec hiding (dbg)
import Data.List.NonEmpty (NonEmpty(..),toList)
import Data.List
import Control.Monad
import Control.Monad.State
import Prelude hiding (exp)
import Control.Lens hiding (prism)
import Data.Default
import Data.Text (Text,pack,unpack)
import qualified Data.Set as S

import Seal.Lang.Clj.Types.Exp
import Seal.Lang.Common.Type
import Universum ((<>))
import Seal.Lang.Common.Compiler 
import qualified Seal.Lang.Common.Compiler as C

-- | Run a compile. TODO squint harder at MP errors for better output.
{-# INLINE runCompile #-}
runCompile :: Compile a -> C.ParseState Exp CompileState -> [Exp Info] -> Either (Info, Text) a
runCompile act cs a =
  case runParser (runStateT act cs) "" (C.Cursor Nothing a) of
    (Right (r,_)) -> Right r
    (Left (TrivialError _ (Just err) expect)) -> case err of
      EndOfInput -> case S.toList expect of
        (Tokens (x :| _):_) -> doErr (getInfo x) "unexpected end of input"
        (Label s:_) -> doErr def (toList s)
        er -> doErr def (show er)
      Label ne -> doErr def (toList ne)
      Tokens (x :| _) -> doErr (getInfo x) $ "expected " <> showExpect expect
    (Left e) -> doErr def (show e)
    where doErr i s = Left (i, pack s)
          showExpect e = case labelText $ S.toList e of
            [] -> show (S.toList e)
            ss -> intercalate "," ss
          labelText [] = []
          labelText (Label s:r) = toList s:labelText r
          labelText (EndOfInput:r) = "end of expression or input":labelText r
          labelText (_:r) = labelText r


-- | Enter a list context, setting the token stream to its contents
{-# INLINE enter #-}
enter :: (ListExp Info,Exp Info) -> Compile (ListExp Info)
enter (l@ListExp{..},e) = do
  par <- getInput
  setInput $ C.Cursor (Just (par,e)) _listList
  return l

-- | Exit a list context, resuming a previous parent context.
{-# INLINE exit #-}
exit :: Compile ()
exit = do
  child <- getInput
  case C._cContext child of
    Just (p,e) -> setInput p >> (C.psCurrent .= e)
    Nothing -> failure (Just EndOfInput) def

-- | Recognize an atom, non-committing.
{-# INLINE atom #-}
atom :: Compile (AtomExp Info)
atom = fst <$> exp "atom" _EAtom

-- | Recognized a literal, non-committing.
{-# INLINE lit #-}
lit :: Compile (LiteralExp Info)
lit = fst <$> exp "literal" _ELiteral

-- | Recognize a list, non-committing.
{-# INLINE list #-}
list :: Compile (ListExp Info,Exp Info)
list = exp "list" _EList

-- | Recognize a separator, committing.
{-# INLINE sep #-}
sep :: Separator -> Compile ()
sep s = exp "sep" _ESeparator >>= \(SeparatorExp{..},_) ->
  if _sepSeparator == s then commit else expected (show s)

-- | Recognize a specific literal, non-committing.
{-# INLINE lit' #-}
lit' :: String -> Prism' Literal a -> Compile a
lit' ty prism = lit >>= \LiteralExp{..} -> case firstOf prism _litLiteral of
  Just l -> return l
  Nothing -> expected ty

-- | Recognize a String literal, non-committing.
{-# INLINE str #-}
str :: Compile Text
str = lit' "string" _LString

-- | Recognize a String literal, non-committing.
{-# INLINE keyword #-}
keyword :: Compile Text
keyword = lit' "keyword" _LKeyword

-- | Recognize a list with specified delimiter, committing.
{-# INLINE list' #-}
list' :: ListDelimiter -> Compile (ListExp Info,Exp Info)
list' d = list >>= \l@(ListExp{..},_) ->
  if _listDelimiter == d then commit >> return l
  else expected $ enlist d (\(s,e)->unpack(s<>"list"<>e))

-- | Recongize a list with specified delimiter and act on contents, committing.
{-# INLINE withList #-}
withList :: ListDelimiter -> (ListExp Info -> Compile a) -> Compile a
withList d act = try $ list' d >>= enter >>= act >>= \a -> exit >> return a

-- | 'withList' without providing ListExp arg to action, committing.
{-# INLINE withList' #-}
withList' :: ListDelimiter -> Compile a -> Compile a
withList' d = withList d . const

-- | Recognize an unqualified "bare" atom, non-committing.
{-# INLINE bareAtom #-}
bareAtom :: Compile (AtomExp Info)
bareAtom = atom >>= \a@AtomExp{..} -> case _atomQualifiers of
  (_:_) -> expected "unqualified atom"
  [] -> return a

-- | Recognize a bare atom with expected text, committing.
{-# INLINE symbol #-}
symbol :: Text -> Compile ()
symbol s = bareAtom >>= \AtomExp{..} ->
  if _atomAtom == s then commit else expected $ unpack s

instance ShowToken (Exp i) where
  showTokens = show
