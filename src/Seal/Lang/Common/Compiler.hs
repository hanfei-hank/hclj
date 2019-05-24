{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      :  Seal.Lang.Common.Compiler
-- Parser combinator over 'exp'.
--

module Seal.Lang.Common.Compiler
  ( Cursor(..)
  , ParseState(..), psCurrent, psUser
  , MkInfo, mkEmptyInfo, mkStringInfo, mkTextInfo
  , ExpParse
  , pTokenEpsilon
  , nes
  , dbg
  , strErr
  , tokenErr, tokenErr'
  , syntaxError
  , expected, unexpected'
  , commit
  , anyExp
  , context, contextInfo
  , current
  , exp
    ) where

import Control.Applicative hiding (some,many)
import Text.Megaparsec hiding (dbg)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Internal (ParsecT(..))
import Data.Proxy
import Data.Void
import Data.List.NonEmpty (NonEmpty(..),fromList)
import Data.List
import Control.Monad
import Control.Monad.State
import Control.Arrow (second)
import Prelude hiding (exp)
import Control.Lens hiding (prism)
import Data.Default
import qualified Data.Set as S

import Seal.Lang.Common.Type
import Universum ((<>))

-- | exp stream type.
data Cursor exp = Cursor
  { _cContext :: Maybe (Cursor exp, exp Info)
  , _cStream :: [exp Info]
  } 
deriving instance Show (exp Info) => Show (Cursor exp)
instance Default (Cursor exp) where def = Cursor def def

-- | adapted from Text.Megaparsec.Stream
defaultAdvance1
  :: Pos               -- ^ Tab width (unused)
  -> SourcePos         -- ^ Current position
  -> t                 -- ^ Current token
  -> SourcePos         -- ^ Incremented position
defaultAdvance1 _width (SourcePos n l c) _t = SourcePos n l (c <> pos1)
{-# INLINE defaultAdvance1 #-}

-- | Adapt Cursor to MP Stream, patterned after
-- [Char] instance.
instance Ord (exp Info) => Stream (Cursor exp) where
  type Token (Cursor exp) = exp Info
  type Tokens (Cursor exp) = [exp Info]
  tokenToChunk Proxy = pure
  tokensToChunk Proxy = id
  chunkToTokens Proxy = id
  chunkLength Proxy = length
  chunkEmpty Proxy = null
  advance1 Proxy = defaultAdvance1
  advanceN Proxy w = foldl' (defaultAdvance1 w)
  take1_ Cursor{..} = case _cStream of
    [] -> Nothing
    (t:ts) -> Just (t, Cursor _cContext ts)
  takeN_ n s@Cursor{..}
    | n <= 0        = Just ([], s)
    | null _cStream = Nothing
    | otherwise = Just $ second (Cursor _cContext) $ splitAt n _cStream
  takeWhile_ f Cursor{..} = second (Cursor _cContext) $ span f _cStream

-- | Capture last-parsed Exp, plus arbitrary state.
data ParseState exp a = ParseState
  { _psCurrent :: exp Info
  , _psUser :: a
  } 
deriving instance (Show a, Show (exp Info)) => Show (ParseState exp a)
makeLenses ''ParseState


type ExpParse exp s a = StateT (ParseState exp s) (Parsec Void (Cursor exp)) a


dbg :: (Show s, Show a, Ord (exp Info), Show (exp Info), ShowToken (exp Info)) => String -> ExpParse exp s a -> ExpParse exp s a
-- dbg m (StateT f) = StateT $ \s -> MP.dbg m $ f s
dbg m (StateT f) = StateT f

{-# INLINE strErr #-}
strErr :: String -> ErrorItem t
strErr = Label . fromList

{-# INLINE tokenErr #-}
tokenErr :: Ord (exp Info) => String -> exp Info -> ExpParse exp s a
tokenErr s = tokenErr' s . Just

{-# INLINE tokenErr' #-}
tokenErr' :: Ord (exp Info) => String -> Maybe (exp Info) -> ExpParse exp s a
tokenErr' ty i = failure
  (fmap (\e -> Tokens (e:|[])) i)
  (S.singleton (strErr ty))

{-# INLINE context #-}
context :: Ord (exp Info) => ExpParse exp s (Maybe (exp Info))
context = fmap snd . _cContext <$> getInput

{-# INLINE contextInfo #-}
contextInfo :: Ord (exp Info) => HasInfo (exp Info) => ExpParse exp s Info
contextInfo = maybe def getInfo <$> context

{-# INLINE current #-}
current :: Ord (exp Info) => ExpParse exp s (exp Info)
current = use psCurrent

{-# INLINE syntaxError #-}
syntaxError :: Ord (exp Info) => String -> ExpParse exp s a
syntaxError s = current >>= tokenErr s

{-# INLINE expected #-}
expected :: Ord (exp Info) => String -> ExpParse exp s a
expected s = syntaxError $ "Expected: " ++ s

{-# INLINE unexpected' #-}
unexpected' :: Ord (exp Info) => String -> ExpParse exp s a
unexpected' s = syntaxError $ "Unexpected: " ++ s

{-# INLINE nes #-}
nes :: a -> NonEmpty a
nes x = x :| []

-- | Test a token in the stream for epsilon/"trivial" acceptance,
-- allowing for further tests on the result before committing.
-- This is copypasta from Megaparsec's implementation of 'token' as
-- of version 6.5.0, so this might break in future MP versions.
pTokenEpsilon :: forall e s m a. Stream s
  => (Token s -> Either ( Maybe (ErrorItem (Token s))
                        , S.Set (ErrorItem (Token s)) ) a)
  -> Maybe (Token s)
  -> ParsecT e s m a
pTokenEpsilon test mtoken = ParsecT $ \s@(State input (pos:|z) tp w) _ _ eok eerr ->
  case take1_ input of
    Nothing ->
      let us = pure EndOfInput
          ps = maybe S.empty (S.singleton . Tokens . nes) mtoken
      in eerr (TrivialError (pos:|z) us ps) s
    Just (c,cs) ->
      case test c of
        Left (us, ps) ->
          let !apos = positionAt1 (Proxy :: Proxy s) pos c
          in eerr (TrivialError (apos:|z) us ps)
                  (State input (apos:|z) tp w)
        Right x ->
          let !npos = advance1 (Proxy :: Proxy s) w pos c
              newstate = State cs (npos:|z) (tp + 1) w
          in eok x newstate mempty -- this is the only change from 'token'

-- | Call commit continuation with current state.
pCommit :: forall e s m. ParsecT e s m ()
pCommit = ParsecT $ \s cok _ _ _ -> cok () s mempty

-- | Commit any previous recognitions.
commit :: Ord (exp Info) => ExpParse exp s ()
commit = lift pCommit

-- | Recognize any Exp, committing.
{-# INLINE anyExp #-}
anyExp :: Ord (exp Info) => ExpParse exp s (exp Info)
anyExp = token Right Nothing

-- | Recognize a specific Exp sub-type, non-committing.
{-# INLINE exp #-}
exp :: Ord (exp Info) => String -> Prism' (exp Info) a -> ExpParse exp s (a,exp Info)
exp ty prism = do
  let test i = case firstOf prism i of
        Just a -> Right (a,i)
        Nothing -> err i ("Expected: " ++ ty)
      err i s = Left (pure (Tokens (i:|[])),
                      S.singleton (strErr s))
  r <- context >>= (lift . pTokenEpsilon test)
  psCurrent .= snd r
  return r
