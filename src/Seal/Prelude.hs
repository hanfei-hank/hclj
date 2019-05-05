{-# OPTIONS_GHC -fno-warn-orphans #-}

module Seal.Prelude (
  module Universum
, module Universum.Base
, module Universum.Container
, module Universum.Functor
, module Universum.String
, module Control.Lens
, module Data.Char
, module Data.Default
, module Data.Foldable
, module Data.List
, module Data.String
, module Data.Tuple
, module RIO
, module UnliftIO
) where

import Universum.Base hiding (reduce, withFile, Type) 
import Universum.Applicative as Universum
import Universum.Bool as Universum
import Universum.Container (Hashable(..), ToPairs(..), One(..))
import Universum.Debug as Universum
import Universum.DeepSeq as Universum
import Universum.Function as Universum
import Universum.Functor hiding (Bifunctor(..))
import Universum.List as Universum
import Universum.Monad as Universum
import Universum.Monoid as Universum
import Universum.Nub as Universum
import Universum.Print as Universum
import Universum.String (Text, encodeUtf8, decodeUtf8, ToString(..), ToText(..))

import Control.Lens hiding (List, op, parts, uncons)
import Data.Char
import Data.Default 
import Data.Foldable 
import Data.List (intersect, nub)
import Data.String
import Data.Tuple
import RIO (Show(..), RIO(..), runRIO, liftRIO, mapLeft)
import UnliftIO 


instance Semigroup a => Semigroup (RIO env a) where
    (<>) = liftA2 (<>)

instance Monoid a => Monoid (RIO env a) where
    mempty = pure mempty