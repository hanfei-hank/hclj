{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

-- |
-- Module      :  Seal.Lang.Clj.Types.Exp
--
-- Exp, the output of the clj parser, and Literal.
--

module Seal.Lang.Clj.Types.Exp
 (
   Literal(..), ToLiteral(..),
   _LString,_LInteger,_LDecimal,_LBool,_LTime,_LKeyword,
   simpleISO8601,formatLTime,
   litToPrim,
   LiteralExp(..),AtomExp(..),ListExp(..),SeparatorExp(..),
   Exp(..),_ELiteral,_EAtom,_EList,_ESeparator,
   ListDelimiter(..),listDelims,enlist,
   Separator(..),
   Meta(..),
   Compile, Cursor,
   Module(..),
   ) where


import Seal.Prelude
import Data.Text (Text,pack,unpack)
import Data.String (unwords)
import Data.Thyme
import System.Locale
import Data.Decimal

import Seal.Lang.Common.Type
import Seal.Lang.Clj.Types.Type

import qualified Seal.Lang.Common.Compiler as C

data Literal =
    LString { _lString :: !Text } |
    LInteger { _lInteger :: !Integer } |
    LDecimal { _lDecimal :: !Decimal } |
    LBool { _lBool :: !Bool } |
    LTime { _lTime :: !UTCTime } |
    LKeyword { _lKeyword :: !Text }
          deriving (Eq,Generic,Ord)


instance NFData Literal

makePrisms ''Literal

class ToLiteral a where
  toLiteral :: a -> Literal

instance ToLiteral Bool where toLiteral = LBool
instance ToLiteral Integer where toLiteral = LInteger
instance ToLiteral Int where toLiteral = LInteger . fromIntegral
instance ToLiteral Decimal where toLiteral = LDecimal
instance ToLiteral Double where toLiteral = LDecimal . fromRational . toRational
instance ToLiteral Text where toLiteral = LString
instance ToLiteral String where toLiteral s = case s of 
                                          (':':xs) ->  LKeyword $ pack xs 
                                          _        ->  LString $ pack s
instance ToLiteral UTCTime where toLiteral = LTime

-- | ISO8601 Thyme format
simpleISO8601 :: String
simpleISO8601 = "%Y-%m-%dT%H:%M:%SZ"

formatLTime :: UTCTime -> Text
formatLTime = pack . formatTime defaultTimeLocale simpleISO8601
{-# INLINE formatLTime #-}


instance Show Literal where
    show (LString s) = show s
    show (LInteger i) = show i
    show (LDecimal r) = show r
    show (LBool b) = map toLower $ show b
    show (LTime t) = show $ formatLTime t
    show (LKeyword k) = ":" ++ unpack k


litToPrim :: Literal -> PrimType
litToPrim LString {} = TyString
litToPrim LInteger {} = TyInteger
litToPrim LDecimal {} = TyDecimal
litToPrim LBool {} = TyBool
litToPrim LTime {} = TyTime
litToPrim LKeyword {} = TyKeyword

data ListDelimiter = Parens|Brackets|Braces deriving (Eq,Show,Ord,Generic,Bounded,Enum)
instance NFData ListDelimiter

listDelims :: ListDelimiter -> (Text,Text)
listDelims Parens = ("(",")")
listDelims Brackets = ("[","]")
listDelims Braces = ("{","}")

enlist :: ListDelimiter -> ((Text,Text) -> a) -> a
enlist d f = f (listDelims d)

data Separator = Colon|SCaret deriving (Eq,Ord,Generic,Bounded,Enum)
instance NFData Separator
instance Show Separator where
  show Colon = ":"
  show SCaret = "^"


data LiteralExp i = LiteralExp
  { _litLiteral :: !Literal
  , _litInfo :: !i
  } deriving (Eq,Ord,Generic,Functor,Foldable,Traversable)
instance Show (LiteralExp i) where show LiteralExp{..} = show _litLiteral
instance HasInfo (LiteralExp Info) where
  getInfo = _litInfo
instance NFData i => NFData (LiteralExp i)

data AtomExp i = AtomExp
  { _atomAtom :: !Text
  , _atomQualifiers :: ![Text]
  , _atomInfo :: i
  } deriving (Eq,Ord,Generic,Functor,Foldable,Traversable)
instance Show (AtomExp i) where
  show AtomExp{..} = intercalate "/" (map unpack $ _atomQualifiers ++ [_atomAtom])
instance HasInfo (AtomExp Info) where
  getInfo = _atomInfo
instance NFData i => NFData (AtomExp i)

data ListExp i = ListExp
  { _listList :: ![Exp i]
  , _listDelimiter :: !ListDelimiter
  , _listInfo :: !i
  } deriving (Eq,Ord,Generic,Functor,Foldable,Traversable)
instance Show (ListExp i) where
  show ListExp{..} =
    enlist _listDelimiter $ \(o,c) ->
      unpack o ++ unwords (map show _listList) ++ unpack c
instance HasInfo (ListExp Info) where
  getInfo = _listInfo
instance NFData i => NFData (ListExp i)

data SeparatorExp i = SeparatorExp
  { _sepSeparator :: !Separator
  , _sepInfo :: !i
  } deriving (Eq,Ord,Generic,Functor,Foldable,Traversable)
instance Show (SeparatorExp i) where show SeparatorExp{..} = show _sepSeparator
instance HasInfo (SeparatorExp Info) where
  getInfo = _sepInfo
instance NFData i => NFData (SeparatorExp i)


-- | clj syntax expressions
data Exp i =
  ELiteral (LiteralExp i) |
  EAtom (AtomExp i) |
  EList (ListExp i) |
  ESeparator (SeparatorExp i)
  deriving (Eq,Ord,Generic,Functor,Foldable,Traversable)

instance NFData i => NFData (Exp i)
instance HasInfo (Exp Info) where
  getInfo e = case e of
    ELiteral i -> getInfo i
    EAtom a -> getInfo a
    EList l -> getInfo l
    ESeparator s -> getInfo s

makePrisms ''Exp

instance Show (Exp i) where
  show e = case e of
    ELiteral i -> show i
    EAtom a -> show a
    EList l -> show l
    ESeparator s -> show s


data Meta = Meta
  { _mDocs  :: !(Maybe Text) -- ^ docs
  , _mModel :: ![Exp Info]   -- ^ model
  } deriving (Eq, Show, Generic)
instance Default Meta where def = Meta def def

type Compile a = C.ExpParse Exp CompileState a

type Cursor = C.Cursor Exp

-- TODO: We need a more expressive, safer ADT for this.
data Module
  = Module
  { _mName :: !ModuleName
  , _mMeta :: !Meta
  , _mCode :: !Code
  } deriving Eq

instance Show Module where
  show m = case m of
    Module{..} -> "(Contract " ++ toString _mName ++ " '" ++ ")"