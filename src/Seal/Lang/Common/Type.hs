{-# LANGUAGE DerivingVia #-}

-- |
-- Module      :  Seal.Lang.Common.Type
--
-- Code-related metadata.
--

module Seal.Lang.Common.Type
 ( ModuleName(..), Name(..), TypeName(..), DefVisibility(..),
   CompileState(..), csFresh, csModule,
   Parsed(..),
   Code(..),
   Info(..),
   renderInfo,
   renderParsed,
   HasInfo(..),
   MkInfo, mkEmptyInfo, mkStringInfo, mkTextInfo,
   ConstVal(..),
   NativeDefName(..),
   ) where


import qualified Text.Trifecta.Delta as TF
import Text.Trifecta.Delta hiding (Columns)
import Seal.Prelude
import Data.Functor.Classes
import Data.Text (Text,unpack)
import qualified Data.Text as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.PrettyPrint.ANSI.Leijen hiding ((<>),(<$>))

import Seal.Lang.Common.Orphans ()
import Seal.Lang.Common.Util

data DefVisibility = PUBLIC | PRIVATE
    deriving (Eq, Show, Generic)

newtype ModuleName = ModuleName Text
    deriving (Eq,Ord,IsString,ToString,ToText,Hashable,Pretty)
    deriving Show via Text

data CompileState = CompileState
  { _csFresh :: Int
  , _csModule :: Maybe ModuleName
  } 
makeLenses ''CompileState

instance Show CompileState where
  show (CompileState n m) = "CompileState " <> show n <> " " <> show m 

-- | A named reference from source.
data Name =
    QName { _nQual :: ModuleName, _nName :: Text, _nInfo :: Info } |
    Name { _nName :: Text, _nInfo :: Info }
        deriving (Generic)
instance Show Name where
    show (QName q n _) = toString q ++ "/" ++ unpack n
    show (Name n _) = unpack n

instance Hashable Name where
  hashWithSalt s (Name t _) = s `hashWithSalt` (0::Int) `hashWithSalt` t
  hashWithSalt s (QName q n _) = s `hashWithSalt` (1::Int) `hashWithSalt` q `hashWithSalt` n
instance Eq Name where
  (QName a b _) == (QName c d _) = (a,b) == (c,d)
  (Name a _) == (Name b _) = a == b
  _ == _ = False
instance Ord Name where
  (QName a b _) `compare` (QName c d _) = (a,b) `compare` (c,d)
  (Name a _) `compare` (Name b _) = a `compare` b
  Name {} `compare` QName {} = LT
  QName {} `compare` Name {} = GT
  

newtype TypeName = TypeName Text
  deriving (Eq,Ord,IsString,ToString,ToText,Pretty,Generic,NFData)
instance Show TypeName where show (TypeName s) = show s

-- | Code location, length from parsing.
data Parsed = Parsed {
  _pDelta :: Delta,
  _pLength :: Int
  } deriving (Eq,Show,Ord,Generic)

instance NFData Parsed
instance Default Parsed where def = Parsed mempty 0
instance HasBytes Parsed where bytes = bytes . _pDelta
instance Pretty Parsed where pretty = pretty . _pDelta


newtype Code = Code { _unCode :: Text }
  deriving (Eq,Ord,IsString,Semigroup,Monoid,Generic,NFData,ToText)
instance Show Code where show = unpack . _unCode
instance Pretty Code where
  pretty (Code c) | T.compareLength c maxLen == GT =
                      text $ unpack (T.take maxLen c <> "...")
                  | otherwise = text $ unpack c
    where maxLen = 30

-- | For parsed items, original code and parse info;
-- for runtime items, nothing
newtype Info = Info { _iInfo :: Maybe (Code,Parsed) } deriving (Generic)

instance NFData Info
-- show instance uses Trifecta renderings
instance Show Info where
    show (Info Nothing) = ""
    show (Info (Just (r,_d))) = renderCompactString r
instance Eq Info where
    Info Nothing == Info Nothing = True
    Info (Just (_,d)) == Info (Just (_,e)) = d == e
    _ == _ = False
instance Ord Info where
  Info Nothing <= Info Nothing = True
  Info (Just (_,d)) <= Info (Just (_,e)) = d <= e
  Info Nothing <= _ = True
  _ <= Info Nothing = False

instance Default Info where def = Info Nothing


-- renderer for line number output.
renderInfo :: Info -> String
renderInfo (Info Nothing) = ""
renderInfo (Info (Just (_, parsed))) = renderParsed parsed

renderParsed :: Parsed -> String
renderParsed (Parsed d _) = case d of
  (Directed f l c _ _) -> decodeUtf8 f ++ ":" ++ show (succ l) ++ ":" ++ show c
  (Lines l c _ _) -> "<interactive>:" ++ show (succ l) ++ ":" ++ show c
  _ -> "<interactive>:0:0"


class HasInfo a where
  getInfo :: a -> Info

instance HasInfo Info where getInfo = id

type MkInfo = Parsed -> Info

{-# INLINE mkEmptyInfo #-}
mkEmptyInfo :: MkInfo
mkEmptyInfo e = Info (Just (mempty,e))

{-# INLINE mkStringInfo #-}
mkStringInfo :: String -> MkInfo
mkStringInfo s d = Info (Just (fromString $ take (_pLength d) $
                               drop (fromIntegral $ TF.bytes d) s,d))

{-# INLINE mkTextInfo #-}
mkTextInfo :: T.Text -> MkInfo
mkTextInfo s d = Info (Just (Code $ T.take (_pLength d) $
                             T.drop (fromIntegral $ TF.bytes d) s,d))


data ConstVal n =
  CVRaw { _cvRaw :: !n } |
  CVEval { _cvRaw :: !n
        , _cvEval :: !n }
  deriving (Eq,Functor,Foldable,Traversable,Generic)

instance Show o => Show (ConstVal o) where
  show (CVRaw r) = show r
  show (CVEval _ e) = show e

instance Eq1 ConstVal where
  liftEq eq (CVRaw a) (CVRaw b) = eq a b
  liftEq eq (CVEval a c) (CVEval b d) = eq a b && eq c d
  liftEq _ _ _ = False


newtype NativeDefName = NativeDefName Text
    deriving (Eq,Ord,IsString,ToString,ToText)
    deriving Show via Text
