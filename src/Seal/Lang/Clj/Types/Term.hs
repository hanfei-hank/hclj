{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- |
--
-- Term and related types.
--

module Seal.Lang.Clj.Types.Term
 (
   Meta(..),mDocs,mModel,
   NativeDefName(..),
   FunApp(..),faDocs,faInfo,faModule,faName,faTypes,
   Ref(..),
   NativeDFun(..),
   BindType(..),
   Module(..),mName,mMeta,mCode,
   ModuleName(..),
   Name(..),
   ConstVal(..),
   Term(..),
   DefVisibility(..),
   tAppArgs,tAppFun,tBindBody,tBindPairs,tBindType,tConstArg,tConstVal,
   tDefBody,tDefName,tMeta,tFunTypes,tFunType,tInfo,
   tListType,tList,tLiteral,tModuleBody,tModuleDef,tModuleName,tModule,
   tNativeDocs,tNativeFun,tNativeName,tNativeTopLevelOnly,tObjectType,tObject,
   tVar,tVisibility,
   ToTerm(..),toTermLiteral,
   toTermList,toTObject,toTList,
   typeof,typeof',
   pattern TLitString,pattern TLitInteger,pattern TLitBool, pattern TLitKeyword,
   tLit,tStr,termEq,abbrev
   ) where


import Seal.Prelude hiding ((.=))
import Control.Arrow ((***))
import Data.Functor.Classes
import Bound
import Data.Text (Text,pack,unpack)
import Data.Thyme
import GHC.Generics (Generic)
import Data.Decimal
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.PrettyPrint.ANSI.Leijen hiding ((<>),(<$>))

import Seal.Lang.Common.Util
import Seal.Lang.Common.Type
import Seal.Lang.Clj.Types.Type
import Seal.Lang.Clj.Types.Exp

import Seal.Lang.Clj.TH.Term

termQ
makeTermLenses

toTermLiteral :: ToLiteral a => a -> Term n
toTermLiteral = toTerm . toLiteral

pattern TLitString :: Text -> Term t
pattern TLitString s <- TLiteral (LString s) _
pattern TLitInteger :: Integer -> Term t
pattern TLitInteger i <- TLiteral (LInteger i) _
pattern TLitBool :: Bool -> Term t
pattern TLitBool b <- TLiteral (LBool b) _
pattern TLitKeyword :: Text -> Term t
pattern TLitKeyword s <- TLiteral (LKeyword s) _
