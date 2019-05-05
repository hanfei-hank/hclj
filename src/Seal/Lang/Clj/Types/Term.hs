{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      :  Seal.Lang.Clj.Types.Term
--
-- Term and related types.
--

module Seal.Lang.Clj.Types.Term
 (
   Meta(..),mDocs,mModel,
   DefType(..),
   defTypeRep,
   NativeDefName(..),
   FunApp(..),faDefType,faDocs,faInfo,faModule,faName,faTypes,
   Ref(..),
   NativeDFun(..),
   BindType(..),
   Module(..),mName,mMeta,mCode,mInterfaces,
   ModuleName(..),
   Name(..),
   ConstVal(..),
   Term(..),
   DefVisibility(..),
   tAppArgs,tAppFun,tBindBody,tBindPairs,tBindType,tConstArg,tConstVal,
   tDefBody,tDefName,tDefType,tMeta,tFunTypes,tFunType,tInfo,
   tListType,tList,tLiteral,tModuleBody,tModuleDef,tModuleName,tModule,
   tNativeDocs,tNativeFun,tNativeName,tNativeTopLevelOnly,tObjectType,tObject,
   tVar,tVisibility,
   ToTerm(..),
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


data Meta = Meta
  { _mDocs  :: !(Maybe Text) -- ^ docs
  , _mModel :: ![Exp Info]   -- ^ model
  } deriving (Eq, Show, Generic)
instance Default Meta where def = Meta def def


data DefType = Defun deriving (Eq,Show)
defTypeRep :: DefType -> String
defTypeRep Defun = "defn"

newtype NativeDefName = NativeDefName Text
    deriving (Eq,Ord,IsString,ToString,ToText)
    deriving Show via Text

-- | Capture function application metadata
data FunApp = FunApp {
      _faInfo :: !Info
    , _faName :: !Text
    , _faModule :: !(Maybe ModuleName)
    , _faDefType :: !DefType
    , _faTypes :: !(FunTypes (Term Name))
    , _faDocs :: !(Maybe Text)
    }

instance Show FunApp where
  show FunApp {..} =
    "(" ++ defTypeRep _faDefType ++ " " ++ maybeDelim "." _faModule ++
    unpack _faName ++ " " ++ showFunTypes _faTypes ++ ")"


-- | Variable type for an evaluable 'Term'.
data Ref =
  -- | "Reduced" (evaluated) or native (irreducible) term.
  Direct (Term Name) |
  -- | Unevaulated/un-reduced term, never a native.
  Ref (Term Ref)
               deriving (Eq)
instance Show Ref where
    show (Direct t) = abbrev t
    show (Ref t) = abbrev t

data NativeDFun = NativeDFun {
      _nativeName :: NativeDefName,
      _nativeFun :: forall m . Monad m => FunApp -> [Term Ref] -> m (Term Name)
    }
instance Eq NativeDFun where a == b = _nativeName a == _nativeName b
instance Show NativeDFun where show a = show $ _nativeName a

-- | Binding forms.
data BindType n =
  -- | Normal "let" bind
  BindLet |
  -- | Schema-style binding, with string value for key
  BindSchema { _bType :: n }
  deriving (Eq,Functor,Foldable,Traversable,Ord)
instance (Show n) => Show (BindType n) where
  show BindLet = "let"
  show (BindSchema b) = "bind" ++ show b
instance (Pretty n) => Pretty (BindType n) where
  pretty BindLet = "let"
  pretty (BindSchema b) = "bind" PP.<> pretty b

instance Eq1 BindType where
  liftEq _ BindLet BindLet = True
  liftEq eq (BindSchema a) (BindSchema m) = eq a m
  liftEq _ _ _ = False

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
  

-- TODO: We need a more expressive, safer ADT for this.
data Module
 = Module
 { _mName :: !ModuleName
 , _mMeta :: !Meta
 , _mCode :: !Code
 , _mInterfaces :: [ModuleName]
 } deriving Eq

instance Show Module where
  show m = case m of
    Module{..} -> "(Contract " ++ toString _mName ++ " '" ++ ")"

                     
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

data DefVisibility = PUBLIC | PRIVATE
     deriving (Eq, Show, Generic)


-- | clj evaluable term.
data Term n =
    TModule {
      _tModuleDef :: Module
    , _tModuleBody :: !(Scope () Term n)
    , _tInfo :: !Info
    } |
    TList {
      _tList :: ![Term n]
    , _tListType :: Type (Term n)
    , _tInfo :: !Info
    } |
    TDef {
     _tVisibility :: !DefVisibility
    , _tDefName :: !Text
    , _tModule :: !ModuleName
    , _tDefType :: !DefType
    , _tFunType :: !(FunType (Term n))
    , _tDefBody :: !(Scope Int Term n)
    , _tMeta :: !Meta
    , _tInfo :: !Info
    } |
    TNative {
      _tNativeName :: !NativeDefName
    , _tNativeFun :: !NativeDFun
    , _tFunTypes :: FunTypes (Term n)
    , _tNativeDocs :: Text
    , _tNativeTopLevelOnly :: Bool
    , _tInfo :: !Info
    } |
    TConst {
      _tConstArg :: !(Arg (Term n))
    , _tModule :: !ModuleName
    , _tConstVal :: !(ConstVal (Term n))
    , _tMeta :: !Meta
    , _tInfo :: !Info
    } |
    TApp {
      _tAppFun :: !(Term n)
    , _tAppArgs :: ![Term n]
    , _tInfo :: !Info
    } |
    TVar {
      _tVar :: !n
    , _tInfo :: !Info
    } |
    TBinding {
      _tBindPairs :: ![(Arg (Term n),Term n)]
    , _tBindBody :: !(Scope Int Term n)
    , _tBindType :: BindType (Type (Term n))
    , _tInfo :: !Info
    } |
    TObject {
      _tObject :: ![(Term n,Term n)]
    , _tObjectType :: !(Type (Term n))
    , _tInfo :: !Info
    } |
    TLiteral {
      _tLiteral :: !Literal
    , _tInfo :: !Info
    } |
    TUse {
      _tModuleName :: !ModuleName
    , _tInfo :: !Info
    } 
   deriving (Functor,Foldable,Traversable,Eq)

instance Show n => Show (Term n) where
    show TModule {..} =
      "(TModule " ++ show _tModuleDef ++ " " ++ show (unscope _tModuleBody) ++ ")"
    show (TList bs _ _) = "[" ++ unwords (map show bs) ++ "]"
    show TDef {..} =
      "(TDef " ++ defTypeRep _tDefType ++ " " ++ toString _tModule ++ "." ++ unpack _tDefName ++ " " ++
      show _tFunType ++ " " ++ show _tMeta ++ " " ++ show _tVisibility ++ ")"
    show TNative {..} =
      "(TNative " ++ toString _tNativeName ++ " " ++ showFunTypes _tFunTypes ++ " " ++ unpack _tNativeDocs ++ ")"
    show TConst {..} =
      "(TConst " ++ toString _tModule ++ "." ++ show _tConstArg ++ " " ++ show _tMeta ++ ")"
    show (TApp f as _) = "(TApp " ++ show f ++ " " ++ show as ++ ")"
    show (TVar n _) = "(TVar " ++ show n ++ ")"
    show (TBinding bs b c _) = "(TBinding " ++ show bs ++ " " ++ show (unscope b) ++ " " ++ show c ++ ")"
    show (TObject bs _ _) =
      "{" ++ intercalate ", " (map (\(a,b) -> show a ++ " " ++ show b) bs) ++ "}"
    show (TLiteral l _) = show l
    show (TUse m _) = "(TUse " ++ show m ++ ")"

showParamType :: Show n => Type n -> String
showParamType TyAny = ""
showParamType t = ":" ++ show t

--deriveEq1 ''Term
-- instance Show1 Term
instance Eq1 Term where
  liftEq eq (TModule a b c) (TModule m n o) =
    a == m && liftEq eq b n && c == o
  liftEq eq (TList a b c) (TList m n o) =
    liftEq (liftEq eq) a m && liftEq (liftEq eq) b n && c == o
  liftEq eq (TDef h a b c d e f g) (TDef t m n o p q r s) =
    h == t && a == m && b == n && c == o && liftEq (liftEq eq) d p && liftEq eq e q && f == r && g == s 
  liftEq eq (TConst a b c d e) (TConst m n o q r) =
    liftEq (liftEq eq) a m && b == n && liftEq (liftEq eq) c o && d == q && e == r
  liftEq eq (TApp a b c) (TApp m n o) =
    liftEq eq a m && liftEq (liftEq eq) b n && c == o
  liftEq eq (TVar a b) (TVar m n) =
    eq a m && b == n
  liftEq eq (TBinding a b c d) (TBinding m n o p) =
    liftEq (\(w,x) (y,z) -> liftEq (liftEq eq) w y && liftEq eq x z) a m &&
    liftEq eq b n && liftEq (liftEq (liftEq eq)) c o && d == p
  liftEq eq (TObject a b c) (TObject m n o) =
    liftEq (\(w,x) (y,z) -> liftEq eq w y && liftEq eq x z) a m && liftEq (liftEq eq) b n && c == o
  liftEq _ (TLiteral a b) (TLiteral m n) =
    a == m && b == n
  liftEq _ (TUse a c) (TUse m o) =
    a == m &&  c == o
  liftEq _ _ _ = False


instance Applicative Term where
    pure = return
    (<*>) = ap

instance Monad Term where
    return a = TVar a def
    TModule m b i >>= f = TModule m (b >>>= f) i
    TList bs t i >>= f = TList (map (>>= f) bs) (fmap (>>= f) t) i
    TDef p n m dt ft b d i >>= f = TDef p n m dt (fmap (>>= f) ft) (b >>>= f) d i
    TNative n fn t d tl i >>= f = TNative n fn (fmap (fmap (>>= f)) t) d tl i
    TConst d m c t i >>= f = TConst (fmap (>>= f) d) m (fmap (>>= f) c) t i
    TApp af as i >>= f = TApp (af >>= f) (map (>>= f) as) i
    TVar n i >>= f = (f n) { _tInfo = i }
    TBinding bs b c i >>= f = TBinding (map (fmap (>>= f) *** (>>= f)) bs) (b >>>= f) (fmap (fmap (>>= f)) c) i
    TObject bs t i >>= f = TObject (map ((>>= f) *** (>>= f)) bs) (fmap (>>= f) t) i
    TLiteral l i >>= _ = TLiteral l i
    TUse m i >>= _ = TUse m i



class ToTerm a where
    toTerm :: a -> Term m
instance ToTerm Bool where toTerm = tLit . LBool
instance ToTerm Integer where toTerm = tLit . LInteger
instance ToTerm Int where toTerm = tLit . LInteger . fromIntegral
instance ToTerm Decimal where toTerm = tLit . LDecimal
instance ToTerm Text where toTerm = tLit . LString
instance ToTerm String where toTerm s = case s of 
                                          (':':xs) ->  tLit . LKeyword $ pack xs 
                                          _        ->  tLit . LString $ pack s
instance ToTerm Literal where toTerm = tLit
instance ToTerm UTCTime where toTerm = tLit . LTime


toTObject :: Type (Term n) -> Info -> [(Term n,Term n)] -> Term n
toTObject ty i ps = TObject ps ty i

toTList :: Type (Term n) -> Info -> [Term n] -> Term n
toTList ty i vs = TList vs ty i

toTermList :: (ToTerm a,Foldable f) => Type (Term b) -> f a -> Term b
toTermList ty l = TList (map toTerm (toList l)) ty def



-- | Return a clj type, or a String description of non-value Terms.
typeof :: Term a -> Either Text (Type (Term a))
typeof t = case t of
      TLiteral l _ -> Right $ TyPrim $ litToPrim l
      TModule {} -> Left "contract"
      TList {..} -> Right $ TyList _tListType
      TDef {..} -> Left $ pack $ defTypeRep _tDefType
      TNative {..} -> Left "def"
      TConst {..} -> Left $ "const:" <> _aName _tConstArg
      TApp {..} -> Left "app"
      TVar {..} -> Left "var"
      TBinding {..} -> case _tBindType of
        BindLet -> Left "let"
        BindSchema bt -> Right $ TySchema TyBinding bt
      TObject {..} -> Right $ TySchema TyObject _tObjectType
      TUse {} -> Left "use"

{-# INLINE typeof #-}

-- | Return string type description.
typeof' :: Show a => Term a -> Text
typeof' = either id (pack . show) . typeof

pattern TLitString :: Text -> Term t
pattern TLitString s <- TLiteral (LString s) _
pattern TLitInteger :: Integer -> Term t
pattern TLitInteger i <- TLiteral (LInteger i) _
pattern TLitBool :: Bool -> Term t
pattern TLitBool b <- TLiteral (LBool b) _
pattern TLitKeyword :: Text -> Term t
pattern TLitKeyword s <- TLiteral (LKeyword s) _

tLit :: Literal -> Term n
tLit = (`TLiteral` def)
{-# INLINE tLit #-}

-- | Convenience for OverloadedStrings annoyances
tStr :: Text -> Term n
tStr = toTerm

-- | Support pact `=` for value-level terms
termEq :: Eq n => Term n -> Term n -> Bool
termEq (TList a _ _) (TList b _ _) = length a == length b && and (zipWith termEq a b)
termEq (TObject a _ _) (TObject b _ _) = length a == length b && all (lkpEq b) a
    where lkpEq [] _ = False
          lkpEq ((k',v'):ts) p@(k,v) | termEq k k' && termEq v v' = True
                                     | otherwise = lkpEq ts p
termEq (TLiteral a _) (TLiteral b _) = a == b
termEq _ _ = False




abbrev :: Show t => Term t -> String
abbrev (TModule m _ _) =
  case m of
    Module{..} -> "<contract " ++ toString _mName ++ ">"
abbrev (TList bs tl _) = "<list(" ++ show (length bs) ++ ")" ++ showParamType tl ++ ">"
abbrev TDef {..} = "<defn " ++ unpack _tDefName ++ ">"
abbrev TNative {..} = "<native " ++ toString _tNativeName ++ ">"
abbrev TConst {..} = "<def " ++ show _tConstArg ++ ">"
abbrev t@TApp {} = "<app " ++ abbrev (_tAppFun t) ++ ">"
abbrev TBinding {} = "<binding>"
abbrev TObject {..} = "<object" ++ showParamType _tObjectType ++ ">"
abbrev (TLiteral l _) = show l
abbrev (TUse m _) = "<use '" ++ show m ++ ">"
abbrev (TVar s _) = show s


makeLenses ''Term
makeLenses ''FunApp
makeLenses ''Meta
makeLenses ''Module
