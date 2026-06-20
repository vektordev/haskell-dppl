module SPLL.Lang.Types
  ( ChainName
  , CompilerError
  , InjFName(..)
  , Expr(..)
  , ExprStub(..)
  , TypeInfo(..)
  , makeTypeInfo
  , Name
  , Program(..)
  , FnDecl
  , NeuralDecl
  , ADTDecl(..)
  , ADTConstructorDecl
  , ThetaTree(..)
  , GenericList(..)
  , ValueList
  , Value
  , GenericValue(..)
  , isVEither, isVTuple, isVADT
  , MultiValue(..)
  , Tag(..)
  , InferenceRule(..)
  ) where


import SPLL.Typing.PType
import SPLL.Typing.RType
import Data.Bifunctor (second)


type ChainName = String

type CompilerError = String

data InjFName = Named String
              deriving (Show, Eq)

data Expr =
              -- Flow Control
                IfThenElse TypeInfo Expr Expr Expr
              | InjF TypeInfo InjFName [Expr]
              -- Variables
              | Var TypeInfo String
              | Constant TypeInfo Value
              | Lambda TypeInfo String Expr    -- (Currently) must use local context
              | Apply TypeInfo Expr Expr
              -- Parameters
              | ThetaI TypeInfo Expr Int
              | Subtree TypeInfo Expr Int
              -- Boolean Operations
              | GreaterThan TypeInfo Expr Expr
              | LessThan TypeInfo Expr Expr
              -- Other
              | ReadNN TypeInfo String Expr
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq)


data ExprStub = StubIfThenElse
              | StubGreaterThan
              | StubLessThan
              | StubThetaI
              | StubSubtree
              | StubConstant
              | StubVar
              | StubInjF
              | StubLambda
              | StubApply
              | StubReadNN
              deriving (Show, Eq)
--Do not use this constructor, use makeTypeInfo instead
data TypeInfo = TypeInfo
  { rType :: RType
  , pType :: PType
  , chainName :: ChainName
  , tags :: [Tag]} deriving (Show, Eq)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.

makeTypeInfo :: TypeInfo
makeTypeInfo = TypeInfo
    { rType = SPLL.Typing.RType.NotSetYet
    , pType = SPLL.Typing.PType.NotSetYet
    , chainName = ""
    , tags = []}


type Name = String

data Program = Program {
                    functions :: [FnDecl],
                    neurals :: [NeuralDecl],
                    adts :: [ADTDecl],
                    -- | Standalone PartitionPlan annotations, keyed by RType: either
                    -- explicit @neural encode :: T of M@ declarations, or sugar registered
                    -- from a NeuralDecl's @of@ clause for its target/source type.
                    encodeDecls :: [(RType, MultiValue)]
                    } deriving (Show, Eq)

type FnDecl = (String, Expr)

type NeuralDecl = (String, RType, Maybe MultiValue)

data ADTDecl = ADTDecl {
  dataName :: String,
  constructors :: [ADTConstructorDecl]
  } deriving (Show, Eq)
type ADTConstructorDecl = (String, [(String, RType)])

data ThetaTree = ThetaTree [Double] [ThetaTree] deriving (Show, Eq)

data GenericList a = EmptyList | ListCont a (GenericList a) | AnyList deriving (Show, Eq)
type ValueList a = GenericList (GenericValue a)

instance Functor GenericList where
  fmap _ EmptyList = EmptyList
  fmap f (ListCont x xs) = ListCont (f x) (fmap f xs) 
  fmap _ AnyList = AnyList

instance Foldable GenericList where
  foldMap _ EmptyList = mempty
  foldMap f (ListCont x xs) = f x `mappend` foldMap f xs
  foldMap _ AnyList = error "Cannot fold AnyLists"

instance Traversable GenericList where
  traverse _ EmptyList = pure EmptyList
  traverse f (ListCont x xs) = ListCont <$> f x <*> traverse f xs
  traverse _ AnyList = error "AnyLists are not traversable"

type Value = GenericValue Expr

data GenericValue a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat Double
           | VUnit
           | VList (GenericList (GenericValue a))
           | VTuple (GenericValue a) (GenericValue a)
           | VEither (Either (GenericValue a) (GenericValue a))
           | VThetaTree ThetaTree
           | VClosure [(String, a)] String a
           | VADT String [GenericValue a]
           | VAny -- Only used for marginal queries
           | VAnyExcept [a] -- Only used for marginal queries
           | VError String
           deriving (Show, Eq)

instance Functor GenericValue where
  fmap _ (VInt x) = VInt x
  fmap _ (VBool x) = VBool x
  fmap _ (VSymbol x) = VSymbol x
  fmap _ (VFloat x) = VFloat x
  fmap _ VUnit = VUnit
  fmap f (VList x) = VList (fmap (fmap f) x)
  fmap f (VTuple x y) = VTuple (fmap f x) (fmap f y)
  fmap f (VEither (Left x)) = VEither (Left (fmap f x))
  fmap f (VEither (Right x)) = VEither (Right (fmap f x))
  fmap _ (VThetaTree x) = VThetaTree x
  fmap f (VClosure e n ex) = VClosure (map (Data.Bifunctor.second f) e) n (f ex)
  fmap f (VADT n adt) = VADT n (map (fmap f) adt)
  fmap f (VAnyExcept x) = VAnyExcept (map f x)
  fmap _ VAny = VAny
  fmap _ (VError s) = VError s


isVTuple, isVEither, isVADT :: GenericValue a -> Bool
isVTuple (VTuple _ _) = True
isVTuple _ = False
isVEither (VEither _) = True
isVEither _ = False
isVADT (VADT _ _) = True
isVADT _ = False

data MultiValue = MultiDiscretes [Value]
                | MultiTuple MultiValue MultiValue
                | MultiEither MultiValue MultiValue
                | MultiADT [(String, [MultiValue])]
                | MultiTypeRef String
                | MultiContinuous     -- ^ A continuous (Float) leaf, written "Real" in .ppl source.
                | MultiAuto           -- ^ Placeholder ("_" in .ppl source): auto-derive from the RType.
                deriving (Show, Eq)


data Tag = DiscreteValues MultiValue
           | IsConditional
           deriving (Show, Eq)
           


-- | A return-type rule: maps an expression shape (ExprStub) to the RType scheme
-- it produces.  Used solely by RInfer for return-type inference.  (Probabilistic
-- algorithm selection no longer lives here — it is done directly in IRCompiler from
-- pType / enumerability annotations.)
data InferenceRule = InferenceRule { forExpression :: ExprStub
                                   , algName :: String
                                   , assumedRType :: Scheme
                                   }

instance Show InferenceRule where
  show (InferenceRule _ name _) = name

instance Eq InferenceRule where
  a1 == a2 = algName a1 == algName a2

instance Ord InferenceRule where
  a1 `compare` a2 = algName a1 `compare` algName a2
