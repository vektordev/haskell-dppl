module SPLL.Lang.Types where


import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set


import qualified Data.Map as Map
import Control.Applicative (liftA2)
import Control.Monad.Random.Lazy (Random)
import Data.Number.Erf (Erf)
import Data.Bifunctor (second)

import Data.Set (empty)
import Data.PartialOrd (PartialOrd((<=)))
import Data.Maybe


type ChainName = String

-- (Set of Preconditions with CType, set of Inferable variables with attached CType, Expression this HornClause originates from with its inversion number
data ExprType = Stub ExprStub | AnnotStub ExprStub String | AnnotValueStub ExprStub (GenericValue Expr) deriving (Show, Eq)
data HornClause = HornClause [(ChainName, CType)] [(ChainName, CType)] (ChainName, ExprType, Int) deriving (Show, Eq)

data CType = CDeterministic
             | CInferDeterministic
             | CConstrainedTo Double Double
             | CBottom
             | CNotSetYet
             deriving (Show, Eq)

instance Ord CType where
  compare x y = compare (rank x) (rank y)
    where
      rank CDeterministic = 10
      rank CInferDeterministic = 9
      rank (CConstrainedTo _ _) = 5
      rank CBottom = 1
      rank CNotSetYet = -1


data Expr =
              -- Flow Control
                IfThenElse TypeInfo Expr Expr Expr
              | InjF TypeInfo String [Expr]
              -- Variables
              | LetIn TypeInfo String Expr Expr
              | Var TypeInfo String
              | Constant TypeInfo Value
              | Lambda TypeInfo String Expr    -- (Currently) must use local context
              | Apply TypeInfo Expr Expr
              -- Distributions
              | Uniform TypeInfo
              | Normal TypeInfo
              -- Parameters
              | ThetaI TypeInfo Expr Int
              | Subtree TypeInfo Expr Int
              -- Lists/Tuples
              | Cons TypeInfo Expr Expr
              | TCons TypeInfo Expr Expr
              | Null TypeInfo
              -- Boolean Operations
              | GreaterThan TypeInfo Expr Expr
              | LessThan TypeInfo Expr Expr
              | And TypeInfo Expr Expr
              | Or TypeInfo Expr Expr
              | Not TypeInfo Expr
              -- Other
              | ReadNN TypeInfo String Expr
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq)


data ExprStub = StubIfThenElse
              | StubGreaterThan
              | StubLessThan
              | StubThetaI
              | StubSubtree
              | StubUniform
              | StubNormal
              | StubConstant
              | StubNot
              | StubAnd
              | StubOr
              | StubNull
              | StubCons
              | StubTCons
              | StubVar
              | StubLetIn
              | StubInjF
              | StubLambda
              | StubApply
              | StubReadNN
              deriving (Show, Eq)

--Do not use this constructor, use makeTypeInfo instead
data TypeInfo = TypeInfo
  { rType :: RType
  , pType :: PType
  , cType :: CType
  , derivingHornClause :: Maybe HornClause
  , witnessedVars :: WitnessedVars
  , chainName :: ChainName
  , tags :: [Tag]} deriving (Show, Eq)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.

makeTypeInfo :: TypeInfo
makeTypeInfo = TypeInfo
    { rType = SPLL.Typing.RType.NotSetYet
    , pType = SPLL.Typing.PType.NotSetYet
    , cType = CNotSetYet
    , derivingHornClause = Nothing
    , witnessedVars = empty
    , chainName = ""
    , tags = []}


type Name = String

data Program = Program {
                    functions :: [FnDecl],
                    neurals :: [NeuralDecl]
                    } deriving (Show, Eq)

type FnDecl = (String, Expr)

type NeuralDecl = (String, RType, Maybe Tag)

type WitnessedVars = Set.Set String

data ThetaTree = ThetaTree [Double] [ThetaTree] deriving (Show, Eq)

data GenericList a = EmptyList | ListCont a (GenericList a) | AnyList deriving (Show, Eq)
type ValueList a = GenericList (GenericValue a)

instance Functor GenericList where
  fmap _ EmptyList = EmptyList
  fmap f (ListCont x xs) = ListCont (f x) (fmap f xs) 
  fmap _ AnyList = AnyList

instance Foldable GenericList where
  foldMap f EmptyList = mempty
  foldMap f (ListCont x xs) = f x `mappend` foldMap f xs
  foldMap f AnyList = error "Cannot fold AnyLists"

type Value = GenericValue Expr

data GenericValue a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat Double
           | VList (GenericList (GenericValue a))
           | VTuple (GenericValue a) (GenericValue a)
           | VEither (Either (GenericValue a) (GenericValue a))
           | VBranch (GenericValue a) (GenericValue a) String
           | VThetaTree ThetaTree
           | VClosure [(String, a)] String a 
           | VAny -- Only used for marginal queries
           -- | Value of TArrow a b could be Expr TypeInfo, with Expr being a Lambda?
           deriving (Show, Eq)

instance Functor GenericValue where
  fmap _ (VInt x) = VInt x
  fmap _ (VBool x) = VBool x
  fmap _ (VSymbol x) = VSymbol x
  fmap _ (VFloat x) = VFloat x
  fmap f (VList x) = VList (fmap (fmap f) x)
  fmap f (VTuple x y) = VTuple (fmap f x) (fmap f y)
  fmap f (VEither (Left x)) = VEither (Left (fmap f x))
  fmap f (VEither (Right x)) = VEither (Right (fmap f x))
  fmap f (VBranch x y s) = VBranch (fmap f x) (fmap f y) s
  fmap _ (VThetaTree x) = VThetaTree x
  fmap f (VClosure e n ex) = VClosure (map (Data.Bifunctor.second f) e) n (f ex)
  fmap _ VAny = VAny


isVInt, isVBool, isVSymbol, isVFloat, isVList, isVTuple, isVBranch, isVThetaTree, isVClosure :: GenericValue a -> Bool
isVInt (VInt _) = True
isVInt _ = False
isVBool (VBool _) = True
isVBool _ = False
isVSymbol (VSymbol _) = True
isVSymbol _ = False
isVFloat (VFloat _) = True
isVFloat _ = False
isVList (VList _) = True
isVList _ = False
isVTuple (VTuple _ _) = True
isVTuple _ = False
isVBranch (VBranch _ _ _) = True
isVBranch _ = False
isVThetaTree (VThetaTree _) = True
isVThetaTree _ = False
isVClosure (VClosure _ _ _) = True
isVClosure _ = False


data Tag = EnumRange (Value, Value)
           | EnumList [Value]
           | Alg InferenceRule
           deriving (Show, Eq)
           


data RuleConstraint = SubExprNIsType Int PType
                    | SubExprNIsNotType Int PType
                    | SubExprNIsAtLeast Int PType
                    | SubExprNIsEnumerable Int
                    | ResultingTypeMatch
                    deriving (Show, Eq)

-- can we encode symmetries?
data InferenceRule = InferenceRule { forExpression :: ExprStub
                                   , constraints :: [RuleConstraint]
                                   , algName :: String
                                   --apply all subexpr PTypes to find PType
                                   , resultingPType :: [PType] -> PType
                                   , assumedRType :: Scheme
                                   }

instance Show InferenceRule where
  show (InferenceRule _ _ name _ _) = name

instance Eq InferenceRule where
  a1 == a2 = algName a1 == algName a2

instance Ord InferenceRule where
  a1 `compare` a2 = algName a1 `compare` algName a2

instance PartialOrd HornClause where
  -- They B depends on A
  HornClause pre1 conc1 _ <= HornClause pre2 conc2 _ = any (\(cn, ct) -> isJust (lookup cn conc1) && fromJust (lookup cn conc1) >= ct) pre2
