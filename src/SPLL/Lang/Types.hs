module SPLL.Lang.Types where


import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set


import qualified Data.Map as Map
import Control.Applicative (liftA2)
import Control.Monad.Random.Lazy (Random)
import Data.Number.Erf (Erf)

import Data.Set (empty)


type ChainName = String

-- (Set of Preconditions with CType, set of Inferable variables with attached CType, Expression this HornClause originates from with its inversion number
type HornClause a = ([(ChainName, CType a)], [(ChainName, CType a)], (ExprStub, Int))

data CType a = CDeterministic
             | CInferDeterministic
             | CConstrainedTo a a
             | CBottom
             | CNotSetYet
             deriving (Show, Eq)

instance Eq a => Ord (CType a) where
  compare x y = compare (rank x) (rank y)
    where
      rank CDeterministic = 10
      rank CInferDeterministic = 9
      rank (CConstrainedTo _ _) = 5
      rank CBottom = 1
      rank CNotSetYet = -1



--Expr x (a :: Precision)
--data Precision = P32 | P64"
--type family PrecisionType P32 = Float
data Expr a =
              -- Flow Control
                IfThenElse (TypeInfo a) (Expr a) (Expr a) (Expr a)
              | Call (TypeInfo a) String
              | CallArg (TypeInfo a) String [Expr a]
              | InjF (TypeInfo a) String [Expr a]
              -- Arithmetic
              | MultF (TypeInfo a) (Expr a) (Expr a)
              | MultI (TypeInfo a) (Expr a) (Expr a)
              | PlusF (TypeInfo a) (Expr a) (Expr a)
              | PlusI (TypeInfo a) (Expr a) (Expr a)
              | ExpF (TypeInfo a) (Expr a)
              | NegF (TypeInfo a) (Expr a)
              -- Variables
              | LetIn (TypeInfo a) String (Expr a) (Expr a)
              | Var (TypeInfo a) String
              | Constant (TypeInfo a) (Value a)
              | Lambda (TypeInfo a) String (Expr a)    -- (Currently) must use local context
              | Apply (TypeInfo a) (Expr a) (Expr a)
              -- Distributions
              | Uniform (TypeInfo a)
              | Normal (TypeInfo a)
              | ThetaI (TypeInfo a) (Expr a) Int
              | Subtree (TypeInfo a) (Expr a) Int
              -- Lists/Tuples
              | Cons (TypeInfo a) (Expr a) (Expr a)
              | TCons (TypeInfo a) (Expr a) (Expr a)
              | Null (TypeInfo a)
              -- Boolean Operations
              | GreaterThan (TypeInfo a) (Expr a) (Expr a)
              | LessThan (TypeInfo a) (Expr a) (Expr a)
              | And (TypeInfo a) (Expr a) (Expr a)
              | Or (TypeInfo a) (Expr a) (Expr a)
              | Not (TypeInfo a) (Expr a)
              -- Other
              | Arg (TypeInfo a) String RType (Expr a)
              | ReadNN (TypeInfo a) String (Expr a)
              | Fix (TypeInfo a) (Expr a)
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq, Ord)


data ExprStub = StubIfThenElse
              | StubGreaterThan
              | StubLessThan
              | StubThetaI
              | StubSubtree
              | StubUniform
              | StubNormal
              | StubConstant
              | StubMultF
              | StubMultI
              | StubPlusF
              | StubPlusI
              | StubNegF
              | StubNot
              | StubExpF
              | StubNull
              | StubCons
              | StubTCons
              | StubCall
              | StubVar
              | StubLetIn
              | StubArg
              | StubInjF
              | StubCallArg
              | StubLambda
              | StubApply
              | StubReadNN
              deriving (Show, Eq, Ord)

--Do not use this constructor, use makeTypeInfo instead
data TypeInfo a = TypeInfo
  { rType :: RType
  , pType :: PType
  , cType :: CType a
  , derivingHornClause :: Maybe (HornClause a)
  , witnessedVars :: WitnessedVars
  , chainName :: ChainName
  , tags :: [Tag a]} deriving (Show, Eq, Ord)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.

makeTypeInfo :: TypeInfo a
makeTypeInfo = TypeInfo
    { rType = SPLL.Typing.RType.NotSetYet
    , pType = SPLL.Typing.PType.NotSetYet
    , cType = CNotSetYet
    , derivingHornClause = Nothing
    , witnessedVars = empty
    , chainName = ""
    , tags = []}


type Name = String

data Program a = Program {
                    functions :: [FnDecl a],
                    neurals :: [NeuralDecl a],
                    main :: (Expr a)
                    } deriving (Show, Eq)

type FnDecl a = (String, Expr a)

type NeuralDecl a = (String, RType, Tag a)

type WitnessedVars = Set.Set String

data ThetaTree a = ThetaTree [a] [ThetaTree a] deriving (Show, Eq, Ord)

data Value a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat a
           | VList [Value a]
           | VTuple (Value a) (Value a)
           | VBranch (Value a) (Value a) String
           | VRange (Limits a)
           | VThetaTree (ThetaTree a)
           | VAnyList
           -- | Value of TArrow a b could be Expr TypeInfo a, with Expr being a Lambda?
           deriving (Show, Eq, Ord)
-- likelihood [vMarg, vAnyList] - likelihood [vMarg, vMarg, vAnylist]
--Nothing indicates low/high infinity.
data Limits a = Limits (Maybe (Value a)) (Maybe (Value a))
           deriving (Show, Eq, Ord)

instance Functor Value where
  fmap = valMap

valMap :: (a -> b) -> Value a -> Value b
valMap f (VBool b) = VBool b
valMap f (VInt i) = VInt i
valMap f (VSymbol i) = VSymbol i
valMap f (VFloat a) = VFloat $ f a
valMap f (VList v) = VList $ map (valMap f) v
valMap f (VTuple v1 v2) = VTuple (valMap f v1) (valMap f v2)
valMap f (VBranch v1 v2 x ) = VBranch (valMap f v1) (valMap f v2) x
valMap f (VRange v1) = VRange (limitsMap f v1)
valMap f VAnyList = VAnyList

limitsMap :: (a -> b) -> Limits a -> Limits b
limitsMap f (Limits a b) = Limits (fmap (valMap f) a) (fmap (valMap f) b)

data Tag a = EnumRange (Value a, Value a)
           | EnumList [Value a]
           | Alg InferenceRule
           deriving (Show, Eq, Ord)

data RuleConstraint = SubExprNIsType Int PType
                    | SubExprNIsNotType Int PType
                    | SubExprNIsAtLeast Int PType
                    | ResultingTypeMatch
                    deriving (Show, Eq, Ord)

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
