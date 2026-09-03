{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SPLL.Lang.Types
  ( ChainName
  , CompilerError
  , InjFName(..)
  , Expr(..)
  , ExprF(..)
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
  , valueContainsAny
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

-- | The AST node shapes, parameterised over the type of sub-expressions.
--
-- Splitting the shape out from the annotation is what makes the traversals in
-- "SPLL.Lang.Lang" generic: 'Functor' \/ 'Foldable' \/ 'Traversable' are derived
-- here, so @getSubExprs@, @tMap@, @tMapM@ and friends need no per-constructor
-- boilerplate.
--
-- Note that @Constant@ holds a concrete 'Value' rather than a @GenericValue a@.
-- A 'Value' can embed 'Expr's (inside a 'VClosure'), but those are *not*
-- sub-expressions of the AST: making the field parametric would drag closure
-- bodies into every derived traversal.
data ExprF a =
              -- Flow Control
                IfThenElse a a a
              | InjF InjFName [a]
              -- Variables
              | Var String
              | Constant Value
              | Lambda String a    -- (Currently) must use local context
              | Apply a a
              -- Parameters
              | ThetaI a Int
              | Subtree a Int
              -- Other
              | ReadNN String a
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq, Functor, Foldable, Traversable)

-- | An AST node: a 'TypeInfo' annotation paired with the node shape.
data Expr = Expr { ann :: TypeInfo, node :: ExprF Expr }
            deriving (Show, Eq)


data ExprStub = StubIfThenElse
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
                    -- explicit @neural writeLogits :: T of M@ declarations, or sugar registered
                    -- from a NeuralDecl's @of@ clause for its target/source type.
                    writeLogitsDecls :: [(RType, MultiValue)]
                    } deriving (Show, Eq)

type FnDecl = (String, Expr)

type NeuralDecl = (String, RType, Maybe MultiValue)

data ADTDecl = ADTDecl {
  dataName :: String,
  constructors :: [ADTConstructorDecl],
  -- | Default recursion-unroll depth.
  -- See 'autoDeriveMultiValue'.
  -- 'Nothing' for non-recursive types or when no default was given.
  adtDepth :: Maybe Int
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
           -- | A tensor: a statically-shaped, flat, homogeneous block of
           -- values. The element list is in row-major order (outermost axis
           -- first) and its length is always @shapeNumel@ of the shape, which
           -- is the invariant every producer maintains and 'tensorWellFormed'
           -- checks.
           --
           -- Flat with an explicit shape, as against 'VList''s cons spine:
           -- extent is known statically, so an index is O(1) and a reduction
           -- is one pass rather than a walk. Produced and consumed only by the
           -- tensor builtins ('BTensor', 'BMap', 'BReduce', 'BIndex') -- the
           -- surface language has no syntax for it and the parser never builds
           -- one, so it is unreachable in a 'Value' that came from a .ppl
           -- file. It lives in 'GenericValue' rather than a type of its own
           -- because the interpreter's let-environments are typed as
           -- 'IRValue', and a mapped tensor has to be let-bindable for one map
           -- to feed two reduces (design ir-tensor-values).
           --
           -- Element type is unconstrained here: homogeneity of /primitives/
           -- is not a typing obligation at this layer but a codegen
           -- opportunity -- a tensor of float/int/bool lowers to a real torch
           -- tensor with an O(1) gather and a vectorized reduce, anything else
           -- falls back to a generic list.
           | VTensor Shape [GenericValue a]
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
  fmap f (VTensor sh xs) = VTensor sh (map (fmap f) xs)
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

-- | Whether a value has a placeholder 'VAny'/'VAnyExcept' anywhere in its
-- structure (e.g. 'VEither (Left VAny)') -- distinct from the value itself
-- being 'VAny'. Used to tell a witness that only partially determines a value
-- (recovered from a lossy inverse, e.g. isLeft's, which knows the tag but not
-- the payload) apart from a fully concrete one.
valueContainsAny :: GenericValue a -> Bool
valueContainsAny VAny = True
valueContainsAny (VAnyExcept _) = True
valueContainsAny (VEither (Left v)) = valueContainsAny v
valueContainsAny (VEither (Right v)) = valueContainsAny v
valueContainsAny (VTuple a b) = valueContainsAny a || valueContainsAny b
valueContainsAny (VADT _ vs) = any valueContainsAny vs
valueContainsAny (VList l) = listContainsAny l
  where
    listContainsAny EmptyList = False
    listContainsAny AnyList = True
    listContainsAny (ListCont x xs) = valueContainsAny x || listContainsAny xs
valueContainsAny _ = False

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
