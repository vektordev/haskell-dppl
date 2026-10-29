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
  , SourceSpan(..)
  , spanPretty
  , desugaredSpan
  , Equiv(..)
  , Name
  , Program(..)
  , FnDecl
  , FnSignature(..)
  , SigStep(..)
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
  , MultiValue
  , GenericMultiValue(..)
  , Tag(..)
  , InferenceRule(..)
  ) where


import SPLL.IR.Value
import SPLL.Typing.PType
import SPLL.Typing.RType
import Data.Foldable (toList)
import Text.Megaparsec.Pos (SourcePos, sourcePosPretty)


type ChainName = String

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
-- | Where in the source a construct came from, for diagnostics.
--
-- @spanDesugaredFrom@ is what makes this usable for nodes the parser
-- *synthesizes* rather than reads. @letInDestructor@ turns @let h : t = e@ into
-- applications of the built-in @head@\/@tail@ InjFs, and a context chain that
-- printed those would be showing the user machine-generated code they never
-- wrote. So a synthesized node carries the span of the construct it was
-- desugared from, plus a human phrase naming it (@"the pattern: h : t"@), and
-- the renderer prints the phrase instead of the node.
data SourceSpan = SourceSpan
  { spanStart :: SourcePos
  , spanEnd :: SourcePos
  -- | @Just phrase@ when this node was synthesized by desugaring; the span then
  -- refers to the surface construct, not to this node.
  , spanDesugaredFrom :: Maybe String
  } deriving (Show, Eq)

-- | @file:line:col@, matching the shape Megaparsec already uses for parse
-- errors so both kinds of diagnostic read the same.
spanPretty :: SourceSpan -> String
spanPretty = sourcePosPretty . spanStart

-- | Re-stamp a span as having been desugared from the named construct.
desugaredSpan :: String -> SourceSpan -> SourceSpan
desugaredSpan phrase sp = sp { spanDesugaredFrom = Just phrase }

data TypeInfo = TypeInfo
  { rType :: RType
  , pType :: PType
  , chainName :: ChainName
  , tags :: [Tag]
  -- | Source provenance. 'Nothing' on every node not built by the parser --
  -- the prelude, "SPLL.Examples", and anything a pass synthesizes after
  -- parsing. Diagnostics degrade gracefully rather than requiring it.
  , srcPos :: Maybe SourceSpan} deriving (Show, Eq)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.

makeTypeInfo :: TypeInfo
makeTypeInfo = TypeInfo
    { rType = SPLL.Typing.RType.NotSetYet
    , pType = SPLL.Typing.PType.NotSetYet
    , chainName = ""
    , tags = []
    , srcPos = Nothing}

-- | Structural equivalence that ignores 'srcPos'.
--
-- 'Eq' stays derived and honest: two 'TypeInfo's from different places in the
-- source really are different values, and a pass that wants to know that can
-- still ask. But the parser tests compare a parsed 'Expr' against a constructed
-- one, or two parses of *different* source strings that should mean the same
-- thing, and for those questions position is noise. @('~=')@ is the operation
-- those tests want; on values whose 'srcPos' is 'Nothing' throughout it agrees
-- with '==' exactly.
class Equiv a where
  (~=) :: a -> a -> Bool

infix 4 ~=

instance Equiv TypeInfo where
  a ~= b = a { srcPos = Nothing } == b { srcPos = Nothing }

instance Equiv Expr where
  -- @fmap (const ())@ erases the children, so this compares the constructor and
  -- every non-recursive field; 'toList' then supplies the children in order.
  Expr a1 n1 ~= Expr a2 n2 =
    a1 ~= a2
      && fmap (const ()) n1 == fmap (const ()) n2
      && and (zipWith (~=) (toList n1) (toList n2))

instance Equiv Program where
  p1 ~= p2 =
    map fst (functions p1) == map fst (functions p2)
      && and (zipWith (~=) (map snd (functions p1)) (map snd (functions p2)))
      && neurals p1 == neurals p2
      && adts p1 == adts p2
      && writeLogitsDecls p1 == writeLogitsDecls p2
      && signatures p1 == signatures p2

instance Equiv a => Equiv [a] where
  xs ~= ys = length xs == length ys && and (zipWith (~=) xs ys)

instance (Equiv a, Equiv b) => Equiv (Either a b) where
  Left a ~= Left b = a ~= b
  Right a ~= Right b = a ~= b
  _ ~= _ = False

-- | For the common @parse x === parse y@ shape, where the left side is an
-- error string and the right side is the value of interest.
instance Equiv Char where
  (~=) = (==)


type Name = String

data Program = Program {
                    functions :: [FnDecl],
                    neurals :: [NeuralDecl],
                    adts :: [ADTDecl],
                    -- | Standalone PartitionPlan annotations, keyed by RType: either
                    -- explicit @neural writeLogits :: T of M@ declarations, or sugar registered
                    -- from a NeuralDecl's @of@ clause for its target/source type.
                    writeLogitsDecls :: [(RType, MultiValue)],
                    -- | Top-level type signatures (@f :: T@). Optional: a definition
                    -- without one is typed by inference alone. A signature is checked
                    -- against the inferred type, and is where a per-value query is
                    -- requested: an @Enumerated@ component in the codomain (task
                    -- per-value-query-over-enumerated-slot, see 'FnSignature').
                    signatures :: [FnSignature]
                    } deriving (Show, Eq)

type FnDecl = (String, Expr)

-- | One step of an accessor path into a tuple-typed codomain.
data SigStep = SigFst | SigSnd deriving (Show, Eq, Ord)

-- | A top-level type signature @name :: T@ (task
-- per-value-query-over-enumerated-slot).
--
-- 'sigType' is the declared type with every @Enumerated@ marker erased, so it
-- compares directly against the inferred 'RType'. 'sigEnumerated' lists the
-- marked slots as accessor paths into the codomain, i.e. the type under all of
-- the parameter arrows: @f :: Symbol -> (Enumerated Int, Bool)@ has the path
-- @[SigFst]@, @g :: Enumerated Int@ the empty path (the whole result).
--
-- A marked function answers a probability query with one result per value of
-- the marked slot's finite domain instead of one number -- the vector
-- @[P(slot = v, rest) | v <- domain]@. See 'SPLL.PerValue'.
data FnSignature = FnSignature
  { sigName       :: String
  , sigType       :: RType
  , sigEnumerated :: [[SigStep]]
  } deriving (Show, Eq)

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

type Value = GenericValue Expr

-- | A value set over expressions; the IR uses @GenericMultiValue IRExpr@.
type MultiValue = GenericMultiValue Expr



data Tag = DiscreteValues MultiValue
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
