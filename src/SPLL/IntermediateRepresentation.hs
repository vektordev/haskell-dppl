{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module SPLL.IntermediateRepresentation (
  IRExpr(..)
, IREnv(..)
, IRFunDecl
, IRFunGroup (..)
, Tag(..)
, Operand(..)
, UnaryOperand(..)
, Builtin(..)
, ReduceOp(..)
, Shape
, Extent(..)
, builtinArity
, expectBuiltinArgs
, Distribution(..)
, Varname
, IRValue
, CompilerConfig(..)
, SemiringFamily(..)
, defaultCompilerConfig
, defaultMaterializationCardinality
, irMap
, irDescend
, irDescendM
, getIRSubExprs
, isPure
, isEffectfulVar
, isPureGiven
, lookupIREnv
, irPrintFlat
, valueToIR
, isLambda
, pattern VProbDim
, pattern VProbDimBC
, resultImpossible
, adtIdentifierRenaming
, renameADTIdentifiers
, firstAnyExceptIR
, anyExceptCodegenRefusal
) where

import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..), Shape, Extent(..), shapeNumel)
import SPLL.Typing.PType()
import SPLL.Typing.Typing()
import Data.Data()
import Data.List (isSuffixOf, sort, group)
import Data.Maybe (mapMaybe, listToMaybe)
import qualified Data.Set as Set

-- | The probability-mode result layout, as produced by 'SPLL.IRCompiler.packResult':
--
-- >  (prob, (dim, (branchCount, impossible)))    -- countBranches on
-- >  (prob, (dim, impossible))                   -- countBranches off
--
-- The impossibility flag is an internal side-channel (design
-- inference-result-side-channels): it tells a mixture which alternatives are
-- structurally inapplicable, instead of that being re-derived by comparing a
-- probability to zero. It is not stripped from the emitted result yet, so
-- consumers match through these patterns rather than on the tuple shape, which
-- is the layout's only definition outside the compiler.
pattern VProbDim :: Double -> Double -> IRValue
pattern VProbDim p d <- (probDimOf -> Just (p, d))

pattern VProbDimBC :: Double -> Double -> Double -> IRValue
pattern VProbDimBC p d bc <- (probDimBCOf -> Just (p, d, bc))

probDimOf :: IRValue -> Maybe (Double, Double)
probDimOf (VTuple (VFloat p) (VTuple (VFloat d) _)) = Just (p, d)
probDimOf _                                         = Nothing

probDimBCOf :: IRValue -> Maybe (Double, Double, Double)
probDimBCOf (VTuple (VFloat p) (VTuple (VFloat d) (VTuple (VFloat bc) _))) = Just (p, d, bc)
probDimBCOf _                                                             = Nothing

-- | The impossibility flag of a result, when the layout carries one.
resultImpossible :: IRValue -> Maybe Bool
resultImpossible (VTuple _ (VTuple _ (VBool imp)))            = Just imp
resultImpossible (VTuple _ (VTuple _ (VTuple _ (VBool imp)))) = Just imp
resultImpossible _                                            = Nothing

{-
{-# OPTIONS -Wall #-}
import Control.Monad.Cont
import Control.Monad.State.Strict


data IRExpr = IRLetIn Varname IRExpr IRExpr
            | IRLit Int
            | IRAdd IRExpr IRExpr
            | IRVar Varname
  deriving (Show)

newtype Varname = Varname String
  deriving (Show)

type M = StateT Int (Cont IRExpr)

runM :: M IRExpr -> IRExpr
runM m = runCont (runStateT m 0) fst

genName :: String -> M Varname
genName base = do
  i <- get
  let name = "$" ++ show i ++ "_" ++ base
  put (i + 1)
  return (Varname name)

letin :: String -> IRExpr -> M Varname
letin base rhs = do
  name <- genName base
  lift $ cont (\f -> IRLetIn name rhs (f name))

-- literal :: Int -> M ()
-- literal n = lift $ cont (\f -> _ f)

generateCode :: M IRExpr
generateCode = do
  varName <- letin "some_string" (IRLit 10)
  subex <- subCode varName
  return (IRAdd (IRVar varName) subex)

-- returs var + 3, using a let binding
subCode :: Varname -> M IRExpr
subCode v = do
  a <- letin "a" (IRLit 3)
  return (IRAdd (IRVar a) (IRVar v))
-}



{-
import Control.Monad.Cont
import Control.Monad.State.Strict

type Varname = String

type M a = ContT Int (State IRExpr)

--runM :: M a IRExpr -> IRExpr
runM m = evalState (runContT m return) 0

genName :: String -> M a Varname
genName base = do
  i <- get
  let name = "$" ++ show i ++ "_" ++ base
  put (i + 1)
  return name

letin :: String -> IRExpr -> M a Varname
letin base rhs = do
  name <- genName base
  ContT (\f -> IRLetIn name rhs <$> f name)
-}
--generateCode :: M a IRExpr
--generateCode = do
--  varName <- letin "some_string" (IRLit 10)
--  subex <- subCode varName
--  return (IRAdd (IRVar varName) subex)

-- returs var + 3, using a let binding
--subCode :: Varname -> M a IRExpr
--subCode v = do
--  a <- letin "a" (IRLit 3)
--  return (IRAdd (IRVar a) (IRVar v))

type Varname = String

data Operand = OpPlus
             | OpMult
             | OpGreaterThan
             | OpLessThan
             | OpDiv
             | OpSub
             | OpOr
             | OpAnd
             | OpEq
             | OpApprox
             -- Fiber-enumerator probe (task fiber-enumerator-probe-max): `max`
             -- is a forward-only binary numeric op, added purely to exercise
             -- the existing isForwardOnly enumerate-both InjF path on a second
             -- operator. Interpreter-only for now -- no Python/Julia/batched
             -- codegen case exists, since the probe's corpus test declares
             -- `backends: interpreter` only.
             | OpMax
             deriving (Show, Eq)

data UnaryOperand = OpNeg
                  | OpSign
                  | OpAbs
                  | OpNot
                  | OpExp
                  | OpLog   --Natural Logarithm
                  | OpIsAny
                  deriving (Show, Eq)

-- | The reduction operators a tensor axis can be folded with. A field of
-- 'BReduce' rather than a constructor per operator: the enum-sum family split
-- 'IREnumSum' from 'IRLogEnumSum' on exactly this axis and paid for it in
-- every generic pass.
data ReduceOp = ROpAdd        -- ^ Sum. Identity 0.
              | ROpLogSumExp  -- ^ Log-sum-exp, the log-space sibling of 'ROpAdd'. Identity -inf.
              | ROpMax        -- ^ Max (task semiring-parametric-marginals): the
                               -- reduction the max-product (MAP/tropical) semiring's
                               -- enumerated-sum sites fold with, in place of 'ROpAdd'.
                               -- Identity -inf, same as 'ROpLogSumExp' (max is
                               -- domain-agnostic: linear and log-space probabilities
                               -- compare in the same order since log is monotone).
              deriving (Show, Eq)

-- | Operations over a tensor (design ir-tensor-values). Deliberately four and
-- no more: build, map, reduce along an axis, and index along an axis by a
-- runtime key.
--
-- The /representation/ carries a full 'Shape', so the typed surface tensor of
-- tensors-in-core-language lowers onto it directly. The /operation set/ stays
-- at these four, and that restraint is a soundness matter rather than an
-- effort one (that design, §4.2): broadcasting would put one latent in every
-- element and silently drop the correlation from @p(t) = \prod p(t_i)@;
-- reducing a probabilistic axis is a convolution, which SPLL has no engine
-- for; a general linear map has a non-diagonal Jacobian that @FDecl@\'s
-- per-input scalar derivatives cannot express. 'BReduce' here is safe because
-- it reduces already-computed probabilities, not random variables.
data Builtin
  -- | @BTensor sh [e1 .. eN]@ -- build a tensor of shape @sh@ from its
  -- elements in row-major order (outermost axis first). @N@ must be
  -- @shapeNumel sh@.
  = BTensor Shape
  -- | @BMap [IRLambda v body, t]@ -- apply the lambda to every element,
  -- yielding a tensor of the same shape. The lambda is the binder; see the
  -- note on 'IRBuiltin'. Shape-preserving, so it needs no axis and no shape
  -- field of its own.
  | BMap
  -- | @BReduce op axis [t]@ -- fold @t@ along @axis@ with @op@, dropping that
  -- axis. Reducing the last axis of a rank-1 tensor yields a scalar, not a
  -- rank-0 tensor: rank 0 is not an inhabited shape.
  --
  -- Note it does /not/ take a lambda: reduce is separate from map rather than
  -- fused with it, which is the whole point -- one 'BMap' can be let-bound and
  -- reduced twice, which is the sharing 'IREnumSumPaired' exists to fake.
  | BReduce ReduceOp Int
  -- | @BIndex axis [t, key]@ -- read along @axis@ at a runtime integer key,
  -- dropping that axis (rank 1 therefore yields a scalar). Distinct from
  -- 'BListIndex', which indexes a cons-list in an O(n) walk; this is an O(1)
  -- read into a flat block.
  | BIndex Int
  -- | @BMapList [f, xs]@ -- apply @f@ to every element of a cons-list @xs@,
  -- yielding a list of the same length (design ir-reengineering, slice S2).
  -- The list-walking sibling of 'BMap': that node is shape-preserving over a
  -- static-extent tensor, this one walks an ordinary 'IRCons' spine
  -- (@mapList(f, xs)@ in both scalar backends), and the batched backend
  -- refuses it outright (no tensor shape to bucket).
  | BMapList
  -- | @BListIndex [xs, i]@ -- the @i@\'th element of a cons-list @xs@, an
  -- O(n) walk via 'elementAt' in the interpreter. Distinct from 'BIndex',
  -- which is an O(1) read into a flat tensor block; a point
  -- "SPLL.IRCompiler" relies on when arguing why materialized marginal cells
  -- are let-bound scalars rather than a table (design ir-reengineering, slice
  -- S2).
  | BListIndex
  deriving (Show, Eq)

-- | The argument count each 'Builtin' takes, or 'Nothing' for the variadic
-- 'BTensor' (whose count is its shape\'s @shapeNumel@). The single source of
-- truth for the shapes documented above; a malformed 'IRBuiltin' is a compiler
-- bug, so consumers that must have a shape use 'expectBuiltinArgs' and 'error'
-- rather than degrading.
builtinArity :: Builtin -> Maybe Int
builtinArity (BTensor _)   = Nothing
builtinArity BMap          = Just 2
builtinArity (BReduce _ _) = Just 1
builtinArity (BIndex _)    = Just 2
builtinArity BMapList      = Just 2
builtinArity BListIndex    = Just 2

-- | Check an 'IRBuiltin'\'s argument list against 'builtinArity' -- and, for
-- 'BTensor', against its shape -- failing loudly with the offending node.
expectBuiltinArgs :: Builtin -> [IRExpr] -> [IRExpr]
expectBuiltinArgs b@(BTensor sh) args
  | length args == shapeNumel sh = args
  | otherwise = error ("IRBuiltin " ++ show b ++ " needs " ++ show (shapeNumel sh)
                       ++ " elements for shape " ++ show sh ++ ", got " ++ show (length args))
expectBuiltinArgs b args = case builtinArity b of
  Nothing -> args
  Just n | length args == n -> args
         | otherwise -> error ("IRBuiltin " ++ show b ++ " expects " ++ show n
                               ++ " arguments, got " ++ show (length args)
                               ++ ": " ++ show args)

data Distribution = IRNormal | IRUniform deriving (Show, Eq)

data IRExpr = IRIf IRExpr IRExpr IRExpr
              -- | A /select/ (design pytorch-tensorizer, M1): semantically an
              -- if whose /both/ arms are evaluated and combined by a mask on the
              -- condition. Every conditional leaves 'IRCompiler' as an 'IRIf';
              -- the batched-mode select pass ('SPLL.IRSelectPass') rewrites the
              -- data-dependent, elementwise-eligible ones to 'IRSelect'. Scalar
              -- consumers lower it identically to 'IRIf' (a lazy ternary) -- the
              -- interpreter delegates and each codegen desugars it away at entry
              -- -- so today it is a behavioural no-op; a future batched backend
              -- lowers it to @torch.where@ instead. A distinct node (rather than
              -- a flag on 'IRIf') keeps if-specific optimizer rewrites from
              -- silently relabelling or mis-transforming a select.
              | IRSelect IRExpr IRExpr IRExpr
              | IROp Operand IRExpr IRExpr
              | IRUnaryOp UnaryOperand IRExpr
              | IRTheta IRExpr Int
              | IRSubtree IRExpr Int
              | IRConst IRValue
              | IRCons IRExpr IRExpr
              | IRTCons IRExpr IRExpr
              | IRHead IRExpr
              | IRTail IRExpr
              | IRTFst IRExpr
              | IRTSnd IRExpr
              | IRLeft IRExpr
              | IRRight IRExpr
              | IRFromLeft IRExpr
              | IRFromRight IRExpr
              | IRIsLeft IRExpr
              | IRIsRight IRExpr
              | IRDensity Distribution IRExpr
              | IRCumulative Distribution IRExpr
              -- | Native log-density / log-cumulative leaves for the two
              -- builtin distributions (task log-space-probability-computation).
              -- Distinct from @log (IRDensity ...)@: the latter computes the
              -- linear pdf (which underflows in a deep tail, e.g. exp(-z^2/2)
              -- for large z) and only then takes the log, so precision is
              -- already lost by the time the log is taken. These nodes let
              -- each backend emit the log-pdf/log-cdf formula directly (e.g.
              -- Normal log-pdf = -0.5*z^2 - 0.5*log(2*pi)), so a compile-time
              -- log-space mode never round-trips through a linear value that
              -- could have underflowed to zero first.
              | IRLogDensity Distribution IRExpr
              | IRLogCumulative Distribution IRExpr
              | IRSample Distribution
              | IRLetIn Varname IRExpr IRExpr
              | IRVar Varname
              | IRLambda String IRExpr
              | IRApply IRExpr IRExpr
              -- auxiliary construct to aid enumeration: bind each enumerated Value to the Varname and evaluate the subexpr. Sum results.
              -- maybe we can instead move this into some kind of standard library.
              | IREnumSum Varname MultiValue IRExpr
              -- | Log-space sibling of 'IREnumSum': sums a discrete mass over
              -- an enumerated support by log-sum-exp instead of a plain add,
              -- so a "long enumeration" (the second motivating case in the
              -- task, alongside deep products) never forms the linear sum of
              -- many small probabilities. Bound variable and body semantics
              -- otherwise mirror 'IREnumSum' exactly (same optimizer/CSE
              -- treatment, same scoping).
              | IRLogEnumSum Varname MultiValue IRExpr
              -- | Paired sibling of 'IREnumSum'/'IRLogEnumSum': ONE loop over
              -- the enumerated support whose body evaluates to a
              -- @(probability, branchCount)@ tuple, reducing the first
              -- component the way the other two nodes reduce their single
              -- scalar (log-sum-exp when the 'Bool' is True, a plain add when
              -- False) and the second component by a plain add. The result is
              -- the reduced tuple.
              --
              -- Exists because a branch-counting compile needs BOTH sums over
              -- the same body, and two single-scalar loops cannot share one
              -- loop body or a binding inside it -- so each re-embedded the
              -- whole per-iteration computation, doubling the IR at every
              -- level of a recursively-enumerable structure
              -- (fuzz-qc-compiler-bugs item 3, third mechanism). The flag is a
              -- field rather than a third constructor because only the
              -- probability component's reduction varies with 'logSpace';
              -- everything else (bound variable, scoping, optimizer and CSE
              -- treatment) is identical to 'IREnumSum'.
              | IREnumSumPaired Bool Varname MultiValue IRExpr
              | IRIsPossible MultiValue IRExpr
              -- | A named operation over a tensor (design ir-tensor-values).
              -- One constructor rather than a family:
              -- which operation, and any shape/operator/axis it is parameterised
              -- by, live in the 'Builtin' tag, so a new tensor operation costs an
              -- enum case and not another binder for every generic pass to
              -- special-case -- which is precisely how the enum-sum family
              -- grew a constructor per reduction operator.
              --
              -- Shaped as @Builtin [IRExpr]@ so a new tensor operation lands
              -- here rather than becoming another constructor family to
              -- collapse later -- exactly the demotion 'BMapList'/'BListIndex'
              -- (design ir-reengineering, slice S2) gave the former @IRMap@/
              -- @IRIndex@ constructors. Argument counts and shapes are
              -- documented per 'Builtin'; 'builtinArity' is the single place
              -- they are checked.
              --
              -- Note the map binds its variable by taking an 'IRLambda' as an
              -- argument, not by carrying a 'Varname' field. That keeps the
              -- flat argument list, at the price of the optimizer's
              -- loop-invariance analysis having to recognise a binder
              -- generically instead of by matching a constructor list.
              | IRBuiltin Builtin [IRExpr]
              | IRError String
              -- Runtime type-tag check: True iff the value of the sub-expression
              -- structurally conforms to the given RType. Emitted only as the
              -- query-type guard at a prob/integ function root (see IRCompiler),
              -- so a wrong-typed query value fails with a clear diagnostic instead
              -- of a silent bogus number or a deep "not a boolean" panic.
              | IRConformsTo RType IRExpr
              deriving (Show, Eq)

type IRValue = GenericValue IRExpr

data IREnv = IREnv [IRFunGroup] [ADTDecl] [(String, IRValue)] deriving (Show)


data IRFunGroup = IRFunGroup {groupName::String, genFun::Maybe IRFunDecl, probFun::Maybe IRFunDecl, integFun::Maybe IRFunDecl, writeLogitsFun::Maybe IRFunDecl, normalFun::Maybe IRFunDecl, groupDoc::String,
  -- | The finite enumeration of values a query against this group's prob/integ
  -- function can take, when the sample domain is statically finite -- the
  -- function's own return type, /not/ the domain of anything it enumerates
  -- internally (that is 'IREnumSum', a separate axis). 'Nothing' whenever the
  -- domain is continuous, unbounded (Int/Symbol), or not statically derivable.
  --
  -- Consumed only by the batched backend's dense-enumeration mode (design
  -- heterogeneous-batch-inference M3), which evaluates the ordinary batched
  -- kernel once with this domain /as the batch/ to get the whole probability
  -- vector. Purely additive: every other backend ignores it.
  sampleDomain::Maybe MultiValue} deriving (Show)

-- Name, Documentation, Body
type IRFunDecl = (IRExpr, String)

data CompilerConfig = CompilerConfig {
  -- If set to Just x: All branches with likelihood less than x are discarded.
  --  Uses local probability of the branch,given that the execution arrives at that branching point
  topKThreshold :: Maybe Double,
  countBranches :: Bool,
  verbose :: Int,
  optimizerLevel :: Int,
  pruneAnyChecks :: Bool,
  noIntegrate :: Bool,
  noProbability :: Bool,
  noGenerate :: Bool,
  -- When True, print every intermediate AST state during compilation (with full TypeInfo/tags)
  showIntermediates :: Bool,
  -- When True (default), the prob/integ function root is wrapped in a guard that
  -- checks the query value structurally conforms to the program's return type,
  -- failing with a clear diagnostic on a mismatch. Independent of optimizerLevel.
  -- Disable (CLI --noTypeCheck) to shave the entry check off hot compiled code.
  checkQueryType :: Bool,
  -- When True (CLI --batched), opt into batched inference mode (design
  -- pytorch-tensorizer). M1 wires only the backend-agnostic select pass, which
  -- retags data-dependent elementwise ifs to SelectIf; scalar lowering is
  -- unchanged, so today this is a behavioural no-op over the tensor fragment.
  batched :: Bool,
  -- When True (CLI --logSpace), compute probabilities in log space rather
  -- than linear space (task log-space-probability-computation, design
  -- materialized-marginals-semiring Decision beta): 'IRCompiler's PResult
  -- combinators (density/mass/prodP/mixP/enumSumP/guardP/scaleCoV/
  -- compareValueExpr) build and combine log-probabilities instead of linear
  -- ones (times becomes IROp OpPlus, mixture-sum becomes log-sum-exp, the
  -- multiplicative unit 1.0 becomes the additive unit 0.0, the zero
  -- probability becomes negative infinity), and the two builtin continuous
  -- distributions emit native log-pdf/log-cdf IR leaves ('IRLogDensity'/
  -- 'IRLogCumulative') rather than logging an already-computed linear value,
  -- so a deep tail never underflows to a hard float zero before its log is
  -- taken. Motivation: deep conjunctions and long enumerations of small
  -- probabilities underflow in linear space long before they are numerically
  -- meaningless. Scope (see the task's written invasiveness verdict): the
  -- core PResult combinators, the Uniform/Normal leaves, discrete
  -- value-equality masses ('compareValueExpr'), and enumerable-InjF sums
  -- ('enumSumP') are log-aware; 'ReadNN'/'AutoNeural' neural read-logits logit
  -- reads, the set-witness/plan-enum continuous measurement machinery, and
  -- batched mode are NOT -- they remain linear-only, so a program reaching
  -- those paths under 'logSpace' will not get the numerical-stability
  -- benefit there (and, for set-witness/plan-enum specifically, may combine
  -- a linear leaf with a log-space combinator and produce a wrong answer;
  -- no compile-time refusal guards this yet). Independent of 'batched'.
  logSpace :: Bool,
  -- When True (CLI --optStats), report optimizer telemetry on stderr: how many
  -- fixed-point iterations 'SPLL.IROptimizer.postProcess' needed per emitted
  -- function, and -- at @verbose >= 1@ -- which rewrite rule fired how many
  -- times in each of those iterations. Diagnostic only; it does not change what
  -- is compiled. Off by default so an ordinary compile stays quiet.
  optStats :: Bool,
  -- | Cardinality budget for marginal materialization (task
  -- materialization-cardinality-guard, design materialized-marginals-semiring
  -- Tier 0): the largest finite 'DiscreteValues' domain whose marginal the
  -- compiler is allowed to tabulate up front, and -- the SAME question, not a
  -- second one -- the largest operand grid it is allowed to unroll into
  -- let-bound cells, since a materialized table IS an unrolling of let-bound
  -- scalar cells rather than a runtime array (see 'SPLL.Analysis's
  -- 'materializationDomain' and IRCompiler's 'materializeOperandTable'). A
  -- domain above this falls back to today's point-query re-descent; set to 0
  -- to disable materialization entirely. Per-node, deliberately NOT a
  -- cumulative budget across nesting levels: budgeting the join is a
  -- non-compositional mechanism that is harder to reason about and to debug,
  -- and each level's unrolling is independently affordable or not. 10000 is a
  -- magic number chosen to sit far above every realistic enumerable domain
  -- (a 10-term MNIST-digit sum tops out at 91 cells and a 910-pair grid) and
  -- far below anything whose unrolling would be a compile-time disaster
  -- (set/bag-valued 2^k intermediates); it is a config field rather than a
  -- literal so the plumbing already exists if it ever needs to be
  -- user-servicable.
  materializationCardinality :: Int,
  -- | Additional per-function probability-mode variants to compile alongside
  -- the ordinary sum-product one (task semiring-parametric-marginals, design
  -- materialized-marginals-semiring Tier 1): each entry in this list adds one
  -- more 'IRFunGroup' per top-level function, named "<name>_<suffix>" (see
  -- 'SPLL.Semiring.semiringSuffix'), whose only populated slot is 'probFun',
  -- compiled with 'SPLL.Semiring.mkSemiring' fed this family instead of the
  -- default 'SRSumProduct' -- everything else ('prodP'/'mixP'/'enumSumP' and
  -- every leaf combinator built on 'SPLL.Semiring.Semiring') is unchanged, so
  -- the extra group rides the exact same compilation code the ordinary
  -- probability function does. Purely additive: '[]' (the default) changes
  -- nothing about any existing group, so every pre-existing compiled program
  -- is byte-for-byte unaffected. CLI: @--semiring=map@ (comma list of one
  -- token today; @map@ maps onto 'SRMaxProduct', the only family with a real
  -- 'SPLL.Semiring.Semiring' instance -- see 'SemiringFamily').
  --
  -- Scope: each extra family only gets a probability-mode entry point (no
  -- 'integFun'/'genFun'/'normalFun'/'writeLogitsFun') -- CDF and generation have no
  -- settled meaning under max-product (see the task's write-up), and
  -- 'topKThreshold' combined with an extra semiring is untested (topK is
  -- itself already an approximate max-plus mechanism; layering it under an
  -- *exact* 'SRMaxProduct' compile is redundant, not composed).
  extraSemirings :: [SemiringFamily]
} deriving (Show)

-- | The probability-mode semiring families 'extraSemirings' can request
-- besides the implicit default 'SRSumProduct' (task
-- semiring-parametric-marginals). Lives here, not in "SPLL.Semiring", purely
-- so 'CompilerConfig' -- itself defined in this module -- can name it in a
-- field without an import cycle; "SPLL.Semiring" re-exports it as part of the
-- same abstraction.
data SemiringFamily = SRSumProduct
                       -- ^ The default: exact probability/density. ⊗ = multiply
                       -- (linear) / add (log), ⊕ = add (linear) / log-sum-exp
                       -- (log). Never requested via 'extraSemirings' --
                       -- it is what every program already compiles with.
                     | SRMaxProduct
                       -- ^ MAP / Viterbi: the probability of the single most
                       -- likely derivation of a query value, rather than the
                       -- total over every derivation. ⊗ unchanged from
                       -- sum-product (independent factors still multiply/add);
                       -- ⊕ becomes max instead of sum/log-sum-exp. AnyExcept
                       -- (marginal-minus-one-branch) has no defined inverse
                       -- under max, so a program reaching that path under this
                       -- family is refused with a named error at compile time.
                     | SRCounting
                       -- ^ Model counting (#SAT) -- NOT implemented, and NOT
                       -- reachable via any accepted CLI/API surface ('Main.hs'
                       -- 's @--semiring=@ parser only accepts @map@;
                       -- 'SPLL.Semiring.mkSemiring' 'error's on this
                       -- constructor rather than emit a wrong answer). Kept as
                       -- a named, documented gap rather than deleted, so the
                       -- next attempt starts from the finding instead of
                       -- rediscovering it: the natural implementation --
                       -- leaves report unit weight instead of their real
                       -- probability, everything else unchanged -- is UNSOUND
                       -- under this codebase's Boolean-condition
                       -- representation. 'IfThenElse'/gt-lt/two-Normal
                       -- comparisons derive @p(cond=False)@ as
                       -- @'SPLL.Semiring.srComplement' p(cond=True)@ (@1 -
                       -- p(cond=True)@ linear) rather than compiling @cond@'s
                       -- False case separately, to avoid an O(2^depth) blowup
                       -- on nested conditions (see the comment at the
                       -- 'IfThenElse' case in IRCompiler.hs). That identity is
                       -- a probability-conservation law: it holds only because
                       -- real probabilities of an exhaustive two-way partition
                       -- sum to 1. A "count" leaf that reports unit weight
                       -- whenever its event is merely POSSIBLE breaks it --
                       -- @main = if Uniform < 0.5 then 1.0 else 2.0@ compiled
                       -- @p(cond=True)@ to the constant 1 (both branches are
                       -- possible, so both get unit weight under the natural
                       -- reading), and @srComplement 1 = 1 - 1 = 0@ then
                       -- reported the False branch -- and hence @count(2.0)@
                       -- -- as impossible: measured @0.0@ against the true
                       -- @1.0@. No 'Semiring'-level fix exists: 'srComplement'
                       -- is a plain @IRExpr -> IRExpr@ function, and the
                       -- correct False-branch weight (0 if @cond@ is
                       -- deterministically true, 1 otherwise) is not a
                       -- function of the collapsed True-branch weight alone --
                       -- it needs the *pre-collapse* probability the collapse
                       -- already discarded. A sound instance needs either a
                       -- richer 'Semiring' interface (e.g. 'srComplement'
                       -- taking the pre-collapse value alongside the collapsed
                       -- one) or accepting the O(2^depth) separate-compile
                       -- cost this identity exists to avoid -- a design
                       -- question for a follow-up task, not a mechanical fix.
                     deriving (Show, Eq, Ord)

-- | The default cardinality budget for marginal materialization. See
-- 'materializationCardinality' for what the number means and why it is 10000.
defaultMaterializationCardinality :: Int
defaultMaterializationCardinality = 10000

defaultCompilerConfig :: CompilerConfig
defaultCompilerConfig = CompilerConfig {countBranches = False, topKThreshold = Nothing, optimizerLevel = 2, verbose = 0, pruneAnyChecks = False, noIntegrate=False, noProbability=False, noGenerate=False, showIntermediates=False, checkQueryType=True, batched=False, logSpace=False, optStats=False, materializationCardinality=defaultMaterializationCardinality, extraSemirings=[]}
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.

valueToIR :: GenericValue a -> GenericValue b
valueToIR = fmap (error "Cannot convert VClosure to IR")

lookupIREnv :: String -> IREnv -> IRFunGroup
lookupIREnv name (IREnv env _ _) =
  case filter (\IRFunGroup{groupName=a} -> a == name) env of
    [] -> error ("function " ++ show name ++ "not found in environment")
    [a] -> a
    lst -> head lst

-- | The first unconsumed @VAnyExcept@ placeholder reachable from any compiled
-- function body in an 'IREnv', if any. @VAnyExcept@ ("any value other than
-- this one") is the @False@-branch witness an @==@ inverse
-- ('PredefinedFunctions.eqInv1'/'eqInv2') or an ADT constructor-test inverse
-- ('PredefinedFunctions.invIs') materialises during inference; it is a
-- symbolic set, not a runtime value. The optimizer normally consumes it before
-- codegen, but where it survives, neither scalar text backend has anywhere to
-- put it: unlike @VAny@/@AnyList@, which both render as real sentinel values,
-- a set has no runtime representation to lower to, so there is no correct
-- string to emit -- only a refusal (task
-- @vanyexcept-unrenderable-in-text-backends@).
firstAnyExceptIR :: IREnv -> Maybe IRExpr
firstAnyExceptIR (IREnv groups _ _) =
  listToMaybe (filter isAnyExceptConst (concatMap allSubExprsOf funBodies))
  where
    funBodies = concatMap groupBodies groups
    groupBodies IRFunGroup{genFun=g, probFun=p, integFun=i, writeLogitsFun=e, normalFun=n} =
      map fst (mapMaybe id [g, p, i, e, n])
    allSubExprsOf ir = ir : concatMap allSubExprsOf (getIRSubExprs ir)
    isAnyExceptConst (IRConst (VAnyExcept _)) = True
    isAnyExceptConst _ = False

-- | Refuse to compile to a scalar text backend (Python or Julia) if a
-- @VAnyExcept@ placeholder survived to codegen, naming the construct rather
-- than letting 'SPLL.CodeGenPyTorch.pyVal'/'SPLL.CodeGenJulia.juliaVal' fall
-- through to their generic "unknown value" panic -- which named an internal
-- IR variable and a source line, not the actual defect. The interpreter is
-- unaffected: it answers these programs directly (its 'VAnyExcept' handling
-- predates this refusal), and that answer is the reference this diagnostic
-- points readers at. The batched backend needs no equivalent call: it already
-- refuses every marginal-query construct, 'VAnyExcept' included, through its
-- own @emittable@/@reason@ guard.
anyExceptCodegenRefusal :: String -> IREnv -> Either CompilerError ()
anyExceptCodegenRefusal lang env = case firstAnyExceptIR env of
  Nothing -> Right ()
  Just ir -> Left $ unlines
    [ lang ++ " codegen cannot render a VAnyExcept placeholder: " ++ show ir
    , "VAnyExcept (\"any value other than this one\") is the False-branch witness"
    , "an == inverse or ADT constructor-test inverse materialises during"
    , "inference. It is a symbolic set, not a runtime value -- unlike"
    , "VAny/AnyList, which both render as real sentinels in the " ++ lang
    , "runtime library, a set has no runtime representation to lower to, so"
    , "there is no correct output to emit. NeST refuses at compile time rather"
    , "than crash inside codegen."
    , "The interpreter answers this program directly; this backend does not."
    , "(task vanyexcept-unrenderable-in-text-backends)" ]

getIRSubExprs :: IRExpr -> [IRExpr]
getIRSubExprs (IRIf a b c) = [a, b, c]
getIRSubExprs (IRSelect a b c) = [a, b, c]
getIRSubExprs (IROp _ a b) = [a, b]
getIRSubExprs (IRUnaryOp _ a) = [a]
getIRSubExprs (IRTheta a _) = [a]
getIRSubExprs (IRSubtree a _) = [a]
getIRSubExprs (IRConst _) = []
getIRSubExprs (IRCons a b) = [a, b]
getIRSubExprs (IRTCons a b) = [a, b]
getIRSubExprs (IRHead a) = [a]
getIRSubExprs (IRTail a) = [a]
getIRSubExprs (IRTFst a) = [a]
getIRSubExprs (IRTSnd a) = [a]
getIRSubExprs (IRLeft a) = [a]
getIRSubExprs (IRRight a) = [a]
getIRSubExprs (IRFromLeft a) = [a]
getIRSubExprs (IRFromRight a) = [a]
getIRSubExprs (IRIsLeft a) = [a]
getIRSubExprs (IRIsRight a) = [a]
getIRSubExprs (IRIsPossible _ a) = [a]
getIRSubExprs (IRDensity _ a) = [a]
getIRSubExprs (IRCumulative _ a) = [a]
getIRSubExprs (IRLogDensity _ a) = [a]
getIRSubExprs (IRLogCumulative _ a) = [a]
getIRSubExprs (IRSample _) = []
getIRSubExprs (IRLetIn _ a b) = [a, b]
getIRSubExprs (IRVar _) = []
getIRSubExprs (IRLambda _ a) = [a]
getIRSubExprs (IRApply a b) = [a, b]
getIRSubExprs (IREnumSum _ _ a) = [a]
getIRSubExprs (IRLogEnumSum _ _ a) = [a]
getIRSubExprs (IREnumSumPaired _ _ _ a) = [a]
getIRSubExprs (IRBuiltin _ args) = args
getIRSubExprs (IRError _) = []
getIRSubExprs (IRConformsTo _ a) = [a]

-- | True if an @IRVar name@ reference is *effectful* -- i.e. a reference to a
-- top-level generator function, whose evaluation draws randomness. The IR uses
-- @IRVar@ for two semantically different things: a pure value reference (a
-- lambda parameter, let binding, or enumSum loop variable, free to duplicate)
-- and a nullary generator call such as @coin_gen@. \"Referencing\" the latter
-- actually /runs the sampler/: the interpreter re-evaluates the bound expression
-- on every lookup and code generation renders it as a call, so duplicating the
-- reference duplicates the random draw (task ir-effectful-var-purity).
--
-- Generator references are recognised by the @_gen@ name suffix that
-- 'SPLL.IRCompiler' appends to every inference-carrying top-level declaration
-- (this also covers neural @_auto_gen@). A @_gen@ reference that names a
-- /function/ rather than a nullary sampler is itself a pure closure value, but
-- treating it conservatively as effectful only ever forgoes an optimization --
-- it never changes semantics -- so this predicate does not try to tell them
-- apart.
isEffectfulVar :: String -> Bool
isEffectfulVar name = "_gen" `isSuffixOf` name

-- | True if evaluating the expression has no observable side effect, so it is
-- safe both to duplicate (inline into several uses) and to collapse repeated
-- occurrences into one shared binding. The two effects are drawing a random
-- sample ('IRSample') and referencing a generator function ('isEffectfulVar').
--
-- This is the single mechanism every duplicating or sharing optimizer rewrite
-- consults, replacing the ad-hoc per-pass assumptions this class of bug used to
-- rely on: @optimizeLetIns@' \"never duplicate a non-'IRConst' binding\" and
-- CSE's \"a subexpression is pure iff it contains no 'IRSample'\" -- the latter
-- silently misclassified an expression built from a generator reference as
-- pure and could collapse two independent draws into one (task
-- ir-effectful-var-purity).
isPure :: IRExpr -> Bool
isPure = isPureGiven Set.empty

-- | 'isPure' relative to a set of generator names already /proven/ deterministic
-- by whole-program analysis (see 'SPLL.IROptimizer.deterministicGens').
--
-- 'isEffectfulVar' is a name test, so it calls every @_gen@ reference effectful.
-- That is safe but blunt: a generate function that draws no randomness -- an
-- accessor, a comparison, an arithmetic helper -- is a pure call, and refusing
-- to share it blocks CSE on every expression that mentions one. In an
-- enumerated inference body, which is written almost entirely in terms of such
-- calls, that means the enumeration itself is never recognised as a repeat and
-- gets evaluated once per occurrence.
isPureGiven :: Set.Set Varname -> IRExpr -> Bool
isPureGiven _   (IRSample _) = False
isPureGiven det (IRVar name) = not (isEffectfulVar name) || Set.member name det
isPureGiven det e            = all (isPureGiven det) (getIRSubExprs e)

irMap :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irMap f x = f (irDescend (irMap f) x)

-- | Apply @f@ to the immediate children of a node, rebuilding it. One level
-- only -- unlike 'irMap' it does not recurse, so the caller controls the
-- traversal. This is what a scope-aware rewrite needs: it can handle the
-- binding forms itself (threading an environment through 'IRLetIn'/'IRLambda'/
-- 'IREnumSum' scopes) and delegate every other constructor here, instead of
-- re-listing the whole 35-constructor AST.
irDescend :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irDescend f x = case x of
  (IRIf cond left right) -> IRIf (f cond) (f left) (f right)
  (IRSelect cond left right) -> IRSelect (f cond) (f left) (f right)
  (IROp op left right) -> IROp op (f left) (f right)
  (IRUnaryOp op expr) -> IRUnaryOp op (f expr)
  (IRCons left right) -> IRCons (f left) (f right)
  (IRTCons left right) -> IRTCons (f left) (f right)
  (IRHead expr) -> IRHead (f expr)
  (IRTail expr) -> IRTail (f expr)
  (IRTFst expr) -> IRTFst (f expr)
  (IRTSnd expr) -> IRTSnd (f expr)
  (IRLeft expr) -> IRLeft (f expr)
  (IRRight expr) -> IRRight (f expr)
  (IRFromLeft expr) -> IRFromLeft (f expr)
  (IRFromRight expr) -> IRFromRight (f expr)
  (IRIsLeft expr) -> IRIsLeft (f expr)
  (IRIsRight expr) -> IRIsRight (f expr)
  (IRIsPossible val expr) -> IRIsPossible val (f expr)
  (IRDensity a expr) -> IRDensity a (f expr)
  (IRCumulative a expr) -> IRCumulative a (f expr)
  (IRLogDensity a expr) -> IRLogDensity a (f expr)
  (IRLogCumulative a expr) -> IRLogCumulative a (f expr)
  (IRLetIn name left right) -> IRLetIn name (f left) (f right)
  (IRLambda name scope) -> IRLambda name (f scope)
  (IRApply a b) -> IRApply (f a) (f b)
  (IREnumSum name val scope) -> IREnumSum name val (f scope)
  (IRLogEnumSum name val scope) -> IRLogEnumSum name val (f scope)
  (IREnumSumPaired lg name val scope) -> IREnumSumPaired lg name val (f scope)
  (IRBuiltin b args) -> IRBuiltin b (map f args)
  (IRTheta a i) -> IRTheta (f a) i
  (IRSubtree a i) -> IRSubtree (f a) i
  (IRConst _) -> x
  (IRSample _) -> x
  (IRVar _) -> x
  (IRError _) -> x
  (IRConformsTo t a) -> IRConformsTo t (f a)

-- | Monadic 'irDescend': rebuild a node from effectfully-rewritten children,
-- one level only. Children are visited left-to-right, so an effect that
-- threads state (a fresh-name counter, a collected list of hoisted bindings)
-- sees them in source order. Like 'irDescend' it does /not/ recurse — the
-- caller drives the traversal and can handle binding forms itself.
irDescendM :: Monad m => (IRExpr -> m IRExpr) -> IRExpr -> m IRExpr
irDescendM f x = case x of
  (IRIf cond left right) -> IRIf <$> f cond <*> f left <*> f right
  (IRSelect cond left right) -> IRSelect <$> f cond <*> f left <*> f right
  (IROp op left right) -> IROp op <$> f left <*> f right
  (IRUnaryOp op expr) -> IRUnaryOp op <$> f expr
  (IRCons left right) -> IRCons <$> f left <*> f right
  (IRTCons left right) -> IRTCons <$> f left <*> f right
  (IRHead expr) -> IRHead <$> f expr
  (IRTail expr) -> IRTail <$> f expr
  (IRTFst expr) -> IRTFst <$> f expr
  (IRTSnd expr) -> IRTSnd <$> f expr
  (IRLeft expr) -> IRLeft <$> f expr
  (IRRight expr) -> IRRight <$> f expr
  (IRFromLeft expr) -> IRFromLeft <$> f expr
  (IRFromRight expr) -> IRFromRight <$> f expr
  (IRIsLeft expr) -> IRIsLeft <$> f expr
  (IRIsRight expr) -> IRIsRight <$> f expr
  (IRIsPossible val expr) -> IRIsPossible val <$> f expr
  (IRDensity a expr) -> IRDensity a <$> f expr
  (IRCumulative a expr) -> IRCumulative a <$> f expr
  (IRLogDensity a expr) -> IRLogDensity a <$> f expr
  (IRLogCumulative a expr) -> IRLogCumulative a <$> f expr
  (IRLetIn name left right) -> IRLetIn name <$> f left <*> f right
  (IRLambda name scope) -> IRLambda name <$> f scope
  (IRApply a b) -> IRApply <$> f a <*> f b
  (IREnumSum name val scope) -> IREnumSum name val <$> f scope
  (IRLogEnumSum name val scope) -> IRLogEnumSum name val <$> f scope
  (IREnumSumPaired lg name val scope) -> IREnumSumPaired lg name val <$> f scope
  (IRBuiltin b args) -> IRBuiltin b <$> mapM f args
  (IRTheta a i) -> flip IRTheta i <$> f a
  (IRSubtree a i) -> flip IRSubtree i <$> f a
  (IRConst _) -> pure x
  (IRSample _) -> pure x
  (IRVar _) -> pure x
  (IRError _) -> pure x
  (IRConformsTo t a) -> IRConformsTo t <$> f a

isLambda :: IRExpr -> Bool
isLambda IRLambda {} = True
isLambda _ = False

irPrintFlat :: IRExpr -> String
irPrintFlat (IRIf _ _ _) = "IRIf"
irPrintFlat (IRSelect _ _ _) = "IRSelect"
irPrintFlat (IROp _ _ _) = "IROp"
irPrintFlat (IRUnaryOp _ _) = "IRUnaryOp"
irPrintFlat (IRTheta _ _) = "IRTheta"
irPrintFlat (IRSubtree _ _) = "IRSubtree"
irPrintFlat (IRConst _) = "IRConst"
irPrintFlat (IRCons _ _) = "IRCons"
irPrintFlat (IRTCons _ _) = "IRTCons"
irPrintFlat (IRHead _) = "IRHead"
irPrintFlat (IRTail _) = "IRTail"
irPrintFlat (IRTFst _) = "IRTFst"
irPrintFlat (IRTSnd _) = "IRTSnd"
irPrintFlat (IRLeft _) = "IRLeft"
irPrintFlat (IRRight _) = "IRRight"
irPrintFlat (IRFromLeft _) = "IRFromLeft"
irPrintFlat (IRFromRight _) = "IRFromRight"
irPrintFlat (IRIsLeft _) = "IRIsLeft"
irPrintFlat (IRIsRight _) = "IRIsRight"
irPrintFlat (IRIsPossible _ _) = "IRIsPossible"
irPrintFlat (IRDensity _ _) = "IRDensity"
irPrintFlat (IRCumulative _ _) = "IRCumulative"
irPrintFlat (IRLogDensity _ _) = "IRLogDensity"
irPrintFlat (IRLogCumulative _ _) = "IRLogCumulative"
irPrintFlat (IRLogEnumSum _ _ _) = "IRLogEnumSum"
irPrintFlat (IRSample _) = "IRSample"
irPrintFlat (IRLetIn _ _ _) = "IRLetIn"
irPrintFlat (IRVar _) = "IRVar"
irPrintFlat (IRLambda _ _) = "IRLambda"
irPrintFlat (IRApply _ _) = "IRApply"
irPrintFlat (IREnumSum _ _ _) = "IREnumSum"
irPrintFlat (IREnumSumPaired _ _ _ _) = "IREnumSumPaired"
irPrintFlat (IRBuiltin b _) = "IRBuiltin " ++ show b
irPrintFlat (IRError _) = "IRError"
irPrintFlat (IRConformsTo _ _) = "IRConformsTo"


-- ----------------------------------------------------------------------------
-- Target-language identifier hygiene for ADT names
--
-- ADT constructor and field names reach the emitted Python/Julia verbatim, as
-- class/struct names, accessor function names, and every reference to them in
-- the compiled expressions. A source name that happens to be a keyword of the
-- target language then produces code that does not compile -- @data Opt = None
-- | Some w::Float@ emitted @class None:@ (a Python SyntaxError), and a field
-- named @end@ emitted a Julia @struct@ that closed two lines early and was
-- silently mis-parsed (task codegen-adt-name-collides-with-target-keyword).
--
-- The fix is to mangle rather than to reject: SPLL is the source language, and
-- whether a program is legal must not depend on which backend it is aimed at.
-- Mangling happens once, over the whole 'IREnv', before any emission -- not at
-- the individual emission sites. That matters because the *same* name appears
-- both as a definition (@class None:@) and as a reference carried in the IR
-- (@IRVar "None"@, @IRVar "isNone"@, @IRVar "w"@); renaming the environment
-- keeps the two halves in step by construction, whereas per-site mangling
-- would have to be repeated at every one of the ~20 places a name is printed
-- and would silently desynchronise the moment one was missed.
--
-- Only ADT-derived names are renamed. Local binders and compiler-generated
-- temporaries are deliberately left alone: they are never ADT names, and
-- renaming references without also renaming their binders is exactly the
-- desynchronisation this pass exists to avoid.
-- ----------------------------------------------------------------------------

-- | Every identifier an ADT declaration contributes to the emitted code,
-- paired with what @mangle@ turns it into -- but only where the two differ,
-- so a program with no colliding name produces an empty renaming and emitted
-- code identical to before.
--
-- Three families per constructor: the constructor itself (a class/struct name
-- and a callable), its @is\<Ctor\>@ predicate, and its field accessors. The
-- predicate is derived from the *mangled* constructor name, matching how the
-- backends spell it (@"is" ++ name@ over the already-renamed declaration), so
-- @None@ becoming @None_@ takes @isNone@ to @isNone_@.
--
-- Field names are global across a program (accessor lookup in
-- 'SPLL.Typing.AlgebraicDataTypes.findField' searches every declaration), so a
-- flat association list is the right shape.
--
-- This is also the only place with enough context to catch a mangling
-- /collision/. Each @mangle@ sees one name at a time -- which is what lets
-- 'SPLL.CodeGenPyTorch.pyVal' mangle a query point that never passed through
-- this pass -- so it cannot know that a field named @isNone_@ lands on the same
-- emitted name as constructor @None@'s derived predicate. Here the whole
-- declaration set is in scope, so two distinct source identifiers sharing one
-- emitted name is a refusal rather than two definitions of which the second
-- silently wins.
adtIdentifierRenaming :: (String -> String) -> [ADTDecl] -> [(String, String)]
adtIdentifierRenaming mangle decls
  | not (null introduced) = error (mangleCollisionMessage introduced)
  | otherwise             = [ (from, to) | (from, to) <- allPairs, from /= to ]
  where
    allPairs =
      [ pair
      | decl <- decls
      , (cName, fields) <- constructors decl
      , pair <- (cName, mangle cName)
              : ("is" ++ cName, "is" ++ mangle cName)
              : [ (fName, mangle fName) | (fName, _) <- fields ]
      ]
    -- Collisions that mangling *introduced*: two identifiers the user kept
    -- apart that land on one emitted name. Distinct sources sharing an emitted
    -- name is exactly that, so the test needs nothing more.
    --
    -- A name that was already duplicated before mangling (two ADTs sharing a
    -- constructor or field name) collapses to a single source here and is
    -- deliberately not reported: it is a pre-existing ambiguity in accessor
    -- lookup, and failing on it would reject programs that compile today.
    introduced =
      [ (sources, to)
      | to <- dedup (map snd allPairs)
      , let sources = dedup [ from | (from, to') <- allPairs, to' == to ]
      , length sources > 1
      ]
    dedup = map head . group . sort

-- | Raised when mangling maps two distinct ADT identifiers onto one emitted
-- name -- the residue 'SPLL.CodeGenPyTorch.pyMangle' cannot see on its own,
-- since it only ever looks at one name. Left as an 'error': the two scalar
-- backends have no error channel at this point, and a loud refusal is strictly
-- better than what the collision otherwise produces, which is two definitions
-- of the same name where the second silently shadows the first.
mangleCollisionMessage :: [([String], String)] -> String
mangleCollisionMessage clashes = unlines
  ( "Target-language name mangling collided. These ADT identifiers are distinct \
    \in the program but would be emitted under one name:"
  : [ "  " ++ show sources ++ " all become " ++ show to | (sources, to) <- clashes ]
 ++ ["Rename one of them in the `data` declaration."] )

-- | Apply an 'adtIdentifierRenaming' to every 'IRVar' reference in every
-- compiled function body.
--
-- The 'ADTDecl's are deliberately left alone, so they keep the names the user
-- wrote. The declarations are printed by exactly one function per backend
-- (@generateADTClass@), which applies @mangle@ itself at each identifier it
-- emits -- and can therefore still spell the *source* constructor name into
-- 'SPLL.Typing.AlgebraicDataTypes.anyCtorTestMessage', which all three backends
-- and the interpreter must agree on word for word (task
-- is-ctor-on-any-slot-diverges-across-backends). Renaming the declaration would
-- have made Python say @isNone_@ where the interpreter says @isNone@, quietly
-- undoing that agreement for precisely the programs this pass exists for.
--
-- The definition and reference halves stay in step because both go through the
-- same @mangle@, which is a pure function of the name: neither side needs to
-- know what the other did.
--
-- Constants and 'IRConst' values are likewise not rewritten. A @VADT@ reaches
-- the output through the backend's value renderer ('pyVal', 'juliaVal'), which
-- mangles there -- including for query points fed in by the test harness and
-- the CLI, which never pass through this pass at all.
renameADTIdentifiers :: (String -> String) -> IREnv -> IREnv
renameADTIdentifiers mangle env@(IREnv groups decls consts)
  | null renaming = env
  | otherwise     = IREnv (map onGroup groups) decls consts
  where
    renaming = adtIdentifierRenaming mangle decls
    rename n = maybe n id (lookup n renaming)
    onGroup g = g
      { genFun    = fmap onBody (genFun g)
      , probFun   = fmap onBody (probFun g)
      , integFun  = fmap onBody (integFun g)
      , writeLogitsFun = fmap onBody (writeLogitsFun g)
      , normalFun = fmap onBody (normalFun g)
      }
    onBody (body, doc) = (irMap onVar body, doc)
    onVar (IRVar n) = IRVar (rename n)
    onVar e         = e
