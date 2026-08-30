-- | The probability-arithmetic core factored out of 'SPLL.IRCompiler' (task
-- semiring-discipline-enforcement): the 'Semiring' abstraction that lets a
-- probability be computed as either a linear value or a log-probability
-- without a second code path (see the module-level Semiring doc in
-- IRCompiler.hs for the full design rationale), and the 'PResult' combinator
-- vocabulary (design presult-combinators) IRCompiler.hs's case dispatch uses
-- instead of hand-deriving dim/branch-count/impossibility per case.
--
-- The point of this module boundary, not just the code motion: 'PResult's
-- probability field is wrapped in a newtype, 'P', whose constructor is NOT
-- exported. Every 'toIRInference' case in IRCompiler.hs -- the module that
-- caused both known instances of this bug class (the nested-IfThenElse
-- complement spelled as a literal @1 - p@, and the topK accumulator spelled
-- as a bare 'OpMult' -- see task topk-logspace-unsound) -- can therefore
-- never drop a hand-rolled 'IROp'/'IRIf' expression into a PResult's
-- probability slot. It can only go through:
--
--   * a combinator below that already routes the value through a 'Semiring'
--     operator (density/mass/detP/prodP/mixP/...), or
--   * 'unsafeLinearP', the one sanctioned escape hatch for the handful of
--     subsystems that are deliberately linear-only regardless of 'logSpace'
--     (set-witness continuous measurement, plan-guided lazy enumeration,
--     AutoNeural's decoder logit reads -- see each call site's comment), or
--   * 'sealP', for the smaller number of call sites in IRCompiler.hs that
--     build a bespoke 'PResult' shape none of the combinators fit, out of
--     values that already went through a Semiring operator or a trusted
--     variable read-back (never a hand-rolled arithmetic expression).
--
-- 'sealP' and 'unsafeLinearP' are identical in implementation and different
-- only in the claim their name makes at the call site -- deliberately kept as
-- two names rather than one, so a grep for 'unsafeLinearP' (the design's own
-- "mechanical audit" payoff) enumerates exactly the linear-only subsystems,
-- not diluted by the structural-reconstruction sites too.
module SPLL.Semiring (
  -- * The probability newtype
  P, unP, unsafeLinearP, sealP,
  -- * PResult
  PResult, rProb, rDim, rBranches, rImposs, mkPResult,
  -- * Semiring
  Semiring(..), mkSemiring, linearSemiring, logSemiring,
  negInfIR, logSumExpIR, logSubExpIR, maskSR,
  distDensity, distCumulative, scaledNormalDensity,
  -- * IR boolean/constant helpers
  const0, const1, constTrueIR, constFalseIR, notIR, orIR, andIR,
  outsideUnitInterval, anyGuardedDim,
  -- * PResult combinators
  density, mass, detP, impossibleP, indicatorP, impossibleWhen,
  prodP, onProb, onDim, onBranches, mapResult, guardP, zipResult,
  scaleCoV, anySafe, anySafeShared, enumSumP, enumSumNode, opaqueMass, shareResult,
  packResult, unpackResult, mixP, mixSubP, mixWith,
  -- * Compiler monad plumbing (generic; not Semiring-specific, but shared by
  -- combinators that bind fresh variables)
  CompilerMonad, mkVariable, setVariables, generateLetInExpr, wrapBlockIfRead
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Utils
import Control.Monad.Writer.Lazy
import qualified Data.Set as Set

type CompilerMonad a = WriterT [(String, IRExpr)] Supply a

mkVariable :: String -> CompilerMonad Varname
mkVariable suffix = do
  varID <- demandUniqueNumber
  return ("l_" ++ show varID ++ "_" ++ suffix)

setVariables :: [(String, IRExpr)] -> CompilerMonad ()
setVariables = tell

-- | A probability value known to live in whatever space (linear or log) the
-- ambient 'Semiring' picked -- see the module header. Constructor
-- deliberately not exported.
newtype P = P { unP :: IRExpr }

-- | Escape hatch for subsystems that are deliberately linear-only regardless
-- of 'logSpace' (set-witness continuous measurement, plan-guided lazy
-- enumeration, AutoNeural's decoder reads). Named distinctly from 'sealP' so
-- a grep for this name alone is the "which subsystems ignore logSpace" audit.
unsafeLinearP :: IRExpr -> P
unsafeLinearP = P

-- | Wrap an 'IRExpr' already known to be a correctly-computed probability
-- value -- built from a 'Semiring' operator, or read back from a variable
-- this module previously bound to one -- into a 'P', for the handful of
-- IRCompiler.hs call sites that build a bespoke 'PResult' none of the other
-- combinators fit. Never wrap a hand-rolled arithmetic expression in this;
-- that is exactly the mistake this module exists to make impossible.
sealP :: IRExpr -> P
sealP = P

-- | The result of compiling one expression in probability or integrate mode:
-- the probability payload plus the two bookkeeping fields that travel with
-- it. Built and combined through the combinator vocabulary below (design
-- presult-combinators) rather than by hand, so that a case body can name the
-- probability and its structural role and leave dim/branch-count implicit.
-- Constructor deliberately not exported -- see 'mkPResult'.
data PResult = PResult
  { rProb     :: P        -- ^ density / probability mass value
  , rDim      :: IRExpr   -- ^ dimensionality: 0 = discrete mass, n = n-variate density
  , rBranches :: IRExpr   -- ^ how many enumerated branches were traversed
  , rImposs   :: IRExpr   -- ^ Bool: is this result a structurally IMPOSSIBLE event?
  }

-- | The general 4-field 'PResult' constructor, for the handful of
-- IRCompiler.hs call sites whose shape doesn't fit 'density'/'mass'/'detP'/
-- etc. Requires an already-sealed 'P' for the probability field -- see
-- 'sealP'/'unsafeLinearP'.
mkPResult :: P -> IRExpr -> IRExpr -> IRExpr -> PResult
mkPResult = PResult

-- ===== IR boolean/constant helpers =====

const0 :: IRExpr
const0 = IRConst (VFloat 0)

const1 :: IRExpr
const1 = IRConst (VFloat 1)

constTrueIR :: IRExpr
constTrueIR = IRConst (VBool True)

-- Boolean IR with constant folding. The impossibility flag is 'constFalseIR'
-- for the overwhelming majority of results, and folding here keeps that
-- statically visible -- both so the flag costs nothing in the emitted code and
-- so 'mixWith' can omit a test it knows can never fire.
constFalseIR :: IRExpr
constFalseIR = IRConst (VBool False)

notIR :: IRExpr -> IRExpr
notIR e | e == constTrueIR  = constFalseIR
        | e == constFalseIR = constTrueIR
        | otherwise         = IRUnaryOp OpNot e

orIR :: IRExpr -> IRExpr -> IRExpr
orIR a b | a == constTrueIR || b == constTrueIR = constTrueIR
         | a == constFalseIR = b
         | b == constFalseIR = a
         | a == b            = a
         | otherwise         = IROp OpOr a b

andIR :: IRExpr -> IRExpr -> IRExpr
andIR a b | a == constFalseIR || b == constFalseIR = constFalseIR
          | a == constTrueIR  = b
          | b == constTrueIR  = a
          | a == b            = a
          | otherwise         = IROp OpAnd a b

-- | True when a sample falls outside the unit interval, the support of the
-- Uniform primitive.
outsideUnitInterval :: IRExpr -> IRExpr
outsideUnitInterval sample =
  orIR (IROp OpLessThan sample const0) (IROp OpGreaterThan sample const1)

-- | Dimension of a continuous leaf: 1, except under a marginal (ANY) query,
-- where the leaf contributes mass 1 and hence no dimension.
anyGuardedDim :: IRExpr -> IRExpr
anyGuardedDim sample = IRIf (IRUnaryOp OpIsAny sample) const0 const1

-- ===== Semiring =====

-- | The two probability semirings 'PResult' can be combined under (design
-- materialized-marginals-semiring Decision beta; task
-- log-space-probability-computation). Linear: (x) = *, (+) = plain add, one =
-- 1.0, zero = 0.0. Log: (x) = +, (+) = log-sum-exp, one = 0.0 (= log 1), zero
-- = negative infinity (= log 0). Only the identity elements and the two
-- combining operators differ between the two; every mode-aware PResult
-- combinator below reads them off a 'Semiring' (picked once per compiled
-- function from 'CompilerConfig' via IRCompiler.hs's 'semiringOf') instead of
-- hard-coding the linear ones, so the log-space toggle is a swap of this one
-- value rather than a second code path threaded through every case.
--
-- NOT semiring-aware (see the task's written invasiveness verdict): the
-- ReadNN/AutoNeural neural decoder's own logit-read construction, and the
-- set-witness/plan-enum continuous measurement machinery in IRCompiler.hs
-- (both build PResult leaves from their own bespoke IRExpr formulas, routed
-- through 'unsafeLinearP', not through this vocabulary). Those remain
-- linear-only under 'logSpace'.
data Semiring = Semiring
  { srLogSpace :: Bool                        -- ^ picks the IR *node* (e.g. IRDensity vs IRLogDensity), where the operator alone isn't enough
  , srZero     :: IRExpr                      -- ^ probability zero / structurally impossible
  , srOne      :: IRExpr                      -- ^ multiplicative identity
  , srTimes    :: IRExpr -> IRExpr -> IRExpr  -- ^ independent conjunction (prodP, change-of-variables scaling)
  , srPlus     :: IRExpr -> IRExpr -> IRExpr  -- ^ mixture / alternative sum (mixP)
  , srMinus    :: IRExpr -> IRExpr -> IRExpr  -- ^ AnyExcept: marginal minus one branch (mixSubP)
  , srComplement :: IRExpr -> IRExpr          -- ^ CDF flip under a decreasing transform: 1 - x linear, log(1 - exp x) log
  }

mkSemiring :: Bool -> Semiring
mkSemiring False = linearSemiring
mkSemiring True  = logSemiring

linearSemiring :: Semiring
linearSemiring = Semiring False const0 const1 (IROp OpMult) (IROp OpPlus) (IROp OpSub)
                          (IROp OpSub const1)

logSemiring :: Semiring
logSemiring = Semiring True negInfIR const0 (IROp OpPlus) logSumExpIR logSubExpIR
                       (\x -> IRUnaryOp OpLog (IROp OpSub const1 (IRUnaryOp OpExp x)))

negInfIR :: IRExpr
negInfIR = IRConst (VFloat (-1/0))

-- | log(exp a + exp b): the log-space mixture sum, stable at the -infinity
-- (impossible) boundary and without ever forming the linear sum that would
-- underflow. a/b are expected to already be cheap (let-bound) references,
-- since each is read twice; 'mixWith' arranges that.
logSumExpIR :: IRExpr -> IRExpr -> IRExpr
logSumExpIR a b =
  IRIf (IROp OpEq a negInfIR) b
  (IRIf (IROp OpEq b negInfIR) a
  (IRIf (IROp OpGreaterThan a b)
    (IROp OpPlus a (IRUnaryOp OpLog (IROp OpPlus const1 (IRUnaryOp OpExp (IROp OpSub b a)))))
    (IROp OpPlus b (IRUnaryOp OpLog (IROp OpPlus const1 (IRUnaryOp OpExp (IROp OpSub a b)))))))

-- | log(exp a - exp b), for the AnyExcept marginal-minus-one-branch case
-- (log-space sibling of 'mixSubP'/'OpSub'). Assumes b <= a, which holds
-- whenever b is genuinely one alternative folded into the marginal a.
logSubExpIR :: IRExpr -> IRExpr -> IRExpr
logSubExpIR a b =
  IRIf (IROp OpEq a negInfIR) negInfIR
  (IRIf (IROp OpEq b negInfIR) a
  (IROp OpPlus a (IRUnaryOp OpLog (IROp OpSub const1 (IRUnaryOp OpExp (IROp OpSub b a))))))

-- | An indicator-shaped semiring value: the semiring one where @cond@ holds,
-- the semiring zero otherwise. Generalizes the very common
-- @IRIf cond const1 const0@ linear 1/0 mask to either semiring.
maskSR :: Semiring -> IRExpr -> IRExpr
maskSR sr cond = IRIf cond (srOne sr) (srZero sr)

-- | The native log-pdf/log-cdf leaf for a builtin distribution when @sr@ is
-- log-space, or the ordinary linear leaf otherwise. Distinct from
-- @log (IRDensity ...)@: the latter computes the linear pdf first (which
-- underflows in a deep tail, e.g. exp(-z^2/2) for large z) and only then
-- takes the log, so precision is already lost by the time the log is taken.
-- These emit the log formula directly in each backend instead.
distDensity :: Semiring -> Distribution -> IRExpr -> IRExpr
distDensity sr d s = if srLogSpace sr then IRLogDensity d s else IRDensity d s

distCumulative :: Semiring -> Distribution -> IRExpr -> IRExpr
distCumulative sr d s = if srLogSpace sr then IRLogCumulative d s else IRCumulative d s

-- | The base normal density scaled by change-of-variables factors (division
-- by one or more positive scale terms -- sigma for PNormal, sigma*sample for
-- PLogNormal). The log form subtracts log(scaleFactor) from the native log-pdf
-- leaf instead of dividing the linear density, so a deep tail's precision
-- survives the whole formula rather than being lost to an earlier exp/log
-- round trip through the linear leaf.
scaledNormalDensity :: Semiring -> IRExpr -> [IRExpr] -> IRExpr
scaledNormalDensity sr z scaleFactors
  | srLogSpace sr = foldl (\acc s -> IROp OpSub acc (IRUnaryOp OpLog s)) (IRLogDensity IRNormal z) scaleFactors
  | otherwise     = foldl (\acc s -> IROp OpDiv acc s) (IRDensity IRNormal z) scaleFactors

-- ===== PResult combinators (design presult-combinators) =====
--
-- Every 'toIRInference' case plays one of a handful of structural roles, and the
-- role alone determines how dim and branch count combine:
--
--   product (independent conjunction)  p1*p2   d1+d2    b1+b2
--   mixture (branch / disjunction)     mixP    min-dim  caller-supplied
--   enumSum                            sum p   0        sum b
--   change-of-variables scaling        f p     unchanged
--   guard / select                     f p     f d, f b (same f)
--   leaf                               given   0 or any-guarded 1  1
--   closure / lambda (no value)        given   0        0
--
-- The combinators below are the whole algebra; cases name one instead of
-- re-deriving all three fields inline.

-- | A continuous density leaf observed at @sample@: dim 1 (ANY-guarded), one branch.
-- Never impossible: a density may be arbitrarily small (and may underflow to a
-- true float zero in a deep tail) without the event being impossible -- that
-- conflation is exactly the bug the impossibility flag exists to remove
-- (design inference-result-side-channels, task addp-zero-check-non-total).
density :: IRExpr -> IRExpr -> PResult
density p sample = PResult (P p) (anyGuardedDim sample) const1 constFalseIR

-- | A discrete probability mass / CDF value: dim 0, one branch. Possible by
-- default; leaves that KNOW when their mass vanishes use 'impossibleWhen'.
mass :: IRExpr -> PResult
mass p = PResult (P p) const0 const1 constFalseIR

-- | A result that resolves to no value of its own -- a closure, a lambda, an
-- error: dim 0, and NO branch. Zero branches is the exception, not the rule:
-- the branch-count anchor is that every terminal LEAF resolution counts 1,
-- whether it evaluates a distribution primitive or compares a
-- deterministically-known value against the sample. A deterministic leaf is
-- therefore 'mass'/'indicatorP', not this -- see the leaf-anchor note on
-- IRCompiler.hs's Var-is-a-local-variable case (task
-- bc-recursive-prob-divergence).
detP :: IRExpr -> PResult
detP p = PResult (P p) const0 const0 constFalseIR

-- | A structurally impossible event: the wrong Either arm, an empty world set,
-- a failed guard. Probability zero (semiring zero, so linear 0.0 or log
-- -infinity), and flagged as such so that a mixture drops it without having
-- to recognise the zero numerically.
impossibleP :: Semiring -> PResult
impossibleP sr = PResult (P (srZero sr)) const0 const0 constTrueIR

-- | An indicator leaf: mass 1 (semiring one) where @cond@ holds, and a flagged
-- impossibility where it does not. The flag is the structural fact the
-- indicator was built from, not a re-reading of the mass it produced.
--
-- @cond@ is deliberately NOT let-bound here, even though both fields read it
-- and it can be the largest expression around (an 'equalityGuard' embeds the
-- whole value being compared). Sharing it at emission time was measured and is
-- a pessimization: at -O2 the binding displaces a CSE that was already finding
-- the repeat and hoisting it more cheaply (+12% emitted code on
-- benchmarks/stressContinuous and stressPlanEnum), and at -O3 the tuple-arm
-- merge in 'SPLL.IROptimizer.distributeIf' reaches the same shared form without
-- it, and smaller. Pre-optimization IR does shrink ~30%, but that buys no
-- measurable compile time. See the semiring-presult-internals notes.
indicatorP :: Semiring -> IRExpr -> PResult
indicatorP sr cond = impossibleWhen (notIR cond) (mass (maskSR sr cond))

-- | Mark a result impossible exactly when @cond@ holds (accumulating onto any
-- impossibility it already carries).
--
-- Branch, don't OR: @cond@ is often precisely the test that makes evaluating
-- the result safe or even terminating -- an arm whose condition has zero
-- probability may contain the recursive call whose evaluation the zero-check
-- exists to avoid -- and IROp OpOr evaluates both sides.
impossibleWhen :: IRExpr -> PResult -> PResult
impossibleWhen cond r
  | rImposs r == constFalseIR = r { rImposs = cond }
  | rImposs r == constTrueIR  = r { rImposs = constTrueIR }
  | otherwise                 = r { rImposs = IRIf cond constTrueIR (rImposs r) }

-- | Independent conjunction: probabilities multiply, dims add, branch counts
-- add, and the conjunction is impossible if either factor is.
prodP :: Semiring -> PResult -> PResult -> PResult
prodP sr (PResult aP aDim aBC aImp) (PResult bP bDim bBC bImp) =
  PResult (P (srTimes sr (unP aP) (unP bP))) (IROp OpPlus aDim bDim) (IROp OpPlus aBC bBC) (orIR aImp bImp)
-- No Semigroup/Monoid instance: the semiring's unit (linear 'detP const1',
-- log 'detP const0') is a runtime choice, not a fixed value, so 'mempty'
-- cannot express it and 'prodP' is called explicitly with a 'Semiring'
-- instead (nothing in this module used '<>'/'mconcat' for PResult, so this
-- is not a behaviour change).

-- | Prob-only transform; dim and branch count untouched.
onProb :: (IRExpr -> IRExpr) -> PResult -> PResult
onProb f r = r { rProb = P (f (unP (rProb r))) }

onDim :: (IRExpr -> IRExpr) -> PResult -> PResult
onDim f r = r { rDim = f (rDim r) }

onBranches :: (IRExpr -> IRExpr) -> PResult -> PResult
onBranches f r = r { rBranches = f (rBranches r) }

-- | Apply the same wrapper to every field, e.g. re-binding a let-in block
-- around a whole result. @f@ must be type-preserving, since it is applied to
-- the Bool impossibility flag as well as the three numeric fields -- a guard
-- that forces the numbers to zero is 'guardP', not this.
mapResult :: (IRExpr -> IRExpr) -> PResult -> PResult
mapResult f (PResult p d bc imp) = PResult (P (f (unP p))) (f d) (f bc) (mapFlag f imp)

-- | Wrappers are applied to the flag like any other field, EXCEPT when it is
-- statically constant -- which it is for most results. Since @f@ here is
-- typically a let-in block being re-wrapped around each field, skipping the
-- constant case is what keeps the flag from costing a fourth copy of every
-- block (and the optimizer a fourth copy to fold away).
mapFlag :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
mapFlag f imp | imp == constFalseIR || imp == constTrueIR = imp
              | otherwise                                 = f imp

-- | Force a result to zero unless @cond@ holds -- the InjF applicability test,
-- the deconstructing-inverse domain guard, a world's guard conjunction. A
-- guard that fails does not merely produce zero, it establishes that this
-- branch cannot occur, so the flag is set rather than left to be re-derived
-- from the zero.
-- Guards nest rather than being conjoined with OpAnd, and each field is a
-- branch rather than an arithmetic combination, because both the guarded
-- result AND the later guards may crash when an earlier guard fails (a
-- deconstructing inverse applied to the wrong arm -- observe-partials-umbrella
-- N1b); only the branch form leaves them unevaluated.
guardP :: Semiring -> [IRExpr] -> PResult -> PResult
guardP sr conds r = PResult
  (P (nest (srZero sr) (unP (rProb r))))
  (nest const0 (rDim r))
  (nest const0 (rBranches r))
  (nest constTrueIR (rImposs r))
  where nest orElse e = foldr (\g acc -> IRIf g acc orElse) e conds

-- | Combine two results field-wise with the same operator. For the cases that
-- select between two whole results at runtime.
zipResult :: (IRExpr -> IRExpr -> IRExpr) -> PResult -> PResult -> PResult
zipResult f (PResult aP aDim aBC aImp) (PResult bP bDim bBC bImp) =
  PResult (P (f (unP aP) (unP bP))) (f aDim bDim) (f aBC bBC)
          (if aImp == bImp then aImp else f aImp bImp)

-- | The change-of-variables correction shared by every inverse-based case: in
-- probability mode multiply by |d(inverse)/d(observation)| unless the result is
-- discrete (dim 0); in cumulative mode a decreasing transform flips the CDF.
-- Reads the result's own dim, so call sites never name it.
scaleCoV :: Semiring -> Bool -> IRExpr -> PResult -> PResult
scaleCoV sr cumulative deriv r = onProb scale r
  where
    -- |deriv| is always a plain linearly-computed Jacobian factor (never
    -- itself a log-space value), so it needs its own log before 'srTimes'
    -- (log mode: OpPlus) can combine it with the log-space probability x.
    scaleFactor s = if srLogSpace sr then IRUnaryOp OpLog s else s
    scale x = if not cumulative
                then srTimes sr x (IRIf (IROp OpEq (rDim r) const0) (srOne sr) (scaleFactor (IRUnaryOp OpAbs deriv)))
                else IRIf (IROp OpGreaterThan deriv const0) x (srComplement sr x)

-- | The ANY-safe wrapper of 'toIRInferenceSave': a marginal query over this
-- expression contributes mass 1, dim 0, no branches, without evaluating the body.
anySafe :: Semiring -> IRExpr -> (IRExpr -> IRExpr) -> PResult -> PResult
anySafe sr sample wrap (PResult p d bc imp) = PResult
  (P (IRIf isAnySample (srOne sr) (wrap (unP p))))
  (IRIf isAnySample const0 (wrap d))
  (IRIf isAnySample const0 (wrap bc))
  -- A marginal query over this expression is mass 1: possible, whatever the
  -- body would have said.
  (if imp == constFalseIR then constFalseIR else IRIf isAnySample constFalseIR (wrap imp))
  where isAnySample = IRUnaryOp OpIsAny sample

-- | 'anySafe', sharing the sub-result's let-in block when more than one field
-- reads it.
--
-- 'anySafe' guards each of the four fields with its own @isAny@ test and wraps
-- each in the block ('wrapBlockIfRead'), so a block that two fields read is
-- emitted twice -- and for an enumerated sum that block holds the single most
-- expensive node in the program. 'opaqueMass' deliberately let-binds the sum
-- so the impossibility flag reads the value instead of recomputing it; the
-- per-field wrap then undoes exactly that, handing @rProb@ one copy of the
-- enumeration and @rImposs@ -- which is only @that value == srZero@ -- another.
--
-- CSE cannot merge them afterwards, and should not: the two copies sit in the
-- else-arms of two different @isAny@ ifs, so sharing them means hoisting the
-- enumeration above the guard whose whole job is to skip it on a marginal
-- (ANY) query.
--
-- Measured over the corpus at the time of writing: 33 of 247 programs
-- re-emitted such an expression, topped by @clevrEqualLargeMetalSphereNatural@
-- at 189 KB, 16% of its emitted Python -- and, being evaluated rather than
-- merely printed, twice the work at run time.
--
-- The sharing rule is 'shareResult's, for 'shareResult's reasons: bind the
-- packed result once, and project out of it only the fields that actually read
-- the block, so a statically-known dim or flag stays the constant it is
-- instead of being routed through an opaque tuple where folding cannot see it.
anySafeShared :: Semiring -> IRExpr -> [(Varname, IRExpr)] -> PResult
              -> CompilerMonad PResult
anySafeShared sr sample binds (PResult p d bc imp)
  -- Below two readers there is no duplication to remove, and the tuple is not
  -- free; 'shareResult' declines on the same test. The second condition is the
  -- one documented at 'blockIterates'.
  | length readers <= 1 || not (any (blockIterates . snd) binds) =
      return (anySafe sr sample (wrapBlockIfRead binds) (PResult p d bc imp))
  | otherwise = do
      v <- mkVariable "any_shared"
      setVariables [(v, IRIf isAnySample
                          (packMany [dflt | (_, _, dflt) <- readers])
                          (generateLetInExpr binds (packMany [e | (_, e, _) <- readers])))]
      let -- A reading field is projected out of the one shared tuple. A
          -- non-reading one keeps 'anySafe''s own guarded form and stays out of
          -- the tuple entirely, so a statically-known dim or flag remains the
          -- constant it is rather than being routed through an opaque tuple
          -- where folding cannot see it ('shareResult' makes the same split).
          field i e dflt = case lookup i (zip [j | (j, _, _) <- readers] [0 ..]) of
            Just k  -> projMany k (length readers) (IRVar v)
            Nothing -> IRIf isAnySample dflt e
      return (PResult (P (field (0 :: Int) (unP p) (srOne sr)))
                      (field 1 d  const0)
                      (field 2 bc const0)
                      (if imp == constFalseIR
                         then constFalseIR
                         else field 3 imp constFalseIR))
  where
    isAnySample = IRUnaryOp OpIsAny sample
    -- A constant-False flag reads nothing and must stay the bare constant
    -- 'anySafe' gives it, guard and all.
    reads' e    = e /= constFalseIR && mentionsAny (map fst binds) e
    -- Each field beside the value a marginal (ANY) query gives it.
    fields      = [(unP p, srOne sr), (d, const0), (bc, const0), (imp, constFalseIR)]
    readers     = [ (i, e, dflt)
                  | (i, (e, dflt)) <- zip [0 :: Int ..] fields, reads' e ]

-- | Does this block contain a loop -- a form whose body is evaluated once per
-- element of a domain?
--
-- This is the gate on sharing, and it is a statement about /run time/, not
-- size: what makes a second copy of the block cost anything is that it is a
-- second traversal. A block of constants and arithmetic folds to a handful of
-- literals, so duplicating it costs nothing and hiding it behind a tuple costs
-- something -- the pack, the projections, and the per-arm split-and-rebuild
-- the optimizer does to a tuple binding. Worse, a folded field routed through
-- an opaque tuple is hidden from constant folding, which is the pessimization
-- 'shareResult' documents.
--
-- A pre-optimization node count was tried here first and is the wrong
-- question: @testCases\/equalsCoin@ builds a block of ~100 nodes that folds to
-- four literals, so it passes any size gate while having nothing worth
-- sharing. Whether the block /iterates/ survives folding, and is exactly the
-- property that made the enumerated sums this exists for expensive.
blockIterates :: IRExpr -> Bool
blockIterates e = iterates e || any blockIterates (getIRSubExprs e)
  where
    iterates x = case x of
      IREnumSum{}                 -> True
      IRLogEnumSum{}              -> True
      IREnumSumPaired{}           -> True
      IRMap{}                     -> True
      IRBuiltin BMap _            -> True
      IRBuiltin (BReduce _ _) _   -> True
      _                           -> False

-- | Pack values into one right-nested tuple; a single value packs to itself.
-- Only the fields that read the shared block go in, so the common
-- probability-and-flag pair costs one 'IRTCons' rather than the three a full
-- 'packResult' would build and the optimizer would then split and rebuild.
packMany :: [IRExpr] -> IRExpr
packMany []     = error "packMany: nothing to pack"
packMany [x]    = x
packMany (x:xs) = IRTCons x (packMany xs)

-- | Read element @k@ of the @n@ that 'packMany' packed.
projMany :: Int -> Int -> IRExpr -> IRExpr
projMany _ 1 t = t
projMany 0 _ t = IRTFst t
projMany k n t = projMany (k - 1) (n - 1) (IRTSnd t)

-- | Sum a result over an enumerated variable's support: probabilities and branch
-- counts sum, the result is a discrete mass (dim 0). @wrap@ post-processes the
-- assembled sums (variable uniqueification at the double-enumeration site).
--
-- Takes the per-iteration result PACKED (as 'packResult' builds it), not as a
-- 'PResult'. A 'PResult' here would already be four projections off the same
-- expression, so every field this reads would carry its own full copy of the
-- body -- and the body is the recursively-compiled sub-inference, the single
-- most expensive thing in the loop. Packed, it can be bound once /inside/ the
-- loop body (a binding outside is impossible: the body reads the loop
-- variable) and every field read off that binding.
--
-- Both sums are taken in a SINGLE loop, over exactly one copy of @r@'s
-- per-iteration computation. Two single-scalar loops -- one summing 'rProb',
-- one summing 'rBranches' -- cannot share a loop body or a binding inside it,
-- so each re-embedded that computation in full; when @r@ is itself built from
-- a recursively enumerable sub-expression, that doubles the IR at every level
-- of the nesting and compounds exponentially (fuzz-qc-compiler-bugs item 3,
-- third mechanism: a plusI/negI chain over nested dice-style
-- IfThenElse-of-Uniform-threshold splits with both operands enumerable hits
-- this at every level, even with topK off).
--
-- When @countBranches@ is off the branch sum is not computed at all, and the
-- ordinary single-scalar node is used: 'rBranches' is a pure side channel with
-- no feedback into 'rProb'/'rDim'/'rImposs' anywhere in the compiler, and is
-- discarded wholesale by 'stripBranchCount' as a post-pass, so summing it
-- would be provably-unread work. When it is on, 'IREnumSumPaired' reduces a
-- @(probability, branchCount)@ body in one pass, the probability component
-- exactly as 'enumSumNode' would have. Either way this module needs no
-- knowledge of CompilerMetadata -- @countBranches@ arrives as a plain Bool.
enumSumP :: Semiring -> Bool -> (IRExpr -> IRExpr) -> Varname -> MultiValue -> IRExpr -> CompilerMonad PResult
enumSumP sr withBranchCount wrap v vals packed
  -- Only the probability is read, so the packed body is projected directly --
  -- one copy, no binding to clean up afterwards.
  | not withBranchCount =
      opaqueMass sr (wrap (enumSumNode sr v vals (unP (rProb (unpackResult packed))))) const0
  | otherwise = do
      body <- mkVariable "enum_body"
      let r = unpackResult (IRVar body)
      paired <- mkVariable "enum_paired"
      setVariables [(paired, wrap (IREnumSumPaired (srLogSpace sr) v vals
                                     (IRLetIn body packed
                                       (IRTCons (unP (rProb r)) (rBranches r)))))]
      opaqueMass sr (IRTFst (IRVar paired)) (IRTSnd (IRVar paired))

-- | The IR node an enumerated sum of probabilities is built from: 'IRLogEnumSum'
-- (log-sum-exp reduction) in log space, plain 'IREnumSum' (linear sum)
-- otherwise. Shared by 'enumSumP' and the hand-rolled double-enumeration
-- cases in IRCompiler.hs's 'toIRInference' that build an 'IREnumSum' directly
-- rather than through 'enumSumP'.
enumSumNode :: Semiring -> Varname -> MultiValue -> IRExpr -> IRExpr
enumSumNode sr = if srLogSpace sr then IRLogEnumSum else IREnumSum

-- | A discrete mass assembled by summing contributions (an enumerated support,
-- a set of plan worlds), with its branch count.
--
-- This is the one place the impossibility flag is read off the value rather
-- than taken from structure: whether ANY enumerated value contributed is not
-- expressible as a Bool over the summed body (there is no boolean IREnumSum).
-- It is sound here in a way it is not in a mixture, because this is a discrete
-- MASS -- an exact zero means no value in the support matched, i.e. the event
-- really is impossible. A density, which may underflow while remaining
-- possible, never derives its flag this way. The sum is let-bound so the test
-- reads the value instead of duplicating the whole enumeration.
opaqueMass :: Semiring -> IRExpr -> IRExpr -> CompilerMonad PResult
opaqueMass sr p bc = do
  s <- mkVariable "enum_mass"
  setVariables [(s, p)]
  return (PResult (P (IRVar s)) const0 bc (IROp OpEq (IRVar s) (srZero sr)))

-- | Bind a sub-result's let-in block ONCE, under @guards@, and hand back
-- projections off that single binding.
--
-- The alternative -- 'mapResult' (@generateLetInExpr binds@) -- re-wraps the
-- whole block around each of the four fields, so every binding the sub-result
-- floated is duplicated four times at every nesting level. That is exponential
-- in nesting depth (measured base ~3.18 per level, ~2.16 before the
-- impossibility flag existed): a 45-line program produced 200 MB of
-- pre-optimisation IR. CSE folds it all back together afterwards, so the cost
-- is entirely in what the optimizer has to traverse.
--
-- The guards must be part of the bound value rather than applied to the
-- projections, because the block becomes eager once it is bound: a guard whose
-- job is to keep a zero-probability arm from being evaluated at all (that arm
-- may hold the recursive call the guard exists to skip) only does that job from
-- inside. A failing guard yields 'impossibleP' -- zero on every numeric field,
-- flagged impossible -- which is what the guarded field-wise form produced too.
--
-- Only the fields that actually read the block are projected out of it. Dims,
-- branch counts and flags are usually statically known constants, and routing a
-- constant through an opaque tuple hides it from constant folding: doing that to
-- every field made the -O2 OUTPUT 2.7x larger even as the -O0 input shrank 400x,
-- with 'mixWith's dim comparisons left as runtime tests that used to fold away.
shareResult :: Semiring -> String -> [IRExpr] -> [(Varname, IRExpr)] -> PResult -> CompilerMonad PResult
shareResult sr tag guards binds r
  -- Sharing only pays when two or more fields would each carry a copy of the
  -- block; below two there is no duplication to remove, and the tuple is not
  -- free: packing and projecting costs assignments per arm, the failed-guard
  -- fallback is another constant tuple per guard, and routing a statically-known
  -- dim or flag through it hides that constant from folding. Sharing every
  -- result unconditionally shrank -O0 400x but grew the -O2 OUTPUT 2.7x.
  | length readers <= 1 = return (PResult
      (P (guarded (srZero sr)  (wrapIfRead (unP (rProb r)))))
      (guarded const0      (wrapIfRead (rDim r)))
      -- The branch count is deliberately not guarded: an arm that cannot occur
      -- still reports the branches it would have traversed, as before.
      (                     wrapIfRead (rBranches r))
      (guarded constTrueIR (wrapIfRead (rImposs r))))
  | otherwise = do
      v <- mkVariable tag
      let block = generateLetInExpr binds (packResult r)
      setVariables [(v, foldr (\g acc -> IRIf g acc (packResult (impossibleP sr))) block guards)]
      let proj prj e = if reads' e then prj (IRVar v) else guarded const0 e
      return (PResult
        (P (IRTFst (IRVar v)))
        (proj (IRTFst . IRTSnd) (rDim r))
        (if reads' (rBranches r) then IRTFst (IRTSnd (IRTSnd (IRVar v))) else rBranches r)
        (if reads' (rImposs r)   then IRTSnd (IRTSnd (IRTSnd (IRVar v)))
                                 else guarded constTrueIR (rImposs r)))
  where
    reads' = mentionsAny (map fst binds)
    readers = filter reads' [unP (rProb r), rDim r, rBranches r, rImposs r]
    wrapIfRead e = if reads' e then generateLetInExpr binds e else e
    -- Guards nest as IRIf, never OpOr/OpAnd -- see 'guardP'.
    guarded orElse e = foldr (\g acc -> IRIf g acc orElse) e guards

-- | Wrap a let-in block around an expression only if the expression actually
-- reads something the block binds. A 'PResult' field that does not -- a
-- statically-known dim of 0, a branch count of 0, a constant flag -- otherwise
-- drags a full copy of the block behind a value it never looks at, which for a
-- body containing an enumerated sum means a duplicate of the single most
-- expensive node in the program per field per nesting level. 'shareResult'
-- already applies this rule to its own fields; 'anySafe' takes it as its @wrap@.
wrapBlockIfRead :: [(Varname, IRExpr)] -> IRExpr -> IRExpr
wrapBlockIfRead binds e
  | mentionsAny (map fst binds) e = generateLetInExpr binds e
  | otherwise                     = e

-- | Does this expression read any of the given variables?
mentionsAny :: [Varname] -> IRExpr -> Bool
mentionsAny [] _ = False
mentionsAny names e = go e
  where
    nameSet = Set.fromList names
    go (IRVar n) = n `Set.member` nameSet
    go x = any go (getIRSubExprs x)

generateLetInExpr :: [(Varname, IRExpr)] -> IRExpr -> IRExpr
generateLetInExpr binds e = foldr (\(var, val) expr -> IRLetIn var val expr) e binds

-- | The IR encoding of a result. 'packResult' and 'unpackResult' are the only
-- places that know it -- and, since the P newtype went in, the only places
-- that cross the P/IRExpr boundary for a whole result at once.
packResult :: PResult -> IRExpr
packResult (PResult p d bc imp) = IRTCons (unP p) (IRTCons d (IRTCons bc imp))

unpackResult :: IRExpr -> PResult
unpackResult e = PResult (P (IRTFst e)) (IRTFst (IRTSnd e))
                         (IRTFst (IRTSnd (IRTSnd e))) (IRTSnd (IRTSnd (IRTSnd e)))

-- | Mixture of two alternatives (branch / disjunction): whichever side is
-- non-zero wins, ties add, and the smaller dimension wins (a discrete mass and
-- a density never sum). The branch count is supplied by the caller: no call
-- site wants a plain sum of the two operands' counts -- an 'IfThenElse' shares
-- one condition between its arms, an AnyExcept selects one arm, and a world set
-- sums over all of its worlds.
mixP :: Semiring -> IRExpr -> PResult -> PResult -> CompilerMonad PResult
mixP sr = mixWith (srPlus sr)

-- | 'mixP' for the AnyExcept case, where the excepted value's mass is
-- subtracted from the marginal rather than added.
mixSubP :: Semiring -> IRExpr -> PResult -> PResult -> CompilerMonad PResult
mixSubP sr = mixWith (srMinus sr)

-- | Shared body of 'mixP'/'mixSubP'. Both operands are let-bound first, since
-- each is read several times by the case analysis below.
--
-- Which side "wins" is decided by the operands' impossibility flags alone. It
-- used to be decided by comparing each operand's probability against zero,
-- which conflated two different facts: an impossible branch (the wrong Either
-- arm, a failed guard, an indicator that did not match) must be dropped from
-- the mixture, while a merely unlikely one must not. That conflation was wrong
-- in both directions -- 'mixSubP' used an approximate 1e-10 test, which
-- discarded legitimately tiny continuous tail densities
-- (observe-partials-umbrella N4), and even an exact test still misfires once a
-- deep-tail density underflows to a true float zero (task
-- addp-zero-check-non-total). The flag carries the fact from the guard or
-- indicator that established it, so neither float scale nor float precision
-- enters the decision.
mixWith :: (IRExpr -> IRExpr -> IRExpr) -> IRExpr -> PResult -> PResult -> CompilerMonad PResult
mixWith combine bc a b = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  setVariables [(pVarA, unP (rProb a)), (pVarB, unP (rProb b)), (dimVarA, rDim a), (dimVarB, rDim b)]
  -- A statically-possible operand needs no runtime test at all; keeping that
  -- visible here (rather than leaving it to the optimizer) is what makes the
  -- flag free in the common case where nothing is ever impossible.
  (impA, impB) <- bindFlags (rImposs a) (rImposs b)
  -- Both fields make the same case distinction: an impossible side is ignored,
  -- then the lower-dimensional side wins, and only equal dimensions combine.
  let ifPossible c whenImpossible rest = if c == constFalseIR then rest else IRIf c whenImpossible rest
  let cases whenAImp whenBImp whenALower whenBLower whenEqual =
        ifPossible impA whenAImp
        (ifPossible impB whenBImp
        (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) whenALower
        (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) whenBLower
        whenEqual)))
  return (PResult
    (P (cases (IRVar pVarB) (IRVar pVarA) (IRVar pVarA) (IRVar pVarB)
           (combine (IRVar pVarA) (IRVar pVarB))))
    (cases (IRVar dimVarB) (IRVar dimVarA) (IRVar dimVarA) (IRVar dimVarB)
           (IRVar dimVarA))
    bc
    -- The mixture is impossible only if every alternative is: an impossible
    -- side is consumed by the choice above, not propagated.
    (andIR impA impB))

-- | Let-bind the operands' impossibility flags for 'mixWith', which reads each
-- of them once per field. Statically-constant flags (the common case) are
-- passed through unbound so they keep folding the tests away.
bindFlags :: IRExpr -> IRExpr -> CompilerMonad (IRExpr, IRExpr)
bindFlags fa fb = (,) <$> bindFlag "impA" fa <*> bindFlag "impB" fb
  where
    -- Constants and plain reads are cheap and pure; binding them would only add
    -- a let for every mixture, and world folds mix once per world.
    atomic (IRConst _)  = True
    atomic (IRVar _)    = True
    atomic (IRTFst e)   = atomic e
    atomic (IRTSnd e)   = atomic e
    atomic _            = False
    bindFlag name f
      | atomic f  = return f
      | otherwise = do
          v <- mkVariable name
          setVariables [(v, f)]
          return (IRVar v)
