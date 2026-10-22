{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving #-}
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
--   * 'unsafeLinearP', the one sanctioned escape hatch for a subsystem that
--     is deliberately linear-only regardless of 'logSpace' (none uses it
--     today -- see its own comment), or
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
  Semiring(..), mkSemiring, linearSemiring, logSemiring, semiringGroupInfix,
  maxLinearSemiring, maxLogSemiring,
  semiringSuffix,
  negInfIR, logSumExpIR, logSubExpIR, maskSR, fromLinearSR, toLinearSR, measureDiffSR, sumAllSR,
  distDensity, distCumulative, scaledNormalDensity, upperTailComplement, complementWhen,
  -- * IR boolean/constant helpers
  const0, const1, dim0, dim1, constTrueIR, constFalseIR, notIR, orIR, andIR,
  outsideUnitInterval, anyGuardedDim,
  -- * PResult combinators
  density, mass, detP, impossibleP, indicatorP, impossibleWhen,
  prodP, onProb, onDim, onBranches, underLambdas, substResult, errorWhen, constantResult, guardP, zipResult, zip3Result,
  scaleCoV, scaleCoVAtom, anySafe, anySafeShared, enumSumP, enumMixP, enumSumNode, tensorDomainSR, opaqueMass, closeResult, guardedResult, shareUnlessLeaf,
  packResult, unpackResult, packedProb, mixP, mixSubP, mixWith,
  -- * Compiler monad plumbing (generic; not Semiring-specific, but shared by
  -- combinators that bind fresh variables)
  CompilerMonad, CompilerM, refuse, runCompilerMonad, mkVariable, setVariables, generateLetInExpr,
  -- * Scopes
  Open, scoped, openWith, openValue, closeExpr, inline, splitOpen, openNames, openReads, openIterates, openNests,
  openIsEmpty, openBlockSize, unsafeDistributeBlock
) where

import SPLL.IntermediateRepresentation
import SPLL.ReservedNames (sumProductGroupTag, maxProductGroupTag, countingGroupTag)
import SPLL.Lang.Types
import SPLL.Lang.Lang (multiValueToValueList)
import Utils
import Control.Monad.Writer.Lazy (WriterT, runWriterT, tell, lift)
import Control.Monad.State (MonadState)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import qualified Data.Set as Set

-- | The compiler monad: fresh names ('Supply'), emitted let-bindings (a
-- writer), and one refusal channel (task static-refusals-become-absent-variants).
--
-- A newtype, so that its writer is NOT reachable from outside this module
-- (design presult-blocks-shared-by-construction). A sub-compile that wants its
-- own bindings runs under 'scoped' and gets an 'Open' back, whose bindings can
-- only leave through the functions below; no caller can hold a scope's
-- bindings as a list and wrap them around each field of a 'PResult' -- the
-- one move behind most of this compiler's exponential compile times (see
-- 'unpackResult').
--
-- The 'ExceptT' sits /under/ the writer on purpose: a refusal inside a scope
-- propagates through 'scoped' untouched, and the name supply, beneath both, is
-- never rewound by a refusal. The supply ('MonadState' 'Int') and the refusal
-- channel ('MonadError') are exported; neither can move a binding.
newtype CompilerM a = CompilerM (WriterT [(String, IRExpr)] (ExceptT VariantRefusal Supply) a)
  deriving newtype (Functor, Applicative, Monad, MonadState Int, MonadError VariantRefusal)
type CompilerMonad a = CompilerM a

unCompilerM :: CompilerM a -> WriterT [(String, IRExpr)] (ExceptT VariantRefusal Supply) a
unCompilerM (CompilerM m) = m

-- | Decline to compile the current variant: an unsupported shape, not an
-- internal invariant (those stay 'error'). The whole variant becomes absent
-- with this reason recorded on its 'IRFunGroup'; see 'VariantRefusal'. The first
-- argument is the chain name of the refusing node ("" when there is none).
refuse :: String -> String -> CompilerMonad a
refuse cn why = throwError (VariantRefusal why cn)

-- | Run a compilation from a fresh name supply. The top-level bindings come
-- back as an 'Open', closed by the caller like any other scope.
runCompilerMonad :: CompilerMonad a -> Either VariantRefusal (Open a)
runCompilerMonad m = uncurry Open <$> evalSupply (runExceptT (runWriterT (unCompilerM m)))

mkVariable :: String -> CompilerMonad Varname
mkVariable suffix = do
  varID <- demandUniqueNumber
  return ("l_" ++ show varID ++ "_" ++ suffix)

-- | Emit let-bindings into the current scope.
setVariables :: [(String, IRExpr)] -> CompilerMonad ()
setVariables = CompilerM . tell

-- ===== Scopes =====

-- | A value together with the let-bindings its scope emitted ('scoped'). The
-- value may read those bindings, so it is only meaningful under them.
--
-- The constructor and the bindings are NOT exported (design
-- presult-blocks-shared-by-construction). The ways out each put the block in
-- one place:
--
--   * 'closeExpr': around one expression built from the value (a lambda or
--     loop body, a packed result);
--   * 'closeResult' (and its variants 'guardedResult', 'shareUnlessLeaf',
--     'anySafeShared'): back into a 'PResult', bound once and projected,
--     inline when at most one field reads it;
--   * 'inline': re-emitted into the enclosing scope;
--   * 'unsafeDistributeBlock': the named escape hatch that copies the block
--     into each reading field, for a block that cannot compound.
--
-- 'openValue' drops the bindings: for a scope run only for its structure
-- (a probe), whose value's variables then name nothing.
data Open a = Open a [(Varname, IRExpr)]

instance Functor Open where
  fmap f (Open a binds) = Open (f a) binds

-- | Scopes combine by concatenating their blocks, left first: @(,) <$> a <*>
-- b@ is the scope that emits @a@'s bindings, then @b@'s.
instance Applicative Open where
  pure a = Open a []
  Open f fb <*> Open a ab = Open (f a) (fb ++ ab)

-- | Run a sub-compile in its own scope: its bindings are captured instead of
-- emitted.
scoped :: CompilerM a -> CompilerM (Open a)
scoped (CompilerM m) = CompilerM (lift (uncurry Open <$> runWriterT m))

-- | A scope built from bindings already in hand: @openWith binds a@ is
-- @scoped (setVariables binds >> return a)@.
openWith :: [(Varname, IRExpr)] -> a -> Open a
openWith binds a = Open a binds

-- | The value without its bindings. Only for a scope run to inspect its
-- result's structure: the value's variables name bindings that are dropped.
openValue :: Open a -> a
openValue (Open a _) = a

-- | Wrap the block around ONE expression built from the value: one copy.
closeExpr :: Open a -> (a -> IRExpr) -> IRExpr
closeExpr (Open a binds) f = generateLetInExpr binds (f a)

-- | Re-emit the scope's bindings into the enclosing scope and return the
-- value. This makes them eager there, so it is only for scopes opened to
-- inspect (a trial compile kept, a size measured) -- never for one opened to
-- keep a guarded arm lazy, whose guard exists to skip what the block computes
-- (a recursive call, a deconstructing inverse on the wrong arm). Guarded
-- sites close through 'closeResult', which puts the guards into the bound
-- value.
inline :: Open a -> CompilerM a
inline (Open a binds) = setVariables binds >> return a

-- | Split a scope's block in two by a partition of its bindings: the first
-- part as a scope of its own (to be emitted with 'inline', e.g. bindings
-- hoisted out of a loop or a guard), the rest still holding the value. The
-- partition must return a split of its argument (each binding exactly once),
-- order kept.
splitOpen :: ([(Varname, IRExpr)] -> ([(Varname, IRExpr)], [(Varname, IRExpr)]))
          -> Open a -> (Open (), Open a)
splitOpen part (Open a binds) = let (out, stay) = part binds in (Open () out, Open a stay)

-- | The names the scope binds (no values: a name alone copies nothing).
openNames :: Open a -> [Varname]
openNames (Open _ binds) = map fst binds

-- | Does this expression read a binding of the scope?
openReads :: Open a -> IRExpr -> Bool
openReads (Open _ binds) = mentionsAny (map fst binds)

-- | Does the block hold a loop or a call ('blockIterates')?
openIterates :: Open a -> Bool
openIterates (Open _ binds) = any (blockIterates . snd) binds

-- | Would copying the block per field compound ('blockNests')?
openNests :: Open a -> Bool
openNests (Open _ binds) = any (blockNests . snd) binds

-- | Did the scope emit no bindings?
openIsEmpty :: Open a -> Bool
openIsEmpty (Open _ binds) = null binds

-- | The sum of a measure over the block's bound values (a size budget).
openBlockSize :: (IRExpr -> Int) -> Open a -> Int
openBlockSize count (Open _ binds) = sum (map (count . snd) binds)

-- | The escape hatch: copy the block into each field of the result that reads
-- it. Every use carries a comment giving its reason -- a block known not to
-- compound, so that its copies fold with the constants a shared tuple would
-- hide. @grep unsafeDistributeBlock@ is the audit of every place a block is
-- copied into a result's fields.
unsafeDistributeBlock :: Open PResult -> PResult
unsafeDistributeBlock (Open (PResult p d bc imp) binds) =
  PResult (P (wrap (unP p))) (wrap d) (wrap bc) (wrapFlag imp)
  where
    wrap = wrapBlockIfRead binds
    -- A statically constant flag reads nothing; skipping it outright keeps
    -- the common case from even testing it.
    wrapFlag f | f == constFalseIR || f == constTrueIR = f
               | otherwise                             = wrap f

-- | A probability value known to live in whatever space (linear or log) the
-- ambient 'Semiring' picked -- see the module header. Constructor
-- deliberately not exported.
newtype P = P { unP :: IRExpr }

-- | Escape hatch for subsystems that are deliberately linear-only regardless
-- of 'logSpace'. Named distinctly from 'sealP' so a grep for this name alone
-- is the "which subsystems ignore logSpace" audit -- which currently comes up
-- empty: its last users, the set-witness and plan-guided world measures,
-- became semiring-generic in task worlds-measure-unification.
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

-- | The dimension constants. A 'rDim' counts dimensions, so it is an 'Int'
-- in the IR (and in every backend), never a 'VFloat': a float dim invites
-- inexact comparisons on what is a count, and a test matching on @VInt 0@
-- silently never fired against one (task presult-dim-as-int).
dim0 :: IRExpr
dim0 = IRConst (VInt 0)

dim1 :: IRExpr
dim1 = IRConst (VInt 1)

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
anyGuardedDim sample = IRIf (IRUnaryOp OpIsAny sample) dim0 dim1

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
-- The set-witness and plan-guided world measures in IRCompiler.hs (task
-- worlds-measure-unification) and the AutoNeural read-logits network's own
-- inference function (@<nn>_auto@, task
-- read-logits-network-linear-under-logspace) were the last linear-only
-- subsystems; both are built from this vocabulary now ('fromLinearSR',
-- 'measureDiffSR', 'sumAllSR' are the pieces they needed).
data Semiring = Semiring
  { srLogSpace :: Bool                        -- ^ picks the 'LogSpace' field on nodes like 'IRDensity' (@Log@ vs @Linear@), where the operator alone isn't enough
  , srReduceOp :: ReduceOp                    -- ^ picks the IR *reduction* 'enumSumP' folds an enumerated support with -- see 'srPlus' below for why this can't just read off that function
  , srZero     :: IRExpr                      -- ^ probability zero / structurally impossible
  , srOne      :: IRExpr                      -- ^ multiplicative identity
  , srTimes    :: IRExpr -> IRExpr -> IRExpr  -- ^ independent conjunction (prodP, change-of-variables scaling)
  , srTimesOp  :: Operand                     -- ^ the 'Operand' 'srTimes' is spelled with, for the same reason 'srReduceOp' exists: an /elementwise/ product over two tensors ('BZip', task categorical-product-ov-fusion) has to name an operator inside a node, which no binary @IRExpr -> IRExpr -> IRExpr@ function can do. Must stay in step with 'srTimes' -- @OpMult@ linear, @OpPlus@ in log space, where getting it wrong silently computes a different number rather than failing
  , srPlus     :: IRExpr -> IRExpr -> IRExpr  -- ^ mixture / alternative sum (mixP). Pairwise only -- 'srReduceOp' is this same operator's identity for 'enumSumP's fold over a whole (possibly large) enumerated domain, kept as a separate field because the fold has to pick an IR *reduction node* (design ir-tensor-values' 'BReduce'), which no binary 'IRExpr -> IRExpr -> IRExpr' function can name.
  , srMinus    :: IRExpr -> IRExpr -> IRExpr  -- ^ AnyExcept: marginal minus one branch (mixSubP)
  , srComplement :: IRExpr -> IRExpr          -- ^ CDF flip under a decreasing transform: 1 - x linear, log(1 - exp x) log
  }

-- | Build the 'Semiring' for a family (task semiring-parametric-marginals) and
-- arithmetic domain (log-space-probability-computation). Orthogonal axes:
-- every family has both a linear and a log-space instance.
--
-- 'SemiringFamily' also names 'SRCounting' (model counting/#SAT), which this
-- function deliberately has no real instance for -- see the long comment on
-- 'SRCounting' in "SPLL.IntermediateRepresentation" for why a leaf-reweighting
-- semiring (one whose leaves report unit weight instead of their real
-- probability) is unsound under this codebase's Boolean-condition
-- representation, discovered and reverted during this task rather than
-- shipped. 'CompilerConfig.extraSemirings' is never populated with it by any
-- accepted CLI/API surface, so this arm is a defensive error, not a reachable
-- path.
mkSemiring :: SemiringFamily -> Bool -> Semiring
mkSemiring SRSumProduct False = linearSemiring
mkSemiring SRSumProduct True  = logSemiring
mkSemiring SRMaxProduct False = maxLinearSemiring
mkSemiring SRMaxProduct True  = maxLogSemiring
mkSemiring SRCounting   _     = error $ "Semiring.mkSemiring: SRCounting has no sound Semiring "
  ++ "instance (see the SRCounting comment in SPLL.IntermediateRepresentation) and should "
  ++ "never have reached here -- this is a defensive check, not a documented refusal path."

linearSemiring :: Semiring
linearSemiring = Semiring False ROpAdd const0 const1 (IROp OpMult) OpMult (IROp OpPlus) (IROp OpSub)
                          (upperTailComplement Linear (IROp OpSub const1))

logSemiring :: Semiring
logSemiring = Semiring True ROpLogSumExp negInfIR const0 (IROp OpPlus) OpPlus logSumExpIR logSubExpIR
                       (upperTailComplement Log logComplement)

-- | Max-product (MAP/Viterbi), linear domain: independent conjunction is still
-- plain multiply (maximizing a product of independent factors over independent
-- choices is the product of their own maxima), but the mixture/enumSum
-- combinator becomes max instead of sum -- the actual Viterbi swap, computing
-- the probability of the single most likely derivation of a value rather than
-- the total over every derivation. 0.0 is a valid max-identity here (every
-- probability is >= 0, so max(x, 0) = x), the same value linear sum-product
-- already uses for its zero -- 'opaqueMass's zero-test and every impossibility
-- comparison stay meaningful unchanged.
--
-- 'srMinus' has no sound definition: max has no inverse (recovering the
-- runner-up when the excepted branch WAS the max needs more state than a
-- scalar carries), so AnyExcept under this family is refused with a named
-- error at the point it would be compiled -- see 'mapHasNoExcept'.
maxLinearSemiring :: Semiring
maxLinearSemiring = Semiring False ROpMax const0 const1 (IROp OpMult) OpMult maxPairIR
                             mapHasNoExcept (upperTailComplement Linear (IROp OpSub const1))

-- | Max-product, log domain: 'srTimes' is add (as in ordinary log-space
-- sum-product -- independent factors still combine by adding their logs), and
-- the mixture combinator is a bare comparison of the two log-values rather
-- than 'logSumExpIR': max commutes with the monotone log transform, so picking
-- the larger log-probability already picks the larger probability, with no
-- need for log-sum-exp's numerical-stability machinery (there is no sum to
-- stabilize).
maxLogSemiring :: Semiring
maxLogSemiring = Semiring True ROpMax negInfIR const0 (IROp OpPlus) OpPlus maxPairIR
                          mapHasNoExcept (upperTailComplement Log logComplement)

-- | The log-space complement @log(1 - exp x)@ of a log-probability.
logComplement :: IRExpr -> IRExpr
logComplement x = IRUnaryOp OpLog (IROp OpSub const1 (IRUnaryOp OpExp x))

-- | 'srComplement' that keeps a normal upper tail's relative precision (task
-- cumulative-normal-upper-tail-cancellation). @1 - Phi(z)@ subtracts two
-- numbers within @Phi(-z)@ of each other, so a tail of size @P@ keeps only
-- about @1e-16 / P@ of relative precision: @P(Normal > 8)@ answered
-- 6.66e-16 for 6.22e-16. The normal is symmetric, so the complement of a
-- standard-normal CDF leaf is the same leaf at @-z@, which the runtimes
-- compute through @erfc@ without cancelling. The log form is the same leaf
-- too: @log(1 - exp(log Phi(z))) = log Phi(-z)@.
--
-- Structural, so it fires only where the leaf is visible: through 'IRIf'
-- arms and an 'IRLetIn' body (both commute with a pointwise complement), and
-- only for a leaf in the semiring's own 'LogSpace'. Anything else -- a
-- let-bound 'IRVar', a mixture sum, a uniform CDF (whose @1 - x@ is already
-- exact for @x@ in [0.5, 1], by Sterbenz) -- takes @fallback@, the plain
-- complement this replaced. 'complementWhen' is the variant for a site that
-- would otherwise let-bind the operand and complement the variable.
upperTailComplement :: LogSpace -> (IRExpr -> IRExpr) -> IRExpr -> IRExpr
upperTailComplement ls fallback = go
  where
    go (IRCumulative IRNormal ls' z) | ls' == ls = IRCumulative IRNormal ls' (IRUnaryOp OpNeg z)
    go (IRIf c a b) = IRIf c (go a) (go b)
    go (IRLetIn v x b) = IRLetIn v x (go b)
    go e = fallback e

-- | @if cond then srComplement x else x@, without either duplicating @x@ or
-- hiding it behind a variable from 'upperTailComplement'. The comparison
-- sites (@v > c@, @v < c@) pick between a CDF and its complement on the
-- queried Bool; they used to let-bind the CDF and complement the variable,
-- which 'upperTailComplement' cannot see through. Here the choice is pushed
-- down to the leaves instead: a standard-normal CDF leaf takes its argument
-- times @-1@ or @1@ (exact, and @z@ is evaluated once), and any other leaf is
-- let-bound locally -- in place, so it stays inside any 'IRLetIn' scope it
-- was pushed through -- and selected as before.
complementWhen :: Semiring -> IRExpr -> IRExpr -> CompilerMonad IRExpr
complementWhen sr cond = go
  where
    ls = if srLogSpace sr then Log else Linear
    go (IRCumulative IRNormal ls' z) | ls' == ls =
      return (IRCumulative IRNormal ls' (IROp OpMult (IRIf cond (IRConst (VFloat (-1))) const1) z))
    go (IRIf c a b) = IRIf c <$> go a <*> go b
    go (IRLetIn v x b) = IRLetIn v x <$> go b
    go e = do
      v <- mkVariable "cdf"
      return (IRLetIn v e (IRIf cond (srComplement sr (IRVar v)) (IRVar v)))

-- | Pairwise max of two already-let-bound values (both 'mixWith' and
-- 'enumSumP' bind their operands before combining them, so this never
-- duplicates evaluation). Valid in both linear and log domain: whichever
-- representation, "greater" means "more probable".
maxPairIR :: IRExpr -> IRExpr -> IRExpr
maxPairIR a b = IRIf (IROp OpGreaterThan a b) a b

-- | 'srMinus' for both max-product instances: max has no algebraic inverse, so
-- there is no way to recover "the marginal excluding one branch" from the
-- marginal's own max alone (see 'maxLinearSemiring'). Fires as a Haskell
-- 'error' at the point IRCompiler would otherwise build the AnyExcept/mixSubP
-- IR -- i.e. at compile time, on the one program shape (a marginal-except
-- query) that reaches it, not at every compile under this family.
mapHasNoExcept :: IRExpr -> IRExpr -> IRExpr
mapHasNoExcept = error $ "Semiring: this program compiles a marginal-except query "
  ++ "(AnyExcept -- e.g. P(x != v)), which has no defined meaning under the "
  ++ "max-product (MAP) semiring: max has no subtraction, so \"the best "
  ++ "derivation excluding one specific branch\" cannot be recovered from the "
  ++ "marginal's own max alone. Compile this program without requesting the "
  ++ "MAP semiring, or restructure the query to avoid marginal-except."

-- | The suffix 'SPLL.IRCompiler' appends to a function's name for an
-- 'extraSemirings' entry's compiled group (e.g. "main" + 'SRMaxProduct' ->
-- "main_map"), and what the CLI's @--semiring=@ list parses back from.
semiringSuffix :: SemiringFamily -> String
semiringSuffix SRSumProduct = sumProductGroupTag -- unused today (never an *extra* entry), named for completeness
semiringSuffix SRMaxProduct = maxProductGroupTag
semiringSuffix SRCounting   = countingGroupTag

-- | The group-name infix a compile under @fam@ must insert when referencing
-- ANOTHER top-level function's compiled inference function: @""@ for the
-- default family (so every pre-existing compile emits the identical
-- @<callee>_prob@ it always did), and @"_map"@ etc. for an extra one, so
-- that @main_map@'s body calls @h_map_prob@ rather than @h_prob@.
--
-- Without this, an extra-semiring group was only semiring-correct for the part
-- of the program inlined into its OWN body: a call to a top-level function
-- resolved to that callee's sum-product group, so any mixture living behind a
-- function call was summed rather than combined with the requested operator --
-- silently, with a plausible number rather than a crash. Measured at the time
-- this was fixed (task semiring-second-instance-and-kbest): with the mixture
-- inline in @main@, @main_map@ correctly gave 0.45; with the identical mixture
-- moved behind @h@ and @main = h@, it gave 0.46, the sum-product answer.
semiringGroupInfix :: SemiringFamily -> String
semiringGroupInfix SRSumProduct = ""
semiringGroupInfix fam          = "_" ++ semiringSuffix fam

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

-- | A plain linear quantity -- a |change-of-variables| factor, a sum of
-- softmax slot probabilities -- carried into the semiring's representation:
-- itself in linear space, its log in log space. For values the semiring has
-- no native leaf for; where one exists ('distDensity', 'distCumulative',
-- 'scaledNormalDensity') prefer it, since it keeps a deep tail's precision.
fromLinearSR :: Semiring -> IRExpr -> IRExpr
fromLinearSR sr x = if srLogSpace sr then IRUnaryOp OpLog x else x

-- | The inverse of 'fromLinearSR': a semiring value as a linear probability,
-- for a site that does arithmetic with it as a number rather than combining
-- it as a probability (the mixture weights of a moment match,
-- 'IRCompiler.momentsOf').
toLinearSR :: Semiring -> IRExpr -> IRExpr
toLinearSR sr x = if srLogSpace sr then IRUnaryOp OpExp x else x

-- | The measure of a set difference @a \ b@ with @b@ inside @a@ -- a CDF
-- difference @F(hi) - F(lo)@. Deliberately not 'srMinus': that is the
-- semiring's AnyExcept operator, which the max-product families leave
-- undefined (max has no inverse), whereas an interval's mass is an integral
-- in every family. So this reads only the arithmetic domain. In log space
-- the operands are read more than once: pass cheap (let-bound) expressions.
measureDiffSR :: Semiring -> IRExpr -> IRExpr -> IRExpr
measureDiffSR sr a b = if srLogSpace sr then logSubExpIR a b else IROp OpSub a b

-- | The semiring sum ('srPlus') of a list of alternatives, for a world set
-- summed outside 'mixP' (whose dim/flag bookkeeping it does not need). Linear
-- sum-product spells it as a right-nested 'OpPlus' chain. Every other
-- family's pairwise 'srPlus' (log-sum-exp, max) reads its operands more than
-- once, and a group of a few thousand worlds folded pairwise is a few thousand
-- nested IRIf chains (measured: compiling a depth-7 counting fold took
-- minutes instead of 30 seconds), so there the sum is one n-ary reduction over a
-- tensor of the operands -- the same node 'enumSumNode' folds an enumerated
-- support with.
sumAllSR :: Semiring -> [IRExpr] -> IRExpr
sumAllSR sr []  = srZero sr
sumAllSR _  [x] = x
sumAllSR sr xs
  | srReduceOp sr == ROpAdd = foldr1 (IROp OpPlus) xs
  | otherwise = IRBuiltin (BReduce (srReduceOp sr) 0) [IRBuiltin (BTensor [EFixed (length xs)]) xs]

-- | The native log-pdf/log-cdf leaf for a builtin distribution when @sr@ is
-- log-space, or the ordinary linear leaf otherwise. Distinct from
-- @log (IRDensity ...)@: the latter computes the linear pdf first (which
-- underflows in a deep tail, e.g. exp(-z^2/2) for large z) and only then
-- takes the log, so precision is already lost by the time the log is taken.
-- These emit the log formula directly in each backend instead.
distDensity :: Semiring -> Distribution -> IRExpr -> IRExpr
distDensity sr d s = IRDensity d (if srLogSpace sr then Log else Linear) s

distCumulative :: Semiring -> Distribution -> IRExpr -> IRExpr
distCumulative sr d s = IRCumulative d (if srLogSpace sr then Log else Linear) s

-- | The base normal density scaled by change-of-variables factors (division
-- by one or more positive scale terms -- sigma for PNormal, sigma*sample for
-- PLogNormal). The log form subtracts log(scaleFactor) from the native log-pdf
-- leaf instead of dividing the linear density, so a deep tail's precision
-- survives the whole formula rather than being lost to an earlier exp/log
-- round trip through the linear leaf.
scaledNormalDensity :: Semiring -> IRExpr -> [IRExpr] -> IRExpr
scaledNormalDensity sr z scaleFactors
  | srLogSpace sr = foldl (\acc s -> IROp OpSub acc (IRUnaryOp OpLog s)) (IRDensity IRNormal Log z) scaleFactors
  | otherwise     = foldl (\acc s -> IROp OpDiv acc s) (IRDensity IRNormal Linear z) scaleFactors

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
mass p = PResult (P p) dim0 const1 constFalseIR

-- | A result that resolves to no value of its own -- a closure, a lambda, an
-- error: dim 0, and NO branch. Zero branches is the exception, not the rule:
-- the branch-count anchor is that every terminal LEAF resolution counts 1,
-- whether it evaluates a distribution primitive or compares a
-- deterministically-known value against the sample. A deterministic leaf is
-- therefore 'mass'/'indicatorP', not this -- see the leaf-anchor note on
-- IRCompiler.hs's Var-is-a-local-variable case (task
-- bc-recursive-prob-divergence).
detP :: IRExpr -> PResult
detP p = PResult (P p) dim0 const0 constFalseIR

-- | A structurally impossible event: the wrong Either arm, an empty world set,
-- a failed guard. Probability zero (semiring zero, so linear 0.0 or log
-- -infinity), and flagged as such so that a mixture drops it without having
-- to recognise the zero numerically.
impossibleP :: Semiring -> PResult
impossibleP sr = PResult (P (srZero sr)) dim0 const0 constTrueIR

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

-- There is deliberately no general "apply @f@ to every field": its main use
-- was re-wrapping a let-in block around each field, the copy 'Open' exists to
-- make unwritable. The per-field transforms that remain are named for what
-- they do, and none of them adds a binding.

-- | Close every field over the same lambda parameters (a result compiled
-- inside a closure). A statically constant flag stays bare.
underLambdas :: [Varname] -> PResult -> PResult
underLambdas vars = eachField (\e -> foldr IRLambda e vars)

-- | Apply a variable substitution (a renaming) to every field.
substResult :: (IRExpr -> IRExpr) -> PResult -> PResult
substResult = eachField

-- | Every field raises @err@ when @cond@ holds (a runtime refusal); a
-- statically constant flag is left as it is.
errorWhen :: IRExpr -> IRExpr -> PResult -> PResult
errorWhen cond err = eachField (IRIf cond err)

-- | A result whose every numeric field is @e@ (an 'IRError' standing for the
-- whole result), flagged possible.
constantResult :: IRExpr -> PResult
constantResult e = PResult (P e) e e constFalseIR

-- | The shared body of the per-field transforms above. Not exported. A
-- statically constant flag is skipped, as it always was.
eachField :: (IRExpr -> IRExpr) -> PResult -> PResult
eachField f (PResult p d bc imp) = PResult (P (f (unP p))) (f d) (f bc) flag
  where flag | imp == constFalseIR || imp == constTrueIR = imp
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
--
-- Each guard is copied into every field, so a guard must be atomic or a small
-- test (a bound variable, a comparison of one), never a sub-result's field:
-- that would copy the sub-result per field, the duplication 'unpackResult'
-- documents. Every caller passes one today.
guardP :: Semiring -> [IRExpr] -> PResult -> PResult
guardP sr conds r = PResult
  (P (nest (srZero sr) (unP (rProb r))))
  (nest dim0 (rDim r))
  (nest const0 (rBranches r))
  (nest constTrueIR (rImposs r))
  where nest orElse e = foldr (\g acc -> IRIf g acc orElse) e conds

-- | Combine two results field-wise with the same operator. For the cases that
-- select between two whole results at runtime.
--
-- @f@ is applied once per field, so whatever it closes over -- typically the
-- condition of an @IRIf@ -- is copied into each; as for 'guardP', it must be
-- a bound variable or a small test, never a sub-result's field.
zipResult :: (IRExpr -> IRExpr -> IRExpr) -> PResult -> PResult -> PResult
zipResult f (PResult aP aDim aBC aImp) (PResult bP bDim bBC bImp) =
  PResult (P (f (unP aP) (unP bP))) (f aDim bDim) (f aBC bBC)
          (if aImp == bImp then aImp else f aImp bImp)

-- | 'zipResult' over three results, e.g. a two-way runtime test selecting one.
zip3Result :: (IRExpr -> IRExpr -> IRExpr -> IRExpr) -> PResult -> PResult -> PResult -> PResult
zip3Result f (PResult aP aDim aBC aImp) (PResult bP bDim bBC bImp) (PResult cP cDim cBC cImp) =
  PResult (P (f (unP aP) (unP bP) (unP cP))) (f aDim bDim cDim) (f aBC bBC cBC)
          (if aImp == bImp && bImp == cImp then aImp else f aImp bImp cImp)

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
                then srTimes sr x (IRIf (IROp OpEq (rDim r) dim0) (srOne sr) (scaleFactor (IRUnaryOp OpAbs deriv)))
                else IRIf (IROp OpGreaterThan deriv const0) x (srComplement sr x)

-- | Cumulative 'scaleCoV' through a point inverse that may be decreasing,
-- given the operand's own point result at the inverted bound (task
-- cdf-through-discrete-inverse-wrong).
--
-- For an increasing inverse @g@, @P(f v <= s) = P(v <= g s)@: the operand's
-- CDF, unchanged. For a decreasing one it is @P(v >= g s)@, and the
-- complement of the CDF, @1 - P(v <= x)@, is @P(v > x)@ -- short by the
-- operand's mass AT @x@. A continuous operand has none, which is why plain
-- 'scaleCoV' was right for every Float transform of a density; a discrete or
-- mixed one does (@-(if Uniform < 0.5 then 1.0 else 2.0)@ at @cdf(-1.0)@
-- answered 0.5 for 1). So that mass is added back: the point result's
-- probability where it is a mass (dim 0) and possible, zero where it is a
-- density or impossible.
scaleCoVAtom :: Semiring -> IRExpr -> PResult -> PResult -> PResult
scaleCoVAtom sr deriv atom = onProb flipped
  where
    atomMass = IRIf (rImposs atom) (srZero sr)
                 (IRIf (IROp OpEq (rDim atom) dim0) (unP (rProb atom)) (srZero sr))
    flipped x = IRIf (IROp OpGreaterThan deriv const0) x
                  (srPlus sr (srComplement sr x) atomMass)

-- | The ANY-safe wrapper of 'toIRInferenceSave': a marginal query over this
-- expression contributes mass 1, dim 0, no branches, without evaluating the body.
anySafe :: Semiring -> IRExpr -> (IRExpr -> IRExpr) -> PResult -> PResult
anySafe sr sample wrap (PResult p d bc imp) = PResult
  (P (IRIf isAnySample (srOne sr) (wrap (unP p))))
  (IRIf isAnySample dim0 (wrap d))
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
-- The sharing rule is 'closeResult's, for 'closeResult's reasons: bind the
-- packed result once, and project out of it only the fields that actually read
-- the block, so a statically-known dim or flag stays the constant it is
-- instead of being routed through an opaque tuple where folding cannot see it.
anySafeShared :: Semiring -> IRExpr -> Open PResult -> CompilerMonad PResult
anySafeShared sr sample (Open (PResult p d bc imp) binds)
  -- Below two readers there is no duplication to remove, and the tuple is not
  -- free; 'closeResult' declines on the same test. The second condition is the
  -- nesting test documented at 'blockNests'. Declining copies the block into
  -- each reading field ('unsafeDistributeBlock''s move, under 'anySafe''s
  -- guards): at most once, or a leaf block that cannot compound.
  | length readers <= 1 || not (any (blockNests . snd) binds) =
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
          -- where folding cannot see it ('closeResult' makes the same split).
          field i e dflt = case lookup i (zip [j | (j, _, _) <- readers] [0 ..]) of
            Just k  -> projMany k (length readers) (IRVar v)
            Nothing -> IRIf isAnySample dflt e
      return (PResult (P (field (0 :: Int) (unP p) (srOne sr)))
                      (field 1 d  dim0)
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
    fields      = [(unP p, srOne sr), (d, dim0), (bc, const0), (imp, constFalseIR)]
    readers     = [ (i, e, dflt)
                  | (i, (e, dflt)) <- zip [0 :: Int ..] fields, reads' e ]

-- | Does this block contain a loop -- a form whose body is evaluated once per
-- element of a domain -- or a function call, whose cost is opaque to the
-- compiler at this point and may itself be recursive?
--
-- This is the first half of the gate on sharing ('blockNests'), and it is a
-- statement about /run time/, not size: what makes a second copy of the block
-- cost anything is that it is a second traversal. A leaf block of constants
-- and arithmetic folds to a handful of literals, so duplicating it once costs
-- little and hiding it behind a tuple costs something -- the pack, the
-- projections, and the per-arm split-and-rebuild the optimizer does to a tuple
-- binding. A field that is not the same constant on every arm of the shared
-- tuple stays hidden from constant folding ('IROptimizer.foldConstProjections'
-- recovers the ones that are), which is the pessimization 'closeResult'
-- documents. What a leaf block does NOT survive is nesting: the second half of
-- the gate.
--
-- A pre-optimization node count was tried here first and is the wrong
-- question: @testCases\/equalsCoin@ builds a block of ~100 nodes that folds to
-- four literals, so it passes any size gate while having nothing worth
-- sharing. Whether the block /iterates/ survives folding, and is exactly the
-- property that made the enumerated sums this exists for expensive.
--
-- 'IRApply' is included for the same reason (task
-- recursive-list-prob-missed-cse): a self-recursive probability function
-- (the standard "coin-flip list" pattern, @main = if Uniform > p then []
-- else X : main@) compiles its tail field through exactly this path, and the
-- 'IRApply' calling @main_prob@ neither folds away nor is a syntactic loop --
-- but naively duplicating it per reading field (as 'anySafe' does when this
-- gate declines) re-invokes the recursive call once per field at every
-- nesting level, which is exponential in recursion depth. CSE cannot recover
-- this afterwards: each duplicate lands inside a differently-shaped guard
-- (a distinct @isAny@/@isclose@ context per field), so the copies never sit
-- in CSE's unconditional skeleton together. Unlike the loop constructors
-- above, an 'IRApply' is not proof the call is expensive -- it may be a cheap
-- local lambda or a non-recursive helper -- but its cost is unknown at this
-- point in the pipeline, so treating it as iterating is the conservative
-- choice performance-wise: a spurious extra tuple projection over one
-- avoidable re-evaluation, unlike the reverse. It is NOT automatically safe
-- on its own, though: sharing binds the block via a plain 'setVariables'
-- with no guard of its own, in whatever scope the call happens to run in --
-- fine when that scope is unconditional, wrong when a caller meant to guard
-- the sub-inference first and only apply the guard to the returned
-- 'PResult' afterwards (a deconstructing inverse's domain test, an InjF's
-- applicability test). 'IRCompiler.guardedSubInference' is the fix for that
-- half: every call site below 'toIRInferenceSave' that follows it with such
-- a guard now isolates the sub-inference's own bindings and re-threads them
-- through 'closeResult' with that same guard, so the two changes are a
-- matched pair.
-- | Would copying this block per field compound? The gate on
-- 'anySafeShared' (task presult-unbound-block-copied-per-field, settling
-- structured-accessor-compile-blowup's mechanism B with its option (a)).
--
-- Copying a block costs a constant factor when the block is a leaf: its few
-- bindings fold to literals, and the copies fold with them. It compounds when
-- the block already holds a COPIED sub-result: each level then copies its
-- child's copies, about three per deconstructing level, so a right-nested
-- accessor @fst (fst (if .. then ((if .., True), True) else ..))@ grew its
-- pre-optimization IR 7x per level (128 MB of -O0 Python, 7 s at -O2, for
-- four levels). So a block is shared when it holds either
--
-- * a loop or a call ('blockIterates'): copying it repeats a traversal, at
--   any depth; or
-- * a field 'anySafe' has already wrapped in its own copy of a block, i.e. an
--   @isAny@-guarded field whose else-arm is a let-block. This is the marker of
--   a level below that declined to share, and of one that shared too (the
--   shared binding has the same shape), so from the second nested level on
--   every level shares and the IR grows linearly with depth.
--
-- A single level of copying is still allowed, which is what keeps a shallow
-- program's folded output: sharing every block at two readers (option (d)
-- there) cost 1% more emitted -O2 code over the corpus than this test, even
-- with 'IROptimizer.foldConstProjections' recovering the shared tuple's
-- constants.
blockNests :: IRExpr -> Bool
blockNests e = blockIterates e || holdsCopiedField e
  where
    holdsCopiedField x = case x of
      IRIf (IRUnaryOp OpIsAny _) _ IRLetIn{} -> True
      _ -> any holdsCopiedField (getIRSubExprs x)

blockIterates :: IRExpr -> Bool
blockIterates e = iterates e || any blockIterates (getIRSubExprs e)
  where
    iterates x = case x of
      IRBuiltin BMapList _        -> True
      IRBuiltin BMap _            -> True
      IRBuiltin (BReduce _ _) _   -> True
      IRApply{}                   -> True
      _                           -> False

-- | Pack values into one right-nested tuple; a single value packs to itself.
-- Only the fields that read the shared block go in, so the common
-- probability-and-flag pair costs one 'IRConstruct' rather than the three a
-- full 'packResult' would build and the optimizer would then split and rebuild.
packMany :: [IRExpr] -> IRExpr
packMany []     = error "packMany: nothing to pack"
packMany [x]    = x
packMany (x:xs) = IRConstruct TgTuple [x, packMany xs]

-- | Read element @k@ of the @n@ that 'packMany' packed.
projMany :: Int -> Int -> IRExpr -> IRExpr
projMany _ 1 t = t
projMany 0 _ t = IRDestruct AcFst t
projMany k n t = projMany (k - 1) (n - 1) (IRDestruct AcSnd t)

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
-- would be provably-unread work. When it is on, one let-bound map over the
-- domain is reduced twice, so a @(probability, branchCount)@ body is evaluated
-- in one pass, the probability component exactly as 'enumSumNode' would. Either way this module needs no
-- knowledge of CompilerMetadata -- @countBranches@ arrives as a plain Bool.
enumSumP :: Semiring -> Bool -> (IRExpr -> IRExpr) -> Varname -> MultiValue -> IRExpr -> CompilerMonad PResult
enumSumP sr withBranchCount wrap v vals packed
  -- Only the probability is read, so the packed body is projected directly --
  -- one copy, no binding to clean up afterwards.
  | not withBranchCount =
      opaqueMass sr (wrap (enumSumNode sr v vals (unP (packedProb packed)))) const0
  -- ONE let-bound map over the domain, its two projections ('rProb' and
  -- 'rBranches') each reduced on their own axis: the probability with the
  -- semiring's own operator, the branch count always with plain 'ROpAdd'
  -- (a count is a count whichever semiring is active). Let-binding the mapped
  -- axis is what lets the two components reduce independently while the body
  -- is evaluated once -- the sharing the retired @IREnumSumPaired@ node
  -- existed to fake before the IR could name a vector of per-iteration
  -- results (task retire-irenumsum).
  | otherwise = do
      n <- mkVariable "enum_axis"
      body <- mkVariable "enum_body"
      let r = unpackResult body
          mapped = IRBuiltin BMap [IRLambda v (IRLetIn body packed (IRConstruct TgTuple [unP (rProb r), rBranches r])), tensorDomainSR vals]
          probs  = IRBuiltin BMap [IRLambda (n ++ "_p") (IRDestruct AcFst (IRVar (n ++ "_p"))), IRVar n]
          bcs    = IRBuiltin BMap [IRLambda (n ++ "_b") (IRDestruct AcSnd (IRVar (n ++ "_b"))), IRVar n]
      paired <- mkVariable "enum_paired"
      setVariables [(paired, wrap (IRLetIn n mapped
                                     (IRConstruct TgTuple [ IRBuiltin (BReduce (srReduceOp sr) 0) [probs]
                                                          , IRBuiltin (BReduce ROpAdd 0) [bcs] ])))]
      opaqueMass sr (IRDestruct AcFst (IRVar paired)) (IRDestruct AcSnd (IRVar paired))

-- | 'enumSumP' for an enumerated MIXTURE of a scalar real value whose terms
-- need not share a dimension: each term keeps its own dim and impossibility
-- flag, and the fold follows 'mixWith''s rule -- impossible terms are
-- dropped, the lower dimension wins, and only terms of the winning dimension
-- are summed. 'enumSumP' instead reports a mass (dim 0) and derives the flag
-- from the summed value, which is only right when every term is one.
--
-- The value is a real scalar, so a term's dim is 0 (an atom) or 1 (a
-- density) and "lowest wins" is "any possible atom wins": the decision is a
-- plain count of possible dim-0 terms, reduced with 'ROpAdd'. A max/min
-- reduction over the dims would say the same thing, but 'ROpMax' is refused
-- by the batched backend, and this must not narrow what compiles there.
--
-- With no possible atom, the result reports @densityDim@ -- the caller's
-- statement of a density term's dim (the continuous path passes
-- 'anyGuardedDim' of its sample) -- rather than reading one back off the
-- terms. The flag is structural where it can be: impossible when no term is
-- possible, and, for an atom sum (a discrete MASS), when that mass is exactly
-- zero -- sound there for the reason 'opaqueMass' gives. A density sum never
-- derives impossibility from its value.
--
-- Like 'enumSumP' it takes the per-iteration result packed ('packResult')
-- and binds it once inside the loop; the mapped axis is let-bound and read by
-- up to four reductions (atom count, possible count, probability, branch
-- count), so the body is evaluated once per value, not once per reduction.
enumMixP :: Semiring -> Bool -> (IRExpr -> IRExpr) -> IRExpr -> Varname -> MultiValue -> IRExpr -> CompilerMonad PResult
enumMixP sr withBranchCount wrap densityDim v vals packed = do
  n <- mkVariable "mix_axis"
  body <- mkVariable "mix_body"
  t <- mkVariable "mix_term"
  hasAtom <- mkVariable "mix_has_atom"
  paired <- mkVariable "mix_paired"
  let r = unpackResult body
      mapped = IRBuiltin BMap [ IRLambda v (IRLetIn body packed
                                  (packMany [unP (rProb r), rDim r, rImposs r, rBranches r]))
                              , tensorDomainSR vals ]
      field k = projMany k 4 (IRVar t)
      possible = notIR (field 2)
      atom = andIR possible (IROp OpEq (field 1) dim0)
      overTerms f = IRBuiltin BMap [IRLambda t f, IRVar n]
      countWhere cond = IRBuiltin (BReduce ROpAdd 0) [overTerms (IRIf cond const1 const0)]
      -- A possible term counts when it has the winning dimension: an atom if
      -- any atom is possible, otherwise any possible (density) term.
      counted = IRIf possible
                  (IRIf (IRVar hasAtom)
                     (IRIf (IROp OpEq (field 1) dim0) (field 0) (srZero sr))
                     (field 0))
                  (srZero sr)
      probSum = IRBuiltin (BReduce (srReduceOp sr) 0) [overTerms counted]
      bcSum   = if withBranchCount
                  then IRBuiltin (BReduce ROpAdd 0) [overTerms (field 3)]
                  else const0
  setVariables [(paired, wrap (IRLetIn n mapped
                                (IRLetIn hasAtom (IROp OpGreaterThan (countWhere atom) const0)
                                  (packMany [ probSum, IRVar hasAtom
                                            , IROp OpEq (countWhere possible) const0, bcSum ]))))]
  let out k = projMany k 4 (IRVar paired)
      atomWon = out 1
  return (PResult (P (out 0))
                  (IRIf atomWon dim0 densityDim)
                  (out 3)
                  (orIR (out 2) (andIR atomWon (IROp OpEq (out 0) (srZero sr)))))

-- | The IR node an enumerated sum/max of probabilities is built from: a
-- 'BMap' of the body over the domain, reduced along that one axis with the
-- semiring's own operator.
--
-- Until task retire-irenumsum this had a front-end constructor per reduction
-- operator (@IREnumSum@ for 'ROpAdd', @IRLogEnumSum@ for 'ROpLogSumExp')
-- that a later pass lowered into exactly this shape, and 'ROpMax' -- added
-- last -- skipped them and built the tensor form here. Every generic pass
-- paid for that split with a case per constructor, and a fourth reduction
-- would have cost a fourth. The operator is a field of 'BReduce', so it now
-- costs nothing: this function is total in 'srReduceOp' by construction.
--
-- Shared by 'enumSumP' and the hand-rolled double-enumeration cases in
-- IRCompiler.hs's 'toIRInference' that build an enumerated reduction directly
-- rather than through 'enumSumP'.
enumSumNode :: Semiring -> Varname -> MultiValue -> IRExpr -> IRExpr
enumSumNode sr v vals body =
  IRBuiltin (BReduce (srReduceOp sr) 0) [IRBuiltin BMap [IRLambda v body, tensorDomainSR vals]]

-- | The enumerated domain as a rank-1 tensor of constants, in the order the
-- enumeration loops over it.
tensorDomainSR :: MultiValue -> IRExpr
tensorDomainSR mv = IRBuiltin (BTensor [EFixed (length vals)]) (map (IRConst . valueToIR) vals)
  where vals = multiValueToValueList mv

-- | A discrete mass assembled by summing contributions (an enumerated support,
-- a set of plan worlds), with its branch count.
--
-- This is the one place the impossibility flag is read off the value rather
-- than taken from structure: whether ANY enumerated value contributed is not
-- expressible as a Bool over the summed body (there is no boolean reduction).
-- It is sound here in a way it is not in a mixture, because this is a discrete
-- MASS -- an exact zero means no value in the support matched, i.e. the event
-- really is impossible. A density, which may underflow while remaining
-- possible, never derives its flag this way. The sum is let-bound so the test
-- reads the value instead of duplicating the whole enumeration.
opaqueMass :: Semiring -> IRExpr -> IRExpr -> CompilerMonad PResult
opaqueMass sr p bc = do
  s <- mkVariable "enum_mass"
  setVariables [(s, p)]
  return (PResult (P (IRVar s)) dim0 bc (IROp OpEq (IRVar s) (srZero sr)))

-- | Close a scope back into a result: bind its let-in block ONCE, under
-- @guards@, and hand back projections off that single binding. The single
-- place (with its variants below) that decides how a result is shared with its
-- block (design presult-blocks-shared-by-construction).
--
-- The alternative -- wrapping the block around each field, which
-- 'unsafeDistributeBlock' still does on request -- re-wraps the
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
closeResult :: Semiring -> String -> [IRExpr] -> Open PResult -> CompilerMonad PResult
closeResult sr tag guards (Open r binds)
  -- Sharing only pays when two or more fields would each carry a copy of the
  -- block; below two there is no duplication to remove, and the tuple is not
  -- free: packing and projecting costs assignments per arm, the failed-guard
  -- fallback is another constant tuple per guard, and routing a statically-known
  -- dim or flag through it hides that constant from folding. Sharing every
  -- result unconditionally shrank -O0 400x but grew the -O2 OUTPUT 2.7x.
  | length readers <= 1 = return (PResult
      (P (guarded (srZero sr)  (wrapIfRead (unP (rProb r)))))
      (guarded dim0        (wrapIfRead (rDim r)))
      -- The branch count is deliberately not guarded: an arm that cannot occur
      -- still reports the branches it would have traversed, as before.
      (                     wrapIfRead (rBranches r))
      (guarded constTrueIR (wrapIfRead (rImposs r))))
  | otherwise = do
      v <- mkVariable tag
      let block = generateLetInExpr binds (packResult r)
      setVariables [(v, foldr (\g acc -> IRIf g acc (packResult (impossibleP sr))) block guards)]
      let proj prj e = if reads' e then prj (IRVar v) else guarded dim0 e
      return (PResult
        (P (IRDestruct AcFst (IRVar v)))
        (proj (IRDestruct AcFst . IRDestruct AcSnd) (rDim r))
        (if reads' (rBranches r) then IRDestruct AcFst (IRDestruct AcSnd (IRDestruct AcSnd (IRVar v))) else rBranches r)
        (if reads' (rImposs r)   then IRDestruct AcSnd (IRDestruct AcSnd (IRDestruct AcSnd (IRVar v)))
                                 else guarded constTrueIR (rImposs r)))
  where
    reads' = mentionsAny (map fst binds)
    readers = filter reads' [unP (rProb r), rDim r, rBranches r, rImposs r]
    wrapIfRead e = if reads' e then generateLetInExpr binds e else e
    -- Guards nest as IRIf, never OpOr/OpAnd -- see 'guardP'.
    guarded orElse e = foldr (\g acc -> IRIf g acc orElse) e guards

-- | Re-attach a sub-result's let-in block: bound once ('closeResult', under
-- @guards@) when copying it could compound, inline in each reading field when
-- it cannot. The one sanctioned exception to binding every block (task
-- presult-unbound-block-copied-per-field), and the same nesting test
-- 'anySafeShared' applies ('blockNests'), with the caller's own static
-- knowledge added: @nests@ says the sub-result's source holds a nested
-- sub-inference of the kind that would copy this block again one level up (a
-- probabilistic let, for the witness fold's body factor).
--
-- A leaf block is a bounded copy -- it holds no sub-result, so at most four
-- copies of a few bindings that typically fold to constants, and folded inline
-- a statically-known dim or flag stays visible where a shared tuple may hide it
-- ('closeResult' records the -O2 cost of that). The guards are applied only to
-- the shared binding, where they are what keeps the block unevaluated; the
-- inline form leaves the fields unguarded, so a caller must guard the result
-- field-wise itself (as 'guardP' does) whenever the block may not be
-- evaluated outside them.
shareUnlessLeaf :: Semiring -> String -> Bool -> [IRExpr] -> Open PResult -> CompilerMonad PResult
shareUnlessLeaf sr tag nests guards o
  | nests || openNests o = closeResult sr tag guards o
  -- A leaf block holds no sub-result, so its copies cannot compound; copied,
  -- its constant dim and flag fold where a shared tuple would hide them.
  | otherwise = return (unsafeDistributeBlock o)

-- | 'guardP' over a sub-result whose let-in block is re-attached to it: the
-- form @guardP sr guards (unsafeDistributeBlock o)@ takes,
-- without copying the block into each field (task
-- presult-unbound-block-copied-per-field).
--
-- When at most one field reads the block, that field gets it inline and the
-- result is exactly 'guardP''s. Otherwise the block is bound once under the
-- guards ('closeResult'), and a field that does not read it is guarded as
-- 'guardP' guards it -- the branch count included, which 'closeResult' leaves
-- unguarded -- so the two forms agree field by field.
guardedResult :: Semiring -> String -> [IRExpr] -> Open PResult -> CompilerMonad PResult
guardedResult sr tag guards o@(Open r _)
  -- At most one field reads the block, so distributing it copies it once.
  | length (filter reads' fields) <= 1 =
      return (guardP sr guards (unsafeDistributeBlock o))
  | otherwise = do
      s <- closeResult sr tag guards o
      return (if reads' (rBranches r) then s
                else s { rBranches = foldr (\g acc -> IRIf g acc const0) (rBranches r) guards })
  where
    reads' = openReads o
    fields = [unP (rProb r), rDim r, rBranches r, rImposs r]

-- | Wrap a let-in block around an expression only if the expression actually
-- reads something the block binds. A 'PResult' field that does not -- a
-- statically-known dim of 0, a branch count of 0, a constant flag -- otherwise
-- drags a full copy of the block behind a value it never looks at, which for a
-- body containing an enumerated sum means a duplicate of the single most
-- expensive node in the program per field per nesting level. 'closeResult'
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
packResult (PResult p d bc imp) =
  IRConstruct TgTuple [unP p, IRConstruct TgTuple [d, IRConstruct TgTuple [bc, imp]]]

-- | The fields of a packed result, read off the VARIABLE it is bound to.
--
-- It takes a name, not an expression, because that is the one rule for
-- 'PResult' sharing (task presult-unbound-block-copied-per-field): a result is
-- built from a non-atomic block only by binding the block. Unpacking an
-- expression puts a copy of it into each of the four fields, and when that
-- expression holds a sub-result built the same way the copies multiply per
-- nesting level -- the cause of most of this compiler's exponential compile
-- times, each one introduced by a fix that looked local. Bind the block
-- ('mkVariable' + 'setVariables', a 'WFactor''s bindings, or 'closeResult',
-- which also places guards), then unpack the variable. A caller that needs
-- only the probability of a packed expression reads it once with 'packedProb'.
unpackResult :: Varname -> PResult
unpackResult v = PResult (P (IRDestruct AcFst e)) (IRDestruct AcFst (IRDestruct AcSnd e))
                         (IRDestruct AcFst (IRDestruct AcSnd (IRDestruct AcSnd e)))
                         (IRDestruct AcSnd (IRDestruct AcSnd (IRDestruct AcSnd e)))
  where e = IRVar v

-- | The probability field of a packed result: a single read, so unlike
-- 'unpackResult' it may take the packed expression itself.
packedProb :: IRExpr -> P
packedProb = P . IRDestruct AcFst

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
    atomic (IRConst _)          = True
    atomic (IRVar _)            = True
    atomic (IRDestruct AcFst e) = atomic e
    atomic (IRDestruct AcSnd e) = atomic e
    atomic _                    = False
    bindFlag name f
      | atomic f  = return f
      | otherwise = do
          v <- mkVariable name
          setVariables [(v, f)]
          return (IRVar v)
