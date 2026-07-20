{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Fuzz-ish QuickCheck properties over randomly generated SPLL programs.
--
-- Two generators feed these properties (see ArbitrarySPLL.hs):
--
--   * 'genRawFuzzProgram' -- the full Expr/Program AST space (all 11
--     constructors, wide Constant leaves, arbitrary identifiers). Almost
--     every draw is ill-typed or otherwise invalid.
--
--   * 'genTypedProgram' -- a narrower, well-typed-by-construction generator
--     (scalar Float/Int/Bool programs built from the same combinators
--     SPLL.Examples hand-writes with) with a low discard rate, used to
--     exercise the actual inference invariants already checked over the
--     hand-written corpus in Spec.hs's Corpus group: P(ANY)=1, topK
--     threshold-0 reproduces exact inference, topK never inflates
--     probability, branch counting doesn't change the probability value, and
--     probability/density is never negative.
--
-- "Compile/generate/probability never crashes" (raises a Haskell exception
-- instead of returning `Left CompilerError`) is checked directly for both
-- generators: for the raw generator, almost every draw is expected to be
-- rejected, so crash-freedom is the *only* invariant that makes sense; for
-- the typed generator it is additionally meaningful on its own (a genuinely
-- well-typed program should never crash the compiler, whether or not that
-- particular shape is supported), which is why it is a separate, unguarded
-- property there rather than folded into the invariant checks below (those
-- swallow a compile-time crash as a discard via 'compileSafe', since
-- crash-freedom on well-typed input is already this module's job, not
-- theirs -- conflating the two would make a topK/branch-counting regression
-- indistinguishable from an unrelated crash in an unsupported IR shape).
--
-- Slow: each well-typed property compiles its drawn program under 2-3
-- CompilerConfigs, so this module lives in the opt-in Slow test group
-- (NEST_SLOW_TESTS=1) rather than the default `stack test` run.
--
-- A further property, 'prop_Fuzz_SamplingMatchesPDF' (exported via
-- 'superSlowFuzzTests'), is central enough to be worth its own even-slower
-- opt-in tier (NEST_SUPERSLOW_TESTS=1): it is the only property here that
-- cross-checks `generate` against `probability` (every other property only
-- cross-checks different CompilerConfigs against each other on the *same*
-- prob function), but doing so needs many forward samples per case, chosen
-- dynamically from the density at the query point (see its docs).
module TestFuzz (fuzzTests, superSlowFuzzTests) where

import Test.QuickCheck
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperties, testProperty)
import Control.Exception (try, evaluate, throwIO, fromException, SomeException, SomeAsyncException(..))
import Control.Monad (replicateM)
import Control.Monad.Random (evalRandIO)
import System.Timeout (timeout)
import Data.Maybe (isJust)
import Data.Number.Erf (erf)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Prelude
import SPLL.Validator (validateProgram)
import ArbitrarySPLL (genRawFuzzProgram, genTypedProgram)

-- | `show`ing a value forces every field, catching lazily-hidden crashes
-- (partial functions/undefined) that a bare WHNF `seq` would miss.
forceShow :: Show a => a -> a
forceShow x = length (show x) `seq` x

-- | Catch only *synchronous* exceptions, re-throwing anything asynchronous
-- (in particular the internal exception 'System.Timeout.timeout' uses to
-- cancel an action it's wrapping). Every use of 'try'/'catch' below runs
-- inside 'withinBudget'/'withinSuperSlowBudget', so a bare
-- 'try :: IO (Either SomeException a)' here would silently swallow the
-- timeout's own cancellation signal -- the action would treat "I was just
-- cancelled" as "the compiler crashed", report 'Nothing', and *keep running
-- the rest of the do-block* instead of actually aborting, defeating the
-- per-case time budget for exactly the slow cases it exists to bound (this
-- was empirically the cause of a single property run taking 529s instead of
-- its ~161-case*1s budget: a handful of topK-configured and/or-heavy
-- programs are genuinely slow to compile, each one running to completion
-- instead of being cut off at 1s).
trySync :: IO a -> IO (Either SomeException a)
trySync act = do
  r <- try act
  case r of
    Left e | Just (SomeAsyncException _) <- fromException e -> throwIO e
    _ -> return r

-- | Compile, catching any synchronous exception rather than letting it
-- propagate as a test failure -- used by the invariant properties below,
-- which care about topK/branch-counting/normalization behaviour on programs
-- that *did* compile, not about crash-freedom (that's
-- 'prop_Fuzz_TypedCompileNeverCrashes'’s job).
compileSafe :: CompilerConfig -> Program -> IO (Maybe IREnv)
compileSafe conf p = do
  r <- trySync (evaluate (forceShow (compile conf p))) :: IO (Either SomeException (Either CompilerError IREnv))
  return $ case r of
    Right (Right irEnv) -> Just irEnv
    _ -> Nothing

drawSample :: Program -> IREnv -> IO IRValue
drawSample p compiled = evalRandIO (runGenC p compiled [])

-- 'runProbC'/'runProbNamedC' irrefutably pattern-match on `probFun` being
-- `Just` (SPLL.Prelude:401) -- calling them on a compiled-but-generate-only
-- program (e.g. an If condition built from a non-invertible comparison
-- chain, which is a legitimate program shape, not a malformed one) throws
-- instead of returning `Left`. That's a real gap in the public API, but not
-- what these invariant properties are about, so check for a probability
-- function up front and discard (property True) rather than let it surface
-- as an unrelated crash in every prob-based invariant below.
hasProbFun :: IREnv -> Bool
hasProbFun compiled = isJust (probFun (lookupIREnv "main" compiled))

irProb :: Program -> IREnv -> IRValue -> Maybe IRValue
irProb p compiled sample
  | not (hasProbFun compiled) = Nothing
  | otherwise = either (const Nothing) Just (runProbC p compiled [] sample)

hasIntegFun :: IREnv -> Bool
hasIntegFun compiled = isJust (integFun (lookupIREnv "main" compiled))

-- | The CDF at a point, i.e. P(X <= x), used by 'windowP0' below to compute
-- an exact window-hit probability instead of a density*width approximation.
irInteg :: Program -> IREnv -> IRValue -> Maybe Double
irInteg p compiled x
  | not (hasIntegFun compiled) = Nothing
  | otherwise = case runIntegC p compiled [] x of
      Right (VTuple (VFloat c) _) -> Just c
      _ -> Nothing

-- | A properly-discarded QuickCheck test case (via the standard '==>'
-- mechanism, same idiom as 'testSamplingProb' in Spec.hs), for the "this
-- draw had nothing to check" branches below (a crash swallowed by
-- 'compileSafe', a generate-only program with no probFun, ...). Earlier
-- these branches returned a bare 'property True', which silently counts as
-- a real pass; measured empirically (see memory: project_fuzz_quickcheck),
-- ~68% of 'genTypedProgram' draws hit one of these branches, so a bare
-- 'property True' there was inflating the reported success count with
-- vacuous passes instead of surfacing (via QuickCheck's own discard-ratio
-- accounting, visible as "N successes; M discarded" or a "gave up" failure
-- if the ratio gets too extreme) how much of the nominal sample size is
-- actually exercising the invariant.
discardVacuous :: Property
discardVacuous = False ==> True

-- Pulls (prob, dim) out of the standard IRValue result shape, tolerating the
-- countBranches variant's extra third tuple component.
probDim :: IRValue -> Maybe (Double, Double)
probDim (VTuple (VFloat pr) (VFloat d)) = Just (pr, d)
probDim (VTuple (VFloat pr) (VTuple (VFloat d) (VFloat _))) = Just (pr, d)
probDim _ = Nothing

-- | The compiler is not (yet) known to terminate on arbitrary/ill-typed
-- input -- e.g. unification over a self-referential Var/Apply/Lambda soup
-- can loop -- so the crash-freedom properties below bound each draw's
-- wall-clock budget rather than risk hanging the whole Slow group. A timeout
-- is reported as a failure (with its quickcheck-replay seed), same as a
-- crash: a compiler that never terminates on some input is exactly the kind
-- of robustness gap this module exists to surface.
perCaseBudgetMicros :: Int
perCaseBudgetMicros = 1 * 1000 * 1000

-- | QuickCheck's default size schedule grows 0..~99 across a property's
-- successes; left unbounded, later draws produce deeply nested expressions
-- that can take a long time in RInfer/ModalityInfer/IROptimizer (a couple of
-- genuinely exponential passes have already needed fixing here before, see
-- memory: parser paren backtracking, IROptimizer CSE) even without hitting an
-- actual non-termination bug. 'withinBudget' is the safety net for real
-- hangs; capping structural size keeps ordinary draws fast so a whole
-- property doesn't spend its entire run on a handful of huge programs.
fuzzSize :: Int
fuzzSize = 12

withinBudget :: IO Property -> IO Property
withinBudget act = do
  result <- timeout perCaseBudgetMicros act
  return $ case result of
    Just prop -> prop
    Nothing -> counterexample ("did not terminate within " ++ show perCaseBudgetMicros ++ "us") False

-- ---------------------------------------------------------------------------
-- Crash-freedom: the compiler must never throw a Haskell exception, only
-- ever return `Left CompilerError`. `ioProperty` catches exceptions raised
-- inside its IO action and reports them as ordinary test failures, so these
-- properties don't need their own explicit exception handling.

-- | Raw AST space: almost every draw is invalid, so this is the only
-- meaningful invariant. Compiling successfully additionally draws one sample
-- and queries its own probability, exercising the generate/probability code
-- paths too, not just the compile pipeline itself.
prop_Fuzz_CompileNeverCrashes :: Property
prop_Fuzz_CompileNeverCrashes = withMaxSuccess 40 $ forAll (resize fuzzSize genRawFuzzProgram) $ \p -> ioProperty $ withinBudget $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      _ <- evaluate (fmap forceShow (runProbC p irEnv [] sample))
      return $ property True

-- | Well-typed scalar programs: a stronger, unguarded crash-freedom check
-- (see module header for why this differs from the invariant properties).
prop_Fuzz_TypedCompileNeverCrashes :: Property
prop_Fuzz_TypedCompileNeverCrashes = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      _ <- evaluate (fmap forceShow (runProbC p irEnv [] sample))
      return $ property True

-- ---------------------------------------------------------------------------
-- Well-typed scalar fuzzing: the inference invariants.

-- | Every well-typed generated program must pass the validator -- if it
-- doesn't, either the generator or the validator disagrees with the type
-- system about what's well-typed.
prop_Fuzz_TypedProgramsValidate :: Property
prop_Fuzz_TypedProgramsValidate = withMaxSuccess 200 $ forAll (resize fuzzSize genTypedProgram) $ \p ->
  case validateProgram p of
    Right _ -> property True
    Left err -> counterexample ("well-typed generated program failed validation: " ++ err) False

-- | P(ANY) = 1 for every well-typed generated program that has a probability
-- function at all (some scalar shapes -- e.g. an If condition built from a
-- non-invertible comparison chain -- are legitimately generate-only, and
-- some currently hit unsupported IR shapes, caught by
-- 'prop_Fuzz_TypedCompileNeverCrashes' instead -- both are discarded here).
prop_Fuzz_MarginalAnyIsOne :: Property
prop_Fuzz_MarginalAnyIsOne = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled >>= \irEnv -> irProb p irEnv VAny of
    Nothing -> return discardVacuous
    Just result -> return $ case probDim result of
      Just (pr, _) -> counterexample ("P(ANY) = " ++ show pr ++ ", expected ~1") (abs (pr - 1) < 1e-6)
      Nothing -> counterexample ("unexpected result shape: " ++ show result) False

-- | A probability/density value must never be negative, at a sample point
-- drawn from the program itself (a real distribution assigns non-negative
-- mass/density everywhere; a negative result means the change-of-variables
-- or mixture-combination arithmetic somewhere in IRCompiler has a sign bug).
prop_Fuzz_ProbabilityNeverNegative :: Property
prop_Fuzz_ProbabilityNeverNegative = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled of
    Nothing -> return discardVacuous
    Just irEnv -> do
      sample <- drawSample p irEnv
      return $ case irProb p irEnv sample of
        Nothing -> discardVacuous
        Just result -> case probDim result of
          Just (pr, _) -> counterexample ("P(" ++ show sample ++ ") = " ++ show pr ++ ", expected >= 0") (pr >= -1e-9)
          Nothing -> counterexample ("unexpected result shape: " ++ show result) False

-- | topK with threshold 0 prunes nothing, so it must reproduce exact
-- inference exactly, at a sample point drawn from the program itself.
prop_Fuzz_TopKZeroMatchesExact :: Property
prop_Fuzz_TopKZeroMatchesExact = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  exact <- compileSafe defaultCompilerConfig p
  topK <- compileSafe (defaultCompilerConfig { topKThreshold = Just 0.0 }) p
  case (exact, topK) of
    (Just exactEnv, Just topKEnv) -> do
      sample <- drawSample p exactEnv
      return $ case (irProb p exactEnv sample, irProb p topKEnv sample) of
        (Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
          (Just (pe, de), Just (pt, dt)) ->
            counterexample ("exact=" ++ show (pe, de) ++ " topK0=" ++ show (pt, dt))
              (abs (pe - pt) < 1e-6 && abs (de - dt) < 1e-6)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous  -- one side lacks a prob function: not this property's concern
    _ -> return discardVacuous

-- | Pruning can only zero out branches, never inflate probability above the
-- exact value, at a sample point drawn from the program itself.
prop_Fuzz_TopKNeverInflates :: Property
prop_Fuzz_TopKNeverInflates = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  exact <- compileSafe defaultCompilerConfig p
  topK <- compileSafe (defaultCompilerConfig { topKThreshold = Just 0.1 }) p
  case (exact, topK) of
    (Just exactEnv, Just topKEnv) -> do
      sample <- drawSample p exactEnv
      return $ case (irProb p exactEnv sample, irProb p topKEnv sample) of
        (Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
          (Just (pe, _), Just (pt, _)) ->
            counterexample (show pt ++ " > " ++ show pe) (pt <= pe + 1e-9)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous
    _ -> return discardVacuous

-- | Enabling branch counting must not alter the probability value, only add
-- a third result component, at a sample point drawn from the program itself.
prop_Fuzz_BranchCountingDoesNotChangeProbability :: Property
prop_Fuzz_BranchCountingDoesNotChangeProbability = withMaxSuccess 40 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinBudget $ do
  def <- compileSafe defaultCompilerConfig p
  bc <- compileSafe (defaultCompilerConfig { countBranches = True }) p
  case (def, bc) of
    (Just defEnv, Just bcEnv) -> do
      sample <- drawSample p defEnv
      return $ case (irProb p defEnv sample, irProb p bcEnv sample) of
        (Just defR, Just bcR) -> case (probDim defR, probDim bcR) of
          (Just (pd, _), Just (pb, _)) ->
            counterexample ("default=" ++ show pd ++ " bc=" ++ show pb) (abs (pd - pb) < 1e-9)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous
    _ -> return discardVacuous

return []

fuzzTests :: TestTree
fuzzTests = testGroup "Fuzz" [testProperties "properties" $(allProperties)]

-- ---------------------------------------------------------------------------
-- SuperSlow: sampling-vs-PDF self-consistency. Wired up with a plain
-- 'testProperty' rather than the quickcheck-th '$(allProperties)' splice
-- 'fuzzTests' uses above -- that macro scans the whole module for 'prop_'
-- bindings regardless of where the splice sits, so a second splice here
-- would re-collect (and re-run) every property already in 'fuzzTests' too.

-- | How many independent query points are checked per drawn program, all
-- against one *shared* batch of forward samples (see 'sharedBatchSize' /
-- 'runSamplingCheck'). Sampling is the expensive part (every sample is a
-- full interpreter draw through 'generate'); checking one more query point
-- against an already-drawn batch is just a cheap array scan plus one extra
-- 'probability' call, so batching turns one expensive compile+sample round
-- into 'queryPointCount' checks instead of one.
queryPointCount :: Int
queryPointCount = 5

-- | Target expected number of forward-sample "hits" landing in the
-- acceptance window, used to size the shared sample budget (see
-- 'dynamicSampleCount'). Large enough that the binomial estimate's relative
-- standard error (~1/sqrt(targetHits)) gives the z-test below reasonable power.
targetHits :: Double
targetHits = 30

-- | Forward-sample budget bounds. The lower bound keeps very-high-density
-- points (which would otherwise need only a handful of samples) statistically
-- meaningful; the upper bound keeps very-low-density points from blowing the
-- per-case time budget.
minSamples, maxSamples :: Int
minSamples = 200
maxSamples = 50000

-- | Acceptance window half-width for continuous (dim > 0) outputs. Discrete
-- (dim == 0) outputs are matched exactly instead (see 'sampleHit').
continuousEps :: Double
continuousEps = 0.1

-- | How many forward samples are needed so that, if the query point's
-- window-hit probability 'p0' is correct (samples*p0 hits in expectation --
-- 'p0' already folds in the acceptance window, so this is just 'pr' for a
-- discrete dim-0 output, or 'pr*eps^dim' for a continuous one, see
-- 'drawQueryPoints'), the expected hit count is ~'targetHits'. Solving for
-- samples and clamping to [minSamples, maxSamples] is what makes the sample
-- count "dynamic" per the type of the output -- a Bool/Int program and a
-- Float program (and, within Float, a sharply-peaked vs. near-uniform
-- density) all get a sample budget scaled to what they actually need,
-- instead of one fixed count that is wasteful for common cases and too weak
-- for rare ones. When batching several query points (see 'queryPointCount'),
-- the shared batch is sized to the *largest* of their individual needs, so
-- every point ends up adequately (or over-) sampled.
dynamicSampleCount :: Double -> Int
dynamicSampleCount p0
  | p0 <= 0 = maxSamples
  | otherwise = max minSamples (min maxSamples (ceiling (targetHits / p0)))

-- | Does a forward-sampled draw land in the acceptance window around the
-- query point? Exact equality for the discrete leaf types the typed
-- generator produces (Bool, Int); a symmetric epsilon-wide window for Float.
sampleHit :: Double -> IRValue -> IRValue -> Bool
sampleHit _ (VBool expected) (VBool actual) = expected == actual
sampleHit _ (VInt expected) (VInt actual) = expected == actual
sampleHit eps (VFloat expected) (VFloat actual) = abs (actual - expected) <= eps / 2
sampleHit _ _ _ = False

-- | Well-typed scalar fuzzing takes longer here than elsewhere in this module
-- (up to 'maxSamples' forward draws through the interpreter per case), so it
-- gets its own, larger per-case budget -- but kept far short of 30s+: a
-- pathologically slow *compile* (the same class of bug the Fuzz group's
-- "did not terminate" failures already surface, just not yet triggered by
-- one of those particular draws) given a generous budget doesn't just run
-- slow, it can allocate enough within that time to exhaust memory before
-- ever reaching the timeout check -- observed directly while tuning this
-- budget (a 30s cap OOM-killed the whole test process rather than cleanly
-- failing one case).
perCaseSuperSlowBudgetMicros :: Int
perCaseSuperSlowBudgetMicros = 8 * 1000 * 1000

withinSuperSlowBudget :: IO Property -> IO Property
withinSuperSlowBudget act = do
  result <- timeout perCaseSuperSlowBudgetMicros act
  return $ case result of
    Just prop -> prop
    Nothing -> counterexample ("did not terminate within " ++ show perCaseSuperSlowBudgetMicros ++ "us") False

-- ---------------------------------------------------------------------------
-- Statistics: classify an empirical hit rate against the compiler's claimed
-- density as significantly Different, confidently Identical (equivalent
-- within a practical margin), or Unclear (neither -- underpowered).

data DensityVerdict = Different | Identical | Unclear deriving (Show, Eq)

-- | Standard normal CDF via the erf identity, same formula already used
-- elsewhere in this codebase for the Gaussian CDF (see IRInterpreter.hs /
-- IROptimizer.hs), so no new numerics dependency beyond the existing 'erf'
-- package.
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))

-- | Standard error of an observed rate under the null hypothesis that the
-- true rate is exactly 'p0' -- i.e. a one-sample Wald test against a known
-- reference value (the compiler's claimed window-hit probability), not a
-- two-sample comparison, so using the null variance (rather than the
-- observed pHat's variance) for every test below is the standard choice.
seUnderNull :: Double -> Int -> Double
seUnderNull p0 samples = sqrt (max 1e-12 (p0 * (1 - p0)) / fromIntegral samples)

-- | Two-sided p-value for H0: true window-hit rate = p0.
twoSidedPValue :: Double -> Int -> Double -> Double
twoSidedPValue p0 samples pHat = 2 * (1 - normalCDF (abs z))
  where z = (pHat - p0) / seUnderNull p0 samples

-- | Bonferroni correction across 'queryPointCount' points checked per draw,
-- so the overall false-"Different" rate per *draw* (not per point) stays at
-- 'alphaDifferent' regardless of how many points are batched together.
alphaDifferent :: Double
alphaDifferent = 0.001 / fromIntegral queryPointCount

-- | Two one-sided tests (TOST), each at this level, for the 'Identical'
-- classification: standard TOST practice runs both legs at the same alpha
-- as a single hypothesis test, since together they bound the overall
-- equivalence claim's confidence at 1-alphaEquivalence.
alphaEquivalence :: Double
alphaEquivalence = 0.05

-- | Relative margin (fraction of the claimed rate) within which the
-- empirical rate is considered practically equivalent, not just
-- "not significantly different" -- e.g. 0.2 accepts a +/-20% relative wobble
-- as still matching, so 'Identical' means "confirmed close", not just
-- "failed to prove different".
equivalenceMargin :: Double
equivalenceMargin = 0.2

-- | TOST equivalence test: both one-sided legs (pHat significantly above the
-- lower bound, and significantly below the upper bound) must clear
-- 'alphaEquivalence' for the rate to be classified 'Identical'.
isEquivalent :: Double -> Int -> Double -> Bool
isEquivalent p0 samples pHat = pLower < alphaEquivalence && pUpper < alphaEquivalence
  where
    se = seUnderNull p0 samples
    lo = p0 * (1 - equivalenceMargin)
    hi = p0 * (1 + equivalenceMargin)
    -- H0: true rate <= lo, vs H1: true rate > lo.
    pLower = 1 - normalCDF ((pHat - lo) / se)
    -- H0: true rate >= hi, vs H1: true rate < hi.
    pUpper = normalCDF ((pHat - hi) / se)

-- | Different takes priority (a significant point-null rejection is strong
-- evidence regardless of the equivalence margin); otherwise Identical if
-- TOST confirms equivalence; otherwise Unclear -- not enough evidence either
-- way, which is exactly when 'runSamplingCheck' doubles the batch and retries.
classifyPoint :: Double -> Int -> Double -> (DensityVerdict, Double)
classifyPoint p0 samples pHat
  | pDiff < alphaDifferent = (Different, pDiff)
  | isEquivalent p0 samples pHat = (Identical, pDiff)
  | otherwise = (Unclear, pDiff)
  where pDiff = twoSidedPValue p0 samples pHat

-- ---------------------------------------------------------------------------

-- | A query point to check, with everything 'classifyPoint' needs cached:
-- the sampled value itself, the compiler's claimed density/dimension, the
-- acceptance window half-width, and 'p0' (the derived window-hit
-- probability: 'pr' directly for a discrete dim-0 output, 'pr*eps^dim' for a
-- continuous one).
data QueryPoint = QueryPoint
  { qpSample :: IRValue
  , qpEps    :: Double
  , qpP0     :: Double
  }

-- | Exact window-hit probability P(x - eps/2 <= X <= x + eps/2) via the
-- compiler's own CDF ('irInteg'), rather than approximating it as
-- density*width. The approximation assumes the density is locally constant
-- across the window, which fails right at a distribution's support boundary
-- -- e.g. a 'Uniform' query point drawn near 0: the window extends into
-- negative territory with zero density, so density*width overstates the
-- true window mass, which (empirically, when this was still an
-- approximation) produced a spurious 'Different' verdict purely from the
-- statistical test's own geometry, not a real compiler bug. Falls back to
-- the approximation only if no integrate function is available at all
-- (shouldn't happen for the continuous shapes 'genTypedProgram' produces,
-- since PNormal/PLogNormal/Integrate all guarantee a closed-form CDF -- see
-- CLAUDE.md's PType section -- but 'drawQueryPoints' filters query points
-- via 'irProb', not 'irInteg', so this stays defensive rather than partial).
windowP0 :: Program -> IREnv -> IRValue -> Double -> Double -> Double -> Double
windowP0 p irEnv (VFloat center) pr dim eps =
  case (irInteg p irEnv (VFloat (center - eps / 2)), irInteg p irEnv (VFloat (center + eps / 2))) of
    (Just lo, Just hi) -> max 0 (hi - lo)
    _ -> pr * eps ** dim
windowP0 _ _ _ pr dim eps = pr * eps ** dim

-- | Draw 'n' independent points from 'generate' and keep only the ones the
-- compiler assigns a well-formed, positive density to (a point with claimed
-- density 0 -- e.g. a query landing exactly on another branch's support --
-- carries no meaningful empirical rate to test against). Drawing the points
-- via 'generate' rather than e.g. a deterministic grid keeps them always
-- in-support, mirroring every other property in this module.
drawQueryPoints :: Program -> IREnv -> Int -> IO [QueryPoint]
drawQueryPoints p irEnv n = do
  samples <- replicateM n (drawSample p irEnv)
  return
    [ QueryPoint s eps p0
    | s <- samples
    , Just result <- [irProb p irEnv s]
    , Just (pr, dim) <- [probDim result]
    , pr > 0
    , let eps = if dim == 0 then 0 else continuousEps
    , let p0 = if dim == 0 then pr else windowP0 p irEnv s pr dim eps
    ]

-- | Draw one shared batch of 'batchSize' forward samples and classify every
-- query point against it (see 'queryPointCount' for why sharing one batch
-- across points is worthwhile). If any point comes back 'Different', fail
-- immediately with a full breakdown. Otherwise, if every point is either
-- 'Identical' or we're out of retries, pass (recording each point's verdict
-- via 'tabulate' so a full property run reports the Identical/Unclear split
-- across all draws -- a persistently high Unclear rate would mean the sample
-- budget or equivalence margin needs revisiting). If some points are still
-- 'Unclear' and retries remain, double the batch and try again -- mirrors
-- the retry-doubling in Spec.hs's 'testSamplingProb'.
runSamplingCheck :: Program -> IREnv -> [QueryPoint] -> Int -> Int -> IO Property
runSamplingCheck p irEnv points batchSize retriesLeft = do
  batch <- replicateM batchSize (drawSample p irEnv)
  let classified =
        [ (qp, verdict, pHat, pDiff)
        | qp <- points
        , let hits = length (filter (sampleHit (qpEps qp) (qpSample qp)) batch)
        , let pHat = fromIntegral hits / fromIntegral batchSize
        , let (verdict, pDiff) = classifyPoint (qpP0 qp) batchSize pHat
        ]
      describe (qp, verdict, pHat, pDiff) =
        "sample=" ++ show (qpSample qp) ++ " claimedRate=" ++ show (qpP0 qp)
          ++ " empiricalRate=" ++ show pHat ++ " verdict=" ++ show verdict ++ " p=" ++ show pDiff
      verdictOf (_, v, _, _) = v
  if any ((== Different) . verdictOf) classified
    then return $ counterexample
      ("batchSize=" ++ show batchSize ++ "\n" ++ unlines (map describe classified))
      False
    else if retriesLeft <= 0 || batchSize >= maxSamples || all ((/= Unclear) . verdictOf) classified
      then return $ tabulate "densityMatch verdict" (map (show . verdictOf) classified) (property True)
      -- Clamped to 'maxSamples': without this, doubling on every retry could
      -- overshoot the intended cap exponentially (batchSize*2^maxRetries),
      -- which is what actually ran a case out of memory during testing.
      else runSamplingCheck p irEnv points (min maxSamples (batchSize * 2)) (retriesLeft - 1)

-- | Bounded retries for 'runSamplingCheck': doubling the batch on an
-- 'Unclear' verdict quadruples statistical power (se shrinks with
-- 1/sqrt(samples)) each round, so this many rounds is enough headroom for
-- borderline cases without risking the per-case time budget.
maxRetries :: Int
maxRetries = 4

-- | The central cross-check: the empirical density estimated by forward
-- sampling ('generate') must agree with the analytic density the compiler's
-- probability function reports at the same points. Every other invariant in
-- this module only cross-checks two different CompilerConfigs against each
-- other on the *same* prob function (topK vs exact, BC vs default); this is
-- the only one that checks prob against generate independently, so a bug
-- that made both sides wrong in the same way (e.g. a shared but incorrect
-- InjF derivative table) would slip past every other property here but not
-- this one.
--
-- 'queryPointCount' points are drawn from the program itself via 'generate'
-- (so they are always in-support), then checked together against one shared
-- batch of forward samples sized to the hardest (lowest-density) point among
-- them (see 'drawQueryPoints' / 'runSamplingCheck').
prop_Fuzz_SamplingMatchesPDF :: Property
prop_Fuzz_SamplingMatchesPDF = withMaxSuccess 20 $ forAll (resize fuzzSize genTypedProgram) $ \p -> ioProperty $ withinSuperSlowBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled of
    Nothing -> return discardVacuous
    Just irEnv
      | not (hasProbFun irEnv) -> return discardVacuous
      | otherwise -> do
          points <- drawQueryPoints p irEnv queryPointCount
          case points of
            [] -> return discardVacuous
            _ -> do
              let initialBatch = maximum [dynamicSampleCount (qpP0 qp) | qp <- points]
              runSamplingCheck p irEnv points initialBatch maxRetries

superSlowFuzzTests :: TestTree
superSlowFuzzTests = testGroup "Fuzz" [testProperty "prop_Fuzz_SamplingMatchesPDF" prop_Fuzz_SamplingMatchesPDF]
