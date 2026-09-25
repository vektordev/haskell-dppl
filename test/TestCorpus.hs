-- | The @Corpus@ tasty group: metamorphic properties driven by the whole
-- @test/cases/**/*.ppl@+@.tst@ corpus (validation, sampling-vs-PDF, topK, branch
-- counting, P(ANY)=1, log-space vs linear, and -O0 vs the default -O2).
--
-- This lives in its own module -- and, via @haskell-dppl-test-corpus@ in
-- @package.yaml@, its own test-suite executable/OS process -- because
-- 'corpusTests' compiles the ENTIRE corpus (~300+ programs) once per
-- 'SPLL.IntermediateRepresentation.CompilerConfig', and needs eight
-- different configs (default, three topK thresholds, branch-counting,
-- log-space, topK+log-space, and unoptimized) to check its invariants
-- against each other. Each of those eight compiles is a full
-- @Map String (Either CompilerError IREnv)@ over the whole corpus, kept
-- alive for as long as any 'testProperty' built from it might still run.
--
-- Measured (2026-09-19, +RTS -s): the Corpus group alone peaks at ~1.4GB
-- resident, nearly 4x the 1048-test End2End group's ~380MB. Because tasty's
-- 'Test.Tasty.defaultMain' holds the whole 'Test.Tasty.TestTree' -- including
-- every 'Test.Tasty.QuickCheck.Property' closure, which is where these maps
-- are captured -- alive until it prints the final summary, none of that
-- memory is ever released mid-run: it stacks on top of whatever every later
-- group in the same process allocates, which is what turned a full
-- @stack test@ into an OOM kill (no assertion failure, just SIGKILL/-9) on a
-- memory-constrained box. Splitting Corpus into its own test-suite means its
-- process exits -- and its whole heap is reclaimed by the OS -- before or
-- after the rest of the suite runs in a separate process, the same way
-- manually batching @stack test --ta '-p ...'@ runs did as a workaround.
--
-- See also the filed follow-up task
-- @runtime-parametric-topk-threshold@ (in @NeST_internal_docs/tasks/@):
-- four of these eight configs differ only in 'topKThreshold' (or
-- 'topKThreshold' plus 'logSpace'), which is baked into the compiled
-- artifact at IR-compile time purely because IRCompiler needs to know the
-- cutoff to decide which branches to elide. Making the cutoff a runtime
-- parameter instead would collapse those four full-corpus compiles into
-- (up to) one, independent of this process-splitting fix.
module TestCorpus
  ( corpusTests
  , CorpusProbCase
  , loadCorpusCases
  , loadCorpusCdfCases
  ) where

import Test.QuickCheck hiding (verbose)
import Test.Tasty (TestTree, testGroup, localOption)
import Test.Tasty.QuickCheck (testProperty, QuickCheckMaxRatio(..))
import System.FilePath (takeBaseName)
import Data.Maybe (fromMaybe)
import Data.List (nubBy)
import Data.Function (on)
import Data.Foldable (toList)
import Control.Monad.Random.Lazy (evalRandIO, replicateM)
import qualified Data.Map.Strict as Map

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Validator
import SPLL.Prelude
import End2EndTesting (getAllTestFiles)
import TestCaseParser (parseProgram, parseTestCases, TestCase(..), Expectation(..), Backend(..))
import TestTolerances (probTolerance, samplingTolerance)
import TestSupport (topKConf, bcConf, reasonablyClose)

-- The expected-value tables that used to live here have moved into the
-- test/cases/**/*.ppl + *.tst corpus (see the End2End groups). The metamorphic
-- properties below draw their (program, sample, params, expected) pool from
-- that corpus instead: every interpreter-routed, non-neural prob/cdf case.
-- Neural programs are excluded because their parameters are mock symbols that
-- only End2EndTesting knows how to construct.
type CorpusProbCase = (String, (Program, IRValue, [IRValue], (IRValue, IRValue)))

loadCorpusCases :: IO [CorpusProbCase]
loadCorpusCases = do
  files <- getAllTestFiles
  pairs <- mapM (\(ppl, tst) -> do
    prog <- parseProgram ppl
    (backends, _slow, _ef, tcs) <- parseTestCases tst
    return (takeBaseName ppl, prog, backends, tcs)) files
  let usable = [(n, p, tcs) | (n, p, backends, tcs) <- pairs, Interpreter `elem` backends, null (neurals p)]
  -- 'Impossible' rows (task tst-dim-unasserted-at-zero-probability) carry no
  -- dim, so they are excluded from this pool rather than plumbed through as a
  -- placeholder: every metamorphic property below that draws on 'expected'
  -- already treats an actual-zero probability as carrying no dim information
  -- (its own "a === 0 .||. d === outDim" checks), so those rows contributed
  -- nothing to this pool's properties even when they were included.
  return [(n, (p, queryPoint, params, (prob, dim))) | (n, p, tcs) <- usable, ProbTestCase _ queryPoint params (Possible prob dim _) <- tcs]

-- | The cdf(...) rows of the same corpus slice, for the invariants that hold
-- of a CDF as much as of a point probability ('TopKNeverInflatesCdf').
loadCorpusCdfCases :: IO [CorpusProbCase]
loadCorpusCdfCases = do
  files <- getAllTestFiles
  pairs <- mapM (\(ppl, tst) -> do
    prog <- parseProgram ppl
    (backends, _slow, _ef, tcs) <- parseTestCases tst
    return (takeBaseName ppl, prog, backends, tcs)) files
  let usable = [(n, p, tcs) | (n, p, backends, tcs) <- pairs, Interpreter `elem` backends, null (neurals p)]
  return [(n, (p, queryPoint, params, (prob, dim))) | (n, p, tcs) <- usable, CumulTestCase _ queryPoint params (Possible prob dim _) <- tcs]

-- | A .tst probability expectation is always a (prob, dim) pair of floats;
-- anything else means the corpus parser handed us a malformed row, which is a
-- broken fixture rather than a property counterexample.
expectedProbDim :: (IRValue, IRValue) -> (Double, Double)
expectedProbDim (VFloat out, VFloat outDim) = (out, outDim)
expectedProbDim other = error ("malformed probability expectation in .tst corpus: " ++ show other)

-- Corpus-driven metamorphic properties. Each property enumerates its whole
-- selected slice deterministically (interpreter-routed, non-neural prob/cdf
-- cases; see forAllNamedIn), so any failing case is surfaced on every run rather
-- than only when a random draw happens to select it. Each invariant:
--  * ValidPrograms: every program the End2End interpreter runs must pass validateProgram.
--  * SamplingMatchesPDF: the empirical frequency of a sampleable value estimates the
--    density the .tst file asserts; non-sampleable shapes (bools, eithers, ANY) and
--    dim >= 2 cases are filtered out of the pool, zero-probability cases pass trivially.
--  * TopK*: pruning may only zero out branches, never invent mass -- threshold 0 must
--    reproduce exact inference and any threshold may only lower the probability.
--  * ProbWithBranchCounting: branch counting adds a third result component without
--    changing (prob, dim), and the values still match the corpus expectations.
--  * MarginalAnyIsOne: P(ANY) = 1 (normalization), queryable for any prob-compiled program.
-- Integral convergence (total mass ~ 1) is *not* a corpus-wide property: a finite
-- CDF probe point must dominate the program's support, and no single point covers
-- both heavy-tailed lognormal products and log-domain programs whose inverse
-- overflows. Convergence is instead encoded in the corpus itself as an upper-tail
-- cdf(x)=(1.0, 0.0) line per program.
corpusTests :: [CorpusProbCase] -> [CorpusProbCase] -> TestTree
corpusTests probPool cdfPool = localOption (QuickCheckMaxRatio 20) $ testGroup "Corpus"
  [ testProperty "ValidPrograms" (forAllNamed (\_ tc -> checkValidPrograms tc))
  -- dim 0 means the expectation refers to an atom, not a density: match drawn
  -- samples against it with a near-exact window (wide enough for float noise like
  -- 0.1+0.2, narrow enough to separate deliberately-close .tst atoms) instead of
  -- the density-estimation window. dim >= 2 cases (and non-sampleable shapes:
  -- bools, eithers, ANY) are filtered out of the enumerated pool rather than
  -- discarded at test time -- conjoin treats a discard as "gave up", not as a
  -- pass. The hit probability of a window estimate scales with density * eps^dim,
  -- so reliable multivariate estimates need prohibitively many samples; those
  -- cases are value-checked exactly by End2End.Interpreter instead.
  , testProperty "SamplingMatchesPDF" $ once $ conjoin
      [ counterexample ("corpus case: " ++ n) (testSamplingProb defaultEnvs n (samplingEps outDim) 1000 5 tc)
      | (n, tc@(_, inp, _, (_, outDim))) <- probPool
      , sampleable inp, outDim == VFloat 0 || outDim == VFloat 1 ]
  , testProperty "TopKInterprets" (forAllNamed (checkTopKInterprets topK005Envs))
  , testProperty "ProbWithBranchCounting" (forAllNamed (checkProbTestCasesWithBC bcEnvs))
  , testProperty "MarginalAnyIsOne" (forAllNamed (checkProbAny defaultEnvs))
  , testProperty "TopKZeroThreshMatchesExact" (forAllNamed (checkTopKZeroMatchesExact topK0Envs defaultEnvs))
  , testProperty "TopKNeverInflates" (forAllNamed (checkTopKNeverInflates topK01Envs defaultEnvs))
  , testProperty "TopKNeverInflatesCdf" (forAllNamedIn cdfPool (checkTopKNeverInflatesCdf topK01Envs defaultEnvs))
  -- task log-space-probability-computation: compiling with logSpace=True makes
  -- p()/cdf() return a log-probability instead of a linear one, so exp(actual)
  -- must reproduce the same corpus expectation as the linear compile. Excludes
  -- the programs whose inference routes through a subsystem the task
  -- deliberately left linear-only (set-valued witnesses / plan-guided lazy
  -- enumeration -- see the Semiring doc comment in IRCompiler.hs): those
  -- subsystems ignore the logSpace flag and keep returning a linear value, so
  -- exp(already-linear) would not match by construction. This is itself the
  -- task's invasiveness evidence, not a bug -- see the task doc/design update.
  , testProperty "LogSpaceMatchesLinear"
      (forAllNamedIn (filter ((`notElem` logSpaceUncoveredPrograms) . fst) probPool)
        (checkLogSpaceMatchesLinear logEnvs))
  -- task topk-logspace-unsound: logSpace combined with topK used to discard all
  -- probability mass (accProb/TOP_K_CUTOFF arithmetic was hardcoded linear, so
  -- every branch compared a log-probability against a linear threshold and was
  -- pruned unconditionally). Checked the same way LogSpaceMatchesLinear is --
  -- against the corresponding LINEAR topK compile at the same threshold, not
  -- against the (topK-off) .tst expectations, since topK is a real pruning
  -- optimisation whose own linear-mode result is the correct oracle here.
  -- Reuses logSpaceUncoveredPrograms: the set-witness/plan-enum subsystems it
  -- excludes stay linear-only regardless of topK.
  , testProperty "TopKLogSpaceMatchesLinear"
      (forAllNamedIn (filter ((`notElem` logSpaceUncoveredPrograms) . fst) probPool)
        (checkTopKLogSpaceMatchesLinear topK005LogEnvs topK005Envs))
  -- task multi-path-recovery-unmaterialized-crash: the IROptimizer must not be
  -- load-bearing for whether a compiled probability function is even runnable.
  -- That ticket's second witness (`let x = Uniform in (x, x+x)`) crashed with
  -- "Variable ast4 not declared" at optimizerLevel 0 while answering correctly
  -- at the default 2 -- constant folding happened to delete the dangling
  -- chain-name reference before anything evaluated it, so the whole suite
  -- (which only ever compiles at the default level) stayed green over a real
  -- codegen defect. Comparing the two levels on the same corpus points closes
  -- that blind spot: the optimizer is a rewrite, so agreement is exact, not
  -- approximate.
  , testProperty "UnoptimizedMatchesOptimized"
      (forAllNamed (checkUnoptimizedMatchesOptimized unoptEnvs defaultEnvs))
  ]
  where
    -- Compile each corpus program once per config, shared by every invariant and
    -- every .tst line drawn from that program (compile depends only on the pair,
    -- never on the queried sample/params).
    progs = uniqueCorpusPrograms (probPool ++ cdfPool)
    defaultEnvs = compileCorpusPrograms defaultCompilerConfig progs
    topK005Envs = compileCorpusPrograms (topKConf 0.05) progs
    topK0Envs   = compileCorpusPrograms (topKConf 0.0) progs
    topK01Envs  = compileCorpusPrograms (topKConf 0.1) progs
    bcEnvs      = compileCorpusPrograms bcConf progs
    logEnvs     = compileCorpusPrograms (defaultCompilerConfig {logSpace = True}) progs
    topK005LogEnvs = compileCorpusPrograms (topKConf 0.05) {logSpace = True} progs
    unoptEnvs   = compileCorpusPrograms (defaultCompilerConfig {optimizerLevel = 0}) progs
    -- Enumerate the whole (filtered) pool deterministically so any failing corpus
    -- case surfaces on every run, rather than only when a random draw selects it.
    forAllNamedIn pool f = once $ conjoin [counterexample ("corpus case: " ++ n) (f n tc) | (n, tc) <- pool]
    forAllNamed = forAllNamedIn probPool
    samplingEps outDim = if outDim == VFloat 0 then 1e-9 else 0.05

checkValidPrograms :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkValidPrograms (p, _, _, _) = case validateProgram p of
  Right _ -> property True
  Left err -> counterexample err False

checkTopKInterprets :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKInterprets envs n (p, inp, params, _) = ioProperty $ do
  let actualOutput = irDensityC envs n p params inp
  return $ actualOutput `reasonablyClose` actualOutput  -- No clue what the correct value should be here. Just test that is interprets to any value

-- Expected values in .tst files are rounded to ~4 digits, so compare with the
-- corpus-wide probTolerance (as the End2End checks do), and skip the dim check
-- for zero probability (a zero result carries no meaningful dimension).
checkProbTestCasesWithBC :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbTestCasesWithBC envs n (p, inp, params, expected) = ioProperty $ do
  let (out, outDim) = expectedProbDim expected
  let actualOutput = irDensityC envs n p params inp
  case actualOutput of
    VProbDimBC a d _ -> return $
      counterexample (show a ++ "/=" ++ show out) (property $ abs (a - out) < probTolerance)
      .&&. (a === 0 .||. d === outDim)
    _ -> return $ counterexample "Return type was no tuple" False

-- | Corpus programs whose inference reaches a subsystem the log-space task
-- deliberately left linear-only (set-valued witnesses, i.e. 'invertToWorlds'/
-- 'measureWorld'/'measureSet'/'cdfAtBound' -- programs whose observation
-- cannot be point-inverted onto the bound variable): those always compute a
-- linear value regardless of the 'logSpace' config flag (see the Semiring doc
-- comment and the 'linearSemiring'-pinned call sites in IRCompiler.hs), so
-- 'checkLogSpaceMatchesLinear' fails on them by construction --
-- exp(already-linear-not-log) is not the corpus expectation. This list was
-- determined empirically (not guessed) by running the property against the
-- WHOLE interpreter-routed non-neural corpus pool with a throwaway diagnostic
-- harness and recording every mismatch; it IS the invasiveness evidence the
-- task's acceptance criteria ask for, and every mismatch was a value
-- disagreement, never a crash. No plan-guided-lazy-enumeration
-- ("planEnum*"/shared-latent) corpus program appears here -- every one of
-- those already routes through the log-aware core combinators and passes.
logSpaceUncoveredPrograms :: [String]
logSpaceUncoveredPrograms =
  [ "letProbIntervalPair", "letProbIf", "letProbCmp", "letProbAbsNormal"
  , "setWitnessTupleDisjointFields", "letBoundEitherDestructure"
  , "eitherIfDeconstructObserve", "observeKeywordTruncated", "showcase_observe_inequality"
  , "observeTwoSidedInterval", "observeTwoSidedIntervalAnd", "observeDisjointTails"
  -- task set-witness-nested-let-classifier: the nested-let family inverts
  -- through an inner binding but is measured by the same linear-pinned
  -- measureWorld/measureSet, so it is uncovered for the same reason.
  , "setWitnessNestedLetShift", "setWitnessNestedLetDecreasing", "setWitnessNestedLetRename"
  , "setWitnessNestedLetTwoSided", "setWitnessNestedLetChain", "setWitnessNestedLetObserve"
  , "setWitnessNestedLetPointArm"
  -- task set-witness-interval-partial-inverse: interval transport through
  -- monotone InjF steps (and its image clamp), measured by the same linear
  -- measureSet.
  , "setWitnessTransportExpNegBound"
  , "setWitnessTransportExpLt"
  , "setWitnessTransportExpTwoSided"
  , "setWitnessTransportExpNested"
  , "setWitnessTransportExpOfNeg"
  , "setWitnessTransportPlus"
  , "setWitnessTransportPlusTwoSided"
  , "setWitnessTransportMultNeg"
  , "setWitnessTransportMultPos"
  , "setWitnessTransportDouble"
  , "setWitnessTransportNeg"
  , "setWitnessTransportLog"
  -- task set-witness-transport-drops-sibling-field-constraint: a point
  -- transport through a field constructor now carries the subtree's residue
  -- as a world factor, measured by the same linear-pinned measureWorld.
  , "setWitnessSiblingConst", "setWitnessSiblingMirror", "setWitnessSiblingFresh"
  , "setWitnessSiblingEither", "setWitnessSiblingCons", "setWitnessSiblingNested"
  , "setWitnessSiblingTwoOcc", "setWitnessSiblingNestedLet", "setWitnessSiblingBoolAny"
  , "setWitnessSiblingAdt"
  -- task continuous-recursive-gate-witness-failure: the gated value returned
  -- as itself is letProbAbsNormal's shape, measured by the same linear-pinned
  -- world sum; its p(0.0) row (atom vs density, dim 0 wins) is where the
  -- mismatch shows.
  , "gatedContinuousTruncated"
  -- task affine-gaussian-closure-lost-across-let-bindings: s1 and s2 are
  -- integrated out as affine Gaussian forms, but the threshold on s3 is still
  -- measured by the linear-pinned set-witness world sum.
  , "affineChainThreshold"
  ]

checkLogSpaceMatchesLinear :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkLogSpaceMatchesLinear envs n (p, inp, params, expected) = ioProperty $ do
  let (out, outDim) = expectedProbDim expected
  let actualOutput = irDensityC envs n p params inp
  case actualOutput of
    VProbDim logP d ->
      let linP = exp logP in
      return $
        counterexample (show linP ++ " (= exp(" ++ show logP ++ ")) /= " ++ show out)
          (property $ abs (linP - out) < probTolerance)
        .&&. (linP === 0 .||. d === outDim)
    _ -> return $ counterexample "Return type was no tuple" False

-- task topk-logspace-unsound: exp(logSpace+topK result) must reproduce the
-- LINEAR topK result at the same threshold -- the topK-off .tst values are
-- the wrong oracle here, since topK genuinely prunes (see
-- checkTopKZeroMatchesExact/checkTopKNeverInflates for the analogous
-- linear-only shape).
checkTopKLogSpaceMatchesLinear :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKLogSpaceMatchesLinear logEnvs linEnvs n (p, inp, params, _) = ioProperty $ do
  let logResult = irDensityC logEnvs n p params inp
  let linResult = irDensityC linEnvs n p params inp
  case (logResult, linResult) of
    (VProbDim logP logD, VProbDim linP linD) ->
      let expLogP = exp logP in
      return $
        counterexample (show expLogP ++ " (= exp(" ++ show logP ++ ")) /= " ++ show linP)
          (property $ abs (expLogP - linP) < probTolerance)
        .&&. (expLogP === 0 .||. logD === linD)
    _ -> return $ counterexample "Return type was no tuple" False

-- task multi-path-recovery-unmaterialized-crash: an optimizerLevel-0 compile must
-- answer exactly what the default level-2 compile answers. The optimizer only
-- rewrites (constant folding, CSE, let-in), so this is an equality, not a
-- tolerance -- and a mismatch is as likely to be a crash (a dangling reference
-- the folder happened to delete) as a wrong number.
checkUnoptimizedMatchesOptimized :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkUnoptimizedMatchesOptimized unoptEnvs optEnvs n (p, inp, params, _) = ioProperty $ do
  let unoptResult = irDensityC unoptEnvs n p params inp
  let optResult   = irDensityC optEnvs n p params inp
  case (unoptResult, optResult) of
    (VProbDim unoptP unoptD, VProbDim optP optD) ->
      return $
        counterexample ("unoptimized " ++ show unoptP ++ " /= optimized " ++ show optP)
          (property $ abs (unoptP - optP) < probTolerance)
        .&&. unoptD === optD
    _ -> return $ counterexample "Return type was no tuple" False

checkProbAny :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbAny envs n (p, _, params, _) = ioProperty $ do
  let actualOutput = irDensityC envs n p params VAny
  case actualOutput of
    VProbDim a _ -> return $ VFloat a `reasonablyClose` VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False

-- Corpus programs are compiled once per (name, config) and shared across every
-- test-case line drawn from that program: with N .tst lines per program and 5
-- corpus invariants each needing their own config, compiling per-line-per-invariant
-- (as irDensity does) redoes the same compile ~5N times over. compile only depends
-- on (config, program), never on the queried sample/params, so this is pure waste.
type CompiledPrograms = Map.Map String (Either CompilerError IREnv)

uniqueCorpusPrograms :: [CorpusProbCase] -> [(String, Program)]
uniqueCorpusPrograms pool = nubBy ((==) `on` fst) [(n, p) | (n, (p, _, _, _)) <- pool]

compileCorpusPrograms :: CompilerConfig -> [(String, Program)] -> CompiledPrograms
compileCorpusPrograms conf progs = Map.fromList [(n, compile conf p) | (n, p) <- progs]

lookupCompiled :: CompiledPrograms -> String -> Either CompilerError IREnv
lookupCompiled envs n = fromMaybe (error ("no compiled entry for corpus program " ++ n)) (Map.lookup n envs)

irDensityC :: CompiledPrograms -> String -> Program -> [IRValue] -> IRValue -> IRValue
irDensityC envs n p params s = either error id (lookupCompiled envs n >>= \c -> runProbC p c params s)

irCumulativeC :: CompiledPrograms -> String -> Program -> [IRValue] -> IRValue -> IRValue
irCumulativeC envs n p params s = either error id (lookupCompiled envs n >>= \c -> runIntegC p c params s)

-- Does a drawn sample match the expected value, within an epsilon-wide window
-- (maximum norm) on continuous components and exactly on discrete ones?
-- 'Nothing' windows every continuous component; 'Just sel' windows only the
-- float coordinates whose position (numbered left to right over the value) is
-- in @sel@ and ignores the rest -- see 'coordinateSubsets' for why that is
-- ever the right thing to do. Discrete components are matched exactly either
-- way: they carry no dimension, so they are never a coordinate to project onto.
sampleMatchesOn :: Maybe [Int] -> Double -> IRValue -> IRValue -> Bool
sampleMatchesOn sel epsilon expected actual = fst (go 0 expected actual)
  where
    windowed i = maybe True (i `elem`) sel
    go i (VFloat e) (VFloat a) = (not (windowed i) || abs (a - e) <= epsilon / 2, i + 1)
    go i (VInt e) (VInt a) = (e == a, i)
    go i (VTuple e1 e2) (VTuple a1 a2) =
      let (ok1, i1) = go i e1 a1
          (ok2, i2) = go i1 e2 a2
      in (ok1 && ok2, i2)
    go i (VList e) (VList a)
      | length es /= length as = (False, i)
      | otherwise = foldl step (True, i) (zip es as)
      where (es, as) = (toList e, toList a)
            step (ok, j) (ev, av) = let (ok', j') = go j ev av in (ok && ok', j')
    go i _ _ = (False, i)

-- How many continuous (float) coordinates the queried value has. This is the
-- AMBIENT dimension; the result's own rDim is the dimension of its support,
-- and the two differ exactly when the support is a lower-dimensional manifold
-- inside those coordinates.
floatCoordCount :: IRValue -> Int
floatCoordCount (VFloat _) = 1
floatCoordCount (VTuple a b) = floatCoordCount a + floatCoordCount b
floatCoordCount (VList l) = sum (map floatCoordCount (toList l))
floatCoordCount _ = 0

-- Which coordinate windows 'testSamplingProb' should try, given the ambient
-- float-coordinate count and the result's reported dimension.
--
-- When they agree (every corpus case but the degenerate-support ones) there is
-- exactly one window, over all coordinates: today's estimator, unchanged.
--
-- When the ambient count EXCEEDS the dimension, the support is a manifold and
-- windowing every coordinate measures the wrong thing. On `(x, x+x)` at
-- (0.3, 0.6) the ambient cube is |x-0.3| <= eps/2 AND |2x-0.6| <= eps/2, i.e.
-- |x-0.3| <= eps/4 -- half the interval eps^1 divides by, so the estimate
-- converges to half the density no matter how many samples are drawn. The
-- factor is the manifold's stretch, so no epsilon or sample count removes it:
-- the ambient cube converges to the marginal density on the FASTEST-STRETCHING
-- coordinate (slot 2 is Uniform(0,2), density 0.5), while the compiler reports
-- the marginal on the slot it witnessed the latent through (slot 1 is
-- Uniform(0,1), density 1.0). Both are honest densities of the same
-- distribution; they just differ in which coordinate they are taken with
-- respect to, and rDim fixes the exponent without fixing that choice.
--
-- So we enumerate every dim-sized subset of the coordinates and window on that
-- subset alone, and 'testSamplingProb' accepts if ANY of them reproduces the
-- compiler's value -- the claim being that the reported density is the marginal
-- on SOME dim-sized set of the observed coordinates, which is what witnessed
-- inference computes (it inverts the observation onto latents through a chosen
-- set of slots). A wrong value still fails, because it has to miss every
-- subset. Caveat: a manifold that self-intersects under the chosen projection
-- would over-count, which can only turn a failure into a pass, never the
-- reverse -- no such corpus shape exists today.
--
-- Note what this deliberately does NOT decide: with more than one admissible
-- chart it accepts the marginal on any of them, so it would pass a compiler
-- reporting 0.5 (the slot-2 chart) just as it passes the 1.0 it reports today.
-- That is the right scope for a metamorphic property -- both numbers really are
-- densities of the same distribution -- and the .tst expectation pins the
-- convention exactly, checked value-for-value by the End2End backends. Which
-- convention SHOULD be the language's is open; see task warn-correlated-slots.
--
-- A projected window says nothing about whether the query is ON the manifold --
-- it drops exactly the coordinates that decide that -- so 'testSamplingProb'
-- keeps the two questions apart, the way the compiled result itself does (a
-- dim-0 support indicator times a dim-'outDim' density): the ambient window is
-- an existence test for support, and only once some draw lands in it does a
-- projected window get to carry the measure. Off the manifold no draw lands in
-- the ambient window and the estimate is 0, which is what the compiler answers
-- there. Without that split, `p((0.3, 0.7)) = 0` on `(x, x+x)` estimates 1.0:
-- projecting onto slot 1 alone cannot tell 0.7 from the 0.6 the manifold
-- carries.
--
-- dim 0 keeps the all-coordinate window: an atom is pinned in every coordinate,
-- and a 0-sized subset would window nothing at all and count every draw.
coordinateSubsets :: Int -> Int -> [Maybe [Int]]
coordinateSubsets coords dim
  | dim <= 0 || coords <= dim = [Nothing]
  | otherwise = map Just (subsetsOfSize dim [0 .. coords - 1])

subsetsOfSize :: Int -> [a] -> [[a]]
subsetsOfSize 0 _ = [[]]
subsetsOfSize _ [] = []
subsetsOfSize k (x:xs) = map (x:) (subsetsOfSize (k - 1) xs) ++ subsetsOfSize k xs

-- Shapes testSamplingProb can estimate a PDF for; everything else is discarded.
sampleable :: IRValue -> Bool
sampleable (VFloat _) = True
sampleable (VInt _) = True
sampleable (VTuple a b) = sampleable a && sampleable b
sampleable (VList l) = all sampleable l
sampleable _ = False

--Sample PDF against expected PDF. Retry specific number of times with double the samples each time
testSamplingProb :: CompiledPrograms -> String -> Double -> Int -> Int -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
testSamplingProb envs n epsilon samples retries tc@(p, inp, params, (VFloat out, VFloat outDim))
  | sampleable inp = ioProperty $ evalRandIO $ do
    let compiledEnv = either error id (lookupCompiled envs n)
    let gen = runGenC p compiledEnv params
    drawn <- replicateM samples gen
    -- The maximum norm creates an outDim-dimensional hypercube of volume
    -- epsilon^outDim; for purely discrete samples outDim is 0 and no division
    -- happens. One estimate per candidate coordinate window -- a single
    -- all-coordinate one unless the support is a lower-dimensional manifold,
    -- see 'coordinateSubsets'.
    let estimateOn sel =
          let countInside = length (filter (sampleMatchesOn sel epsilon inp) drawn)
              ratioInside = fromIntegral countInside / fromIntegral samples
          in ratioInside / (epsilon ** outDim)
    let windows = coordinateSubsets (floatCoordCount inp) (round outDim)
    -- On a manifold the ambient window no longer carries the measure, so it
    -- serves as the support test instead: no draw inside it means the query is
    -- off-support and the density is 0. Where the ambient window IS the only
    -- window (full-dimensional support) this is subsumed -- an empty window
    -- already estimates 0 -- so the branch changes nothing there.
    let onSupport = windows == [Nothing] || any (sampleMatchesOn Nothing epsilon inp) drawn
    let estimates = if onSupport then map estimateOn windows else [0]
    let valid = any (\e -> abs (e - out) <= samplingTolerance) estimates
    if valid then
      return $ property True
    else
      if retries > 0 then
        return $ testSamplingProb envs n epsilon (samples * 2) (retries - 1) tc
      else
        return $ counterexample ("Sampled PDF is: " ++ show estimates ++ ", but should be: " ++ show out) (property valid)
testSamplingProb _ _ _ _ _ _ = False ==> False

-- Threshold=0 never prunes any branch, so results must match exact inference.
checkTopKZeroMatchesExact :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKZeroMatchesExact topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  case (topKResult, exactResult) of
    (VProbDim topKP topKD, VProbDim exactP exactD) ->
      return $ VFloat topKP `reasonablyClose` VFloat exactP
          .&&. VFloat topKD `reasonablyClose` VFloat exactD
    _ -> return $ counterexample "Return type was no tuple" False

-- Pruning can only zero out branches, never inflate probability above the exact value.
checkTopKNeverInflates :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKNeverInflates topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  return (topKNeverInflates topKResult exactResult)

-- | The CDF half of 'checkTopKNeverInflates' (task
-- topk-inflates-probability-int-comparison-mix): a CDF is a probability too,
-- and the cumulative path has its own complement site (the change-of-variables
-- flip under a decreasing inverse, 'scaleCoV') that the point-query pool never
-- exercises -- 'topKComplementCdfFlip' is its canary.
checkTopKNeverInflatesCdf :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKNeverInflatesCdf topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irCumulativeC topKEnvs n p params inp
  let exactResult = irCumulativeC defEnvs n p params inp
  return (topKNeverInflates topKResult exactResult)

-- | The one-sided topK invariant on a (pruned, exact) result pair. A pruned
-- probability is a lower bound on the exact one -- but only at the same
-- dimension. Pruning removes alternatives from a mixture, and the mixture
-- reports the LOWEST dim among the alternatives it still has, so the pruned
-- dim can only rise (test/cases/topk-pruning/topKPrunesMassArm: pruning the then-arm's
-- point mass at 1.0 leaves the else-arm's density, (0.95, dim 1) against the
-- exact (0.05, dim 0) -- a density and a mass are not comparable). So: equal
-- dims compare values, unequal dims require the pruned one to be higher.
topKNeverInflates :: IRValue -> IRValue -> Property
topKNeverInflates topKResult exactResult = case (topKResult, exactResult) of
    (VProbDim topKP topKD, VProbDim exactP exactD)
      | topKD == exactD ->
          counterexample (show topKP ++ " > " ++ show exactP ++ " at dim " ++ show exactD) (topKP <= exactP + 1e-9)
      | otherwise ->
          counterexample ("pruned dim " ++ show topKD ++ " below exact dim " ++ show exactD) (topKD > exactD)
    _ -> counterexample "Return type was no tuple" False
