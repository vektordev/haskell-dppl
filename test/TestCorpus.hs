{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
-- | The @Corpus@ tasty group: metamorphic properties driven by the whole
-- @test/cases/**/*.ppl@+@.tst@ corpus (validation, sampling-vs-PDF, topK, branch
-- counting, P(ANY)=1, log-space vs linear, -O0 vs the default -O2, and operand
-- order under topK).
--
-- This lives in its own module -- and, via @haskell-dppl-test-corpus@ in
-- @package.yaml@, its own test-suite executable/OS process -- because
-- 'corpusTests' compiles the ENTIRE corpus (~300+ programs) once per
-- 'SPLL.IntermediateRepresentation.CompilerConfig', and needs six
-- different configs (default, topK, branch-counting, log-space,
-- topK+log-space, and unoptimized) to check its invariants against each
-- other. Each of those compiles is a full
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
-- (Until task runtime-parametric-topk-threshold there were eight: three topK
-- thresholds were three full-corpus compiles. The topK cutoff is now a runtime
-- parameter of the compiled functions, so the 0, 0.05 and 0.1 thresholds share
-- one compile re-thresholded by 'withTopKCutoff'. topK+log-space keeps its
-- own compile, because log space is a compile-time semiring choice.)
--
-- Two of the six compiles serve only a Slow-tier property each, and since the
-- maps are lazy a default run never builds them: topK+log-space
-- (TopKLogSpaceMatchesLinear; the default "topK runtime cutoff" group already
-- checks the log-space cutoff conversion on purpose-built programs) and -O0
-- (UnoptimizedMatchesOptimized, a check on the optimizer and on IR the
-- optimizer must not be load-bearing for).
module TestCorpus
  ( corpusTests
  , CorpusProbCase
  ) where

import SPLL.IRTypeCheck (CheckedIR)
import Test.QuickCheck hiding (verbose)
import Test.Tasty (TestTree, testGroup, localOption)
import Test.Tasty.QuickCheck (testProperty, QuickCheckMaxRatio(..))
import Test.Tasty.HUnit (testCaseInfo, assertFailure)
import Control.Exception (SomeException, evaluate, try)
import System.Timeout (timeout)
import Data.Maybe (fromMaybe)
import Data.List (nub, nubBy, isPrefixOf)
import Data.Function (on)
import Data.Foldable (toList)
import Control.Monad.Random.Lazy (evalRandIO, replicateM)
import qualified Data.Map.Strict as Map

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.CompilerConfig
import SPLL.Validator
import SPLL.Prelude
import CorpusSweep
import TestCaseParser (TestCase(..), Expectation(..), Backend(..))
import TestTolerances (probTolerance, samplingTolerance)
import TestSupport (topKConf, bcConf, reasonablyClose)
import ImpactManifest
import End2EndTesting (programRuntimeFields, shapedCases)
import Rewrites (commuteSites)

-- The expected-value tables that used to live here have moved into the
-- test/cases/**/*.ppl + *.tst corpus (see the End2End groups). The metamorphic
-- properties below draw their (program, sample, params, expected) pool from
-- that corpus instead: every interpreter-routed, non-neural prob/cdf case.
-- Neural programs are excluded because their parameters are mock symbols that
-- End2EndTesting shapes; the two sampler sweeps take them, shaped
-- ('samplerPoolEntry', 'shapedEntry').
type CorpusProbCase = (String, (Program, IRValue, [IRValue], (Double, Int)))

-- | The slice every Corpus sweep selects.
corpusPoolEntry :: CorpusEntry -> Bool
corpusPoolEntry e = Interpreter `elem` ceBackends e && null (neurals (ceProgram e))

-- | The slice the two sampler sweeps select: 'corpusPoolEntry' with the
-- neural programs added, whose mock networks the interpreter's sampler and
-- density both read through 'programMockOracle'.
samplerPoolEntry :: CorpusEntry -> Bool
samplerPoolEntry e = Interpreter `elem` ceBackends e

-- | Corpus programs 'SamplingMatchesPDF' is known to fail on, each with its
-- tracking document. The check is inverted for them: some row must still
-- miss, so a fix cannot leave the list stale.
knownSamplerMismatches :: [(String, String)]
knownSamplerMismatches =
  -- The enumerated sum over observe's {0, 2} reports a density-valued weight
  -- at dim 0, so the sampler (which never draws x == 0.0) estimates 0 mass.
  [ ("observeContinuousEqualsLetBound", "enumerated-weight-density-reported-as-mass")
  , ("observeContinuousEqualsLetfree", "enumerated-weight-density-reported-as-mass")
  , ("observeNegatedContinuousEqualsLetfree", "enumerated-weight-density-reported-as-mass") ]

-- | A corpus entry with its rows' neural parameters shaped
-- ('End2EndTesting.shapedCases'); a non-neural entry is unchanged.
shapedEntry :: CorpusEntry -> CorpusEntry
shapedEntry e = e { ceCases = shapedCases e }

-- | Does 'SamplingMatchesPDF' check this row: a shape it can window, at a
-- dimension a window over 1000-odd draws can estimate.
samplerWindowed :: IRValue -> Int -> Bool
samplerWindowed inp outDim = sampleable inp && outDim <= 1 && densityLivesOnSamples inp outDim

-- | The parameter lists 'SamplesInSupport' samples a program at: those of its
-- p() rows of dim >= 2, each once.
supportCheckedParams :: CorpusEntry -> [[IRValue]]
supportCheckedParams e = nub [ params | (_, (_, _, params, (_, d))) <- probCasesOf [e], d >= 2 ]

-- | The rows 'SamplingMatchesPDF' estimates on a program, grouped by
-- parameter list: the rows of one group share their draws.
windowedRowGroups :: CorpusEntry -> [([IRValue], [(IRValue, (Double, Int))])]
windowedRowGroups e = [ (params, [ (inp, ex) | (ps, inp, ex) <- rows, ps == params ]) | params <- nub [ ps | (ps, _, _) <- rows ] ]
  where rows = [ (params, inp, ex) | (_, (_, inp, params, ex@(_, d))) <- sampledProbCasesOf [e], samplerWindowed inp d ]

-- | Every group of a program through 'samplingRows'.
runGroups :: CompiledPrograms -> String -> Bool -> Program -> [([IRValue], [(IRValue, (Double, Int))])] -> IO [((IRValue, (Double, Int)), RowVerdict)]
runGroups envs n mayFail p groups = concat <$> mapM (\(params, rows) -> samplingRows envs n mayFail p params rows) groups

-- | One row's verdict as a property.
rowProperty :: ((IRValue, (Double, Int)), RowVerdict) -> Property
rowProperty ((inp, _), verdict) = counterexample ("row p(" ++ show inp ++ ")") $ case verdict of
  RowPass -> property True
  RowSkip l -> label l True
  RowFail why -> counterexample why False

-- | Bump when the sampler checks' logic changes.
samplingCheckVersion, supportCheckVersion :: String
samplingCheckVersion = "corpus-sampling-v3"
supportCheckVersion = "corpus-support-v1"

-- | Key of a sampler check on one program: its default compile, its runtime
-- fields and the rows or parameters it samples at, with the interpreter
-- fingerprint; this module's source joins the harness. A refused compile has
-- no key, so the check runs.
samplerKey :: Manifest -> String -> Program -> Either CompilerError CheckedIR -> String -> IO (Maybe String)
samplerKey _ _ _ (Left _) _ = return Nothing
samplerKey m version p (Right env) rows = do
  h <- harnessFingerprint m
  src <- sourcesFingerprint m ["test/TestCorpus.hs"]
  i <- interpreterFingerprint m
  return $ Just $ hashKey [ version, h, src, i, show env, programRuntimeFields p, rows, show samplingTolerance ]

-- | The p(...) rows of a slice.
--
-- 'Impossible' rows (task tst-dim-unasserted-at-zero-probability) carry no
-- dim, so they are excluded from this pool rather than plumbed through as a
-- placeholder: every metamorphic property below that draws on 'expected'
-- already treats an actual-zero probability as carrying no dim information
-- (its own "a === 0 .||. d === outDim" checks), so those rows contributed
-- nothing to this pool's properties even when they were included.
probCasesOf :: [CorpusEntry] -> [CorpusProbCase]
probCasesOf = probCasesWhere (const True)

-- | The p() rows the empirical sampler check may use: a row marked
-- @no-sample@ is checked exactly everywhere but is left out here, since a
-- symmetric window over drawn samples averages the two sides of a support
-- edge or a jump.
sampledProbCasesOf :: [CorpusEntry] -> [CorpusProbCase]
sampledProbCasesOf = probCasesWhere (not . noSample)
  where noSample (ProbTestCase _ _ _ _ ns) = ns
        noSample _ = False

probCasesWhere :: (TestCase -> Bool) -> [CorpusEntry] -> [CorpusProbCase]
probCasesWhere keep es = [ (ceName e, (ceProgram e, queryPoint, params, (expectedProb e prob, dim)))
                 | e <- es, tc@(ProbTestCase _ queryPoint params (Possible prob dim _) _) <- ceCases e, keep tc ]

-- | The cdf(...) rows of the same slice, for the invariants that hold
-- of a CDF as much as of a point probability ('TopKNeverInflatesCdf').
cdfCasesOf :: [CorpusEntry] -> [CorpusProbCase]
cdfCasesOf es = [ (ceName e, (ceProgram e, queryPoint, params, (expectedProb e prob, dim)))
                | e <- es, CumulTestCase _ queryPoint params (Possible prob dim _) <- ceCases e ]

-- | A .tst probability expectation is always a float (the parser makes the
-- dim an 'Int'); anything else means the corpus parser handed us a malformed
-- row, which is a broken fixture rather than a property counterexample.
expectedProb :: CorpusEntry -> IRValue -> Double
expectedProb _ (VFloat out) = out
expectedProb e other = error ("malformed probability expectation in .tst corpus (" ++ ceName e ++ "): " ++ show other)

-- Corpus-driven metamorphic properties. Each property enumerates its whole
-- selected slice deterministically (interpreter-routed, non-neural prob/cdf
-- cases; see forAllNamedIn), so any failing case is surfaced on every run rather
-- than only when a random draw happens to select it. Each invariant:
--  * ValidPrograms: every program the End2End interpreter runs must pass validateProgram.
--  * SamplingMatchesPDF: the empirical frequency of forward samples estimates the
--    density each dim <= 1 row asserts, discrete shapes and ANY slots included
--    (one test per program, neural ones too).
--  * SamplesInSupport: a program with a dim >= 2 row draws only values its
--    probability variant gives a finite, positive density (one test per program).
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
-- | The sweeps keyed by impact analysis record their passes in @manifest@
-- (today 'Corpus.LogSpaceMatchesLinear', see 'logSpaceKey').
corpusTests :: Corpus -> Manifest -> IO TestTree
corpusTests corpus manifest = do
  ordinary <- corpusGroup ordinaryVariant corpus manifest
  slowTwin <- corpusGroup slowVariant corpus manifest
  return (testGroup "Tests" [ordinary, testGroup "Slow" [slowTwin]])

-- | Which programs a copy of the sweeps runs over, and under which tier.
data Variant = Variant
  { vPath   :: String       -- ^ the sweeps' path prefix
  , vGroup  :: String       -- ^ the tasty group holding them
  , vTier   :: Tier         -- ^ the tier of the sweeps that are 'Default' for ordinary programs
  , vHeader :: SlowHeader
  , vSelect :: CorpusEntry -> Bool
  }

ordinaryVariant :: Variant
ordinaryVariant = Variant "Corpus" "Corpus" Default SkipSlow corpusPoolEntry

-- | The same sweeps over the @slow@-headered programs (task
-- corpus-sweeps-slow-twin), the way End2End has a @(slow)@ twin. Every sweep
-- has one. No sweep leaves out 'slowForCompileCost': measured with those
-- programs excluded and included, the twin ran the same 405 programs in the
-- same time (about 62 s of tests), so the pool already drops them.
slowVariant :: Variant
slowVariant = Variant "Slow.Corpus (slow)" "Corpus (slow)" Slow OnlySlow
  corpusPoolEntry

corpusGroup :: Variant -> Corpus -> Manifest -> IO TestTree
corpusGroup Variant{vPath, vGroup, vTier, vHeader, vSelect} corpus manifest = fmap (localOption (QuickCheckMaxRatio 20) . testGroup vGroup) $ sequence
  [ corpusProperty SweepSpec
      { sweepName = vPath ++ ".ValidPrograms", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "every program the interpreter runs passes validateProgram" } $ \probPool _ ->
      testProperty "ValidPrograms" (forAllNamedIn probPool (\_ tc -> checkValidPrograms tc))
  -- dim 0 means the expectation refers to an atom, not a density: match drawn
  -- samples against it with a near-exact window (wide enough for float noise like
  -- 0.1+0.2, narrow enough to separate deliberately-close .tst atoms) instead of
  -- the density-estimation window. Discrete components (ints, bools, eithers,
  -- ADT constructors) match exactly and an ANY slot matches every draw, so a
  -- marginal row estimates the marginal. dim >= 2 rows are filtered out of the
  -- enumerated pool rather than discarded at test time -- conjoin treats a
  -- discard as "gave up", not as a pass. The hit probability of a window
  -- estimate scales with density * eps^dim, so reliable multivariate estimates
  -- need prohibitively many samples; 'SamplesInSupport' checks those programs'
  -- samplers instead. Unlike the other sweeps this one also takes the neural
  -- programs, their rows' mock envelopes shaped the way End2End shapes them
  -- (task generate-unchecked-against-density-outside-sampling-pool).
  , corpusSweepAll corpus SweepSpec
      { sweepName = vPath ++ ".SamplingMatchesPDF", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = samplerPoolEntry, sweepNote = "the empirical frequency of forward samples estimates the .tst density (rows marked no-sample excepted)" } $ \es -> return $
      let envs = samplerEnvs es
          name = vPath ++ ".SamplingMatchesPDF" in
      testGroup "SamplingMatchesPDF"
        [ testProperty n $ once $ cachedProperty manifest name n
            (samplerKey manifest samplingCheckVersion p (lookupCompiled envs n) (show groups))
            (case lookup n knownSamplerMismatches of
               Nothing -> ioProperty (conjoin . map rowProperty <$> runGroups envs n mayFail p groups)
               Just doc -> counterexample ("known sampler mismatch [" ++ doc ++ "] no longer observed -- \
                             \fixed? remove its knownSamplerMismatches entry") $ ioProperty $ do
                 vs <- runGroups envs n mayFail p groups
                 return (property (or [ True | (_, RowFail _) <- vs ])))
        | e <- map shapedEntry es
        , let n = ceName e
        , let p = ceProgram e
        , let mayFail = ceNoNormalization e
        , let groups = windowedRowGroups e
        , not (null groups) ]
  -- The dim >= 2 rows' sampler check: support agreement. Every draw the
  -- forward sampler makes must have a finite, positive density under the
  -- probability variant. It needs no window, so the dimension does not matter;
  -- what it cannot see is a sampler that puts the right support under the
  -- wrong weights.
  , corpusSweepAll corpus SweepSpec
      { sweepName = vPath ++ ".SamplesInSupport", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = samplerPoolEntry, sweepNote = "every forward sample of a program with a dim >= 2 row has a finite, positive density" } $ \es -> return $
      let envs = samplerEnvs es
          name = vPath ++ ".SamplesInSupport" in
      testGroup "SamplesInSupport"
        [ testProperty n $ once $ cachedProperty manifest name n
            (samplerKey manifest supportCheckVersion p (lookupCompiled envs n) (show paramLists))
            (conjoin [ counterexample ("at parameters " ++ show params)
                         (checkSamplesInSupport envs n (ceNoNormalization e) p params 200)
                     | params <- paramLists ])
        | e <- map shapedEntry es
        , let n = ceName e
        , let p = ceProgram e
        , let paramLists = supportCheckedParams e
        , not (null paramLists) ]
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".TopKInterprets", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "a topK 0.05 compile still answers every p() row" } $ \probPool _ ->
      testProperty "TopKInterprets" (forAllNamedIn probPool (checkTopKInterprets topK005Envs))
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".ProbWithBranchCounting", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "branch counting leaves (prob, dim) unchanged" } $ \probPool _ ->
      testProperty "ProbWithBranchCounting" (forAllNamedIn probPool (checkProbTestCasesWithBC bcEnvs))
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".MarginalAnyIsOne", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "P(ANY) = 1" } $ \probPool _ ->
      testProperty "MarginalAnyIsOne" (forAllNamedIn probPool (checkProbAny defaultEnvs))
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".TopKZeroThreshMatchesExact", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "topK at threshold 0 is exact inference" } $ \probPool _ ->
      testProperty "TopKZeroThreshMatchesExact" (forAllNamedIn probPool (checkTopKZeroMatchesExact topK0Envs defaultEnvs))
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".TopKNeverInflates", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "topK pruning never raises a p() row" } $ \probPool _ ->
      testProperty "TopKNeverInflates" (forAllNamedIn probPool (checkTopKNeverInflates topK01Envs defaultEnvs))
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".TopKNeverInflatesCdf", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "topK pruning never raises a cdf() row" } $ \_ cdfPool ->
      testProperty "TopKNeverInflatesCdf" (forAllNamedIn cdfPool (checkTopKNeverInflatesCdf topK01Envs defaultEnvs))
  -- task log-space-probability-computation: compiling with logSpace=True makes
  -- p()/cdf() return a log-probability instead of a linear one, so exp(actual)
  -- must reproduce the same corpus expectation as the linear compile. Over the
  -- whole pool: the set-valued-witness programs that used to be excluded here
  -- (their worlds were measured linear-pinned) are measured in the ambient
  -- semiring since task worlds-measure-unification. (The pool holds no neural
  -- program, so the plan engine's worlds are checked by End2End's
  -- PlanEngineLogSpaceMatchesLinear instead.)
  --
  -- One test per program rather than one property over the pool, so each
  -- program has a slot in the impact-analysis manifest: a program whose
  -- log-space compile and rows are unchanged since it last passed is skipped
  -- (docs-repo task impact-analysis-remaining-sweeps).
  , corpusSweepAll corpus SweepSpec
      { sweepName = vPath ++ ".LogSpaceMatchesLinear", sweepTier = vTier, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "exp of the log-space answer is the .tst expectation" } $ \es ->
      return $ testGroup "LogSpaceMatchesLinear"
        [ testProperty n $ once $ cachedProperty manifest (vPath ++ ".LogSpaceMatchesLinear") n
            (logSpaceKey manifest p (lookupCompiled logEnvs n) rows)
            (conjoin [ counterexample ("corpus case: " ++ n) (checkLogSpaceMatchesLinear logEnvs n tc) | tc <- rows ])
        | e <- es
        , let n = ceName e
        , let p = ceProgram e
        , let rows = map snd (probCasesOf [e])
        , not (null rows) ]
  -- task topk-logspace-unsound: logSpace combined with topK used to discard all
  -- probability mass (accProb/TOP_K_CUTOFF arithmetic was hardcoded linear, so
  -- every branch compared a log-probability against a linear threshold and was
  -- pruned unconditionally). Checked the same way LogSpaceMatchesLinear is --
  -- against the corresponding LINEAR topK compile at the same threshold, not
  -- against the (topK-off) .tst expectations, since topK is a real pruning
  -- optimisation whose own linear-mode result is the correct oracle here.
  -- Slow: the cutoff's log conversion is covered in the default suite by the
  -- "topK runtime cutoff" group; this is its corpus-wide version.
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".TopKLogSpaceMatchesLinear", sweepTier = Slow, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "log-space topK agrees with linear topK" } $ \probPool _ ->
      testProperty "TopKLogSpaceMatchesLinear"
      (forAllNamedIn probPool (checkTopKLogSpaceMatchesLinear topK005LogEnvs topK005Envs))
  -- task multi-path-recovery-unmaterialized-crash: the IROptimizer must not be
  -- load-bearing for whether a compiled probability function is even runnable.
  -- That ticket's second witness (`let x = Uniform in (x, x+x)`) crashed with
  -- "Variable ast4 not declared" at optimizerLevel 0 while answering correctly
  -- at the default 2 -- constant folding happened to delete the dangling
  -- chain-name reference before anything evaluated it, so the whole suite
  -- (which only ever compiles at the default level) stayed green over a real
  -- codegen defect. Comparing the two levels on the same corpus points closes
  -- that blind spot: the optimizer is a rewrite, so agreement is exact, not
  -- approximate. Slow: the -O0 corpus compile is a whole extra corpus compile
  -- spent on the optimizer alone.
  , corpusProperty SweepSpec
      { sweepName = vPath ++ ".UnoptimizedMatchesOptimized", sweepTier = Slow, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "-O0 answers exactly what -O2 answers" } $ \probPool _ ->
      testProperty "UnoptimizedMatchesOptimized"
      (forAllNamedIn probPool (checkUnoptimizedMatchesOptimized unoptEnvs defaultEnvs))
  -- task transformation-differential-testing-m1-config-differencing: does
  -- topK pruning depend on the order of commutative operands? Every pool
  -- program is compiled once more per commutative call site, its operands
  -- swapped ('commuteSites'), and both spellings answer their p() rows from
  -- one topK compile each at two runtime cutoffs. At threshold 0 pruning is
  -- off, so the two must agree exactly (a hard failure: a commutativity bug,
  -- not a topK one). At 0.1 they may not: an enumerated InjF guards each
  -- term on accProb * pLeft, never on pRight, so the left operand's marginal
  -- decides what is dropped (topk-pruning/topKOperandOrder pins the minimal
  -- case). Those divergences are by design of the current pruning rule and
  -- are logged, not failed -- 'TASTY_HIDE_SUCCESSES=false' shows them. Slow:
  -- one extra compile per site.
  , corpusSweepAll corpus SweepSpec
      { sweepName = vPath ++ ".TopKOperandOrder", sweepTier = Slow, sweepSlow = vHeader
      , sweepSelect = vSelect, sweepNote = "swapping a commutative call's operands changes nothing at threshold 0; logs what it changes at 0.1" } $ \es ->
      return $ testGroup "TopKOperandOrder"
        [ testCaseInfo n (checkTopKOperandOrder (lookup n knownOperandOrderDependent) (lookupCompiled topK005Envs n) p rows)
        | e <- es
        , let n = ceName e
        , let p = ceProgram e
        , let rows = [ (inp, params) | (_, inp, params, _) <- map snd (probCasesOf [e]) ]
        , not (null rows)
        , not (null (commuteSites p)) ]
  ]
  where
    -- Each property is its own sweep over the same slice, and sees that
    -- slice's p() and cdf() rows.
    corpusProperty spec prop = corpusSweepAll corpus spec $ \es ->
      return (prop (probCasesOf es) (cdfCasesOf es))
    -- The slice the sweeps above select ('SkipSlow', 'corpusPoolEntry').
    poolEntries = [ e | e <- corpusEntries corpus, ceSlow e == (vHeader == OnlySlow), vSelect e ]
    -- Compile each corpus program once per config, shared by every invariant and
    -- every .tst line drawn from that program (compile depends only on the pair,
    -- never on the queried sample/params).
    progs = uniqueCorpusPrograms (probCasesOf poolEntries ++ cdfCasesOf poolEntries)
    defaultEnvs = compileCorpusPrograms defaultCompilerConfig progs
    -- One topK compile answers every threshold: the cutoff is a runtime
    -- parameter, so 'withTopKCutoff' re-thresholds the shared compile instead
    -- of recompiling the corpus per threshold (task runtime-parametric-topk-threshold).
    topK005Envs = compileCorpusPrograms (topKConf 0.05) progs
    topK0Envs   = rethreshold 0.0 topK005Envs
    topK01Envs  = rethreshold 0.1 topK005Envs
    rethreshold t = Map.map (fmap (withTopKCutoff t))
    bcEnvs      = compileCorpusPrograms bcConf progs
    logEnvs     = compileCorpusPrograms (defaultCompilerConfig {logSpace = True}) progs
    topK005LogEnvs = compileCorpusPrograms (topKConf 0.05) {logSpace = True} progs
    unoptEnvs   = compileCorpusPrograms (defaultCompilerConfig {optimizerLevel = 0}) progs
    -- Enumerate the whole (filtered) pool deterministically so any failing corpus
    -- case surfaces on every run, rather than only when a random draw selects it.
    forAllNamedIn pool f = once $ conjoin [counterexample ("corpus case: " ++ n) (f n tc) | (n, tc) <- pool]
    -- The sampler sweeps also compile the neural programs the shared
    -- 'defaultEnvs' leaves out ('corpusPoolEntry').
    samplerEnvs es = Map.union defaultEnvs
      (compileCorpusPrograms defaultCompilerConfig
        [ (ceName e, ceProgram e) | e <- es, not (null (neurals (ceProgram e))) ])

-- | Bump when 'checkLogSpaceMatchesLinear' changes.
logSpaceCheckVersion :: String
logSpaceCheckVersion = "corpus-log-space-v1"

-- | Key of 'Corpus.LogSpaceMatchesLinear' on one program: its log-space
-- compile, its runtime fields, its p() rows (query point, parameters,
-- expectation) and the tolerance, with the interpreter fingerprint; this
-- module's source joins the harness. A refused compile has no key, so the
-- check runs (and fails, as it always did).
logSpaceKey :: Manifest -> Program -> Either CompilerError CheckedIR -> [(Program, IRValue, [IRValue], (Double, Int))] -> IO (Maybe String)
logSpaceKey _ _ (Left _) _ = return Nothing
logSpaceKey m p (Right env) rows = do
  h <- harnessFingerprint m
  src <- sourcesFingerprint m ["test/TestCorpus.hs"]
  i <- interpreterFingerprint m
  return $ Just $ hashKey
    [ logSpaceCheckVersion, h, src, i, show env, programRuntimeFields p
    , show [ (inp, params, expected) | (_, inp, params, expected) <- rows ], show probTolerance ]

checkValidPrograms :: (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkValidPrograms (p, _, _, _) = case validateProgram p of
  Right _ -> property True
  Left err -> counterexample err False

checkTopKInterprets :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkTopKInterprets envs n (p, inp, params, _) = ioProperty $ do
  let actualOutput = irDensityC envs n p params inp
  return $ actualOutput `reasonablyClose` actualOutput  -- No clue what the correct value should be here. Just test that is interprets to any value

-- Expected values in .tst files are rounded to ~4 digits, so compare with the
-- corpus-wide probTolerance (as the End2End checks do), and skip the dim check
-- for zero probability (a zero result carries no meaningful dimension).
checkProbTestCasesWithBC :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkProbTestCasesWithBC envs n (p, inp, params, expected) = ioProperty $ do
  let (out, outDim) = expected
  let actualOutput = irDensityC envs n p params inp
  case actualOutput of
    VProbDimBC a d _ -> return $
      counterexample (show a ++ "/=" ++ show out) (property $ abs (a - out) < probTolerance)
      .&&. (a === 0 .||. d === outDim)
    _ -> return $ counterexample "Return type was no tuple" False

checkLogSpaceMatchesLinear :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkLogSpaceMatchesLinear envs n (p, inp, params, expected) = ioProperty $ do
  let (out, outDim) = expected
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
checkTopKLogSpaceMatchesLinear :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
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
checkUnoptimizedMatchesOptimized :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
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

-- | Corpus programs known to answer differently at threshold 0.1 once a
-- commutative call's operands are swapped, each with its tracking document.
-- An entry whose program no longer diverges fails its test, so a fix to the
-- pruning rule cannot leave the list stale. A divergence on a program not
-- listed here is logged, not failed: pruning is lossy by design, and which
-- term it drops depending on operand order is the documented behaviour until
-- the tracking document changes the rule.
knownOperandOrderDependent :: [(String, String)]
knownOperandOrderDependent =
  [ ("topKOperandOrder", "topk-prunes-on-left-operand-marginal-only") ]

-- | One program's 'Corpus.TopKOperandOrder' check: per commutative site, the
-- swapped program's topK compile against the original's, at threshold 0
-- (must agree) and 0.1 (logged). A side that refuses, crashes or times out
-- is logged; there is nothing to compare.
checkTopKOperandOrder :: Maybe String -> Either CompilerError CheckedIR -> Program -> [(IRValue, [IRValue])] -> IO String
checkTopKOperandOrder known origCompiled p rows = do
  origAt <- mapM (\t -> answerAt p (Right =<< origCompiled) t) thresholds
  verdicts <- mapM (\(site, p') -> do
      c' <- timed (compile (topKConf 0.05) p')
      swappedAt <- mapM (answerAt p' c') thresholds
      return (site, judgeSite origAt swappedAt)) (commuteSites p)
  let hard = [ site ++ ": " ++ m | (site, Left m) <- verdicts ]
      logged = [ site ++ ": " ++ m | (site, Right (Just m)) <- verdicts ]
      orderDependent = any (\m -> "ORDER-DEPENDENT" `isPrefixOf` m) [ m | (_, Right (Just m)) <- verdicts ]
  if not (null hard)
    then assertFailure (unlines hard) >> return ""
    else if maybe False (const (not orderDependent)) known
    then assertFailure ("known operand-order dependence no longer observed -- fixed? remove its \
                        \knownOperandOrderDependent entry and update its .tst comment ["
                        ++ concat known ++ "]") >> return ""
    else return $ show (length verdicts) ++ " sites, " ++ show (length verdicts - length logged) ++ " agree"
           ++ concatMap ("\n    " ++) logged
  where
    thresholds = [0.0, 0.1]
    timed :: Either CompilerError CheckedIR -> IO (Either String CheckedIR)
    timed c = do
      r <- timeout (20 * 1000000) (try (evaluate c))
      return $ case r of
        Nothing -> Left "compile timeout (20s)"
        Just (Left ex) -> Left ("compile crash: " ++ firstLine (show (ex :: SomeException)))
        Just (Right (Left err)) -> Left ("refused: " ++ firstLine err)
        Just (Right (Right env)) -> Right env
    answerAt :: Program -> Either String CheckedIR -> Double -> IO (Either String [(Double, Int)])
    answerAt _ (Left why) _ = return (Left why)
    answerAt q (Right env) t = do
      let env' = withTopKCutoff t env
          one (s, params) = case runProbC q env' params s of
            Right (VProbDim pr d) -> Right (pr, d)
            Right v -> Left ("not a probability result: " ++ firstLine (show v))
            Left err -> Left ("refused: " ++ firstLine err)
          answers = mapM one rows
          force x = either length (\xs -> length [ () | (a, b) <- xs, a + fromIntegral b == a + fromIntegral b ]) x `seq` x
      r <- timeout (20 * 1000000) (try (evaluate (force answers)))
      return $ case r of
        Nothing -> Left "timeout (20s)"
        Just (Left ex) -> Left ("crash: " ++ firstLine (show (ex :: SomeException)))
        Just (Right x) -> x
    -- Left: a hard failure; Right Nothing: agrees; Right (Just m): logged.
    judgeSite [Right o0, Right o1] [Right s0, Right s1]
      | not (and (zipWith agreesPD o0 s0)) = Left ("threshold 0 disagrees: original " ++ show o0 ++ ", swapped " ++ show s0)
      | not (and (zipWith agreesPD o1 s1)) = Right (Just ("ORDER-DEPENDENT at 0.1: original " ++ show o1 ++ ", swapped " ++ show s1
                                                          ++ maybe "" (\d -> " [known: " ++ d ++ "]") known))
      | otherwise = Right Nothing
    judgeSite [Left why, _] _ = Right (Just ("original does not answer: " ++ why))
    judgeSite _ [Left why, _] = Right (Just ("swapped does not answer: " ++ why))
    judgeSite o s = Right (Just ("does not answer at 0.1: " ++ concat (take 1 [ w | Left w <- o ++ s ])))
    agreesPD (p1, d1) (p2, d2)
      | isNaN p1 || isNaN p2 = isNaN p1 && isNaN p2 && d1 == d2
      | p1 == 0 && p2 == 0 = True
      | otherwise = abs (p1 - p2) <= probTolerance * max 1 (abs p1) && d1 == d2
    firstLine m = let l = takeWhile (/= '\n') m in if length l > 160 then take 160 l ++ "..." else l

checkProbAny :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
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
type CompiledPrograms = Map.Map String (Either CompilerError CheckedIR)

uniqueCorpusPrograms :: [CorpusProbCase] -> [(String, Program)]
uniqueCorpusPrograms pool = nubBy ((==) `on` fst) [(n, p) | (n, (p, _, _, _)) <- pool]

compileCorpusPrograms :: CompilerConfig -> [(String, Program)] -> CompiledPrograms
compileCorpusPrograms conf progs = Map.fromList [(n, compile conf p) | (n, p) <- progs]

lookupCompiled :: CompiledPrograms -> String -> Either CompilerError CheckedIR
lookupCompiled envs n = fromMaybe (error ("no compiled entry for corpus program " ++ n)) (Map.lookup n envs)

irDensityC :: CompiledPrograms -> String -> Program -> [IRValue] -> IRValue -> IRValue
irDensityC envs n p params s = either error id (lookupCompiled envs n >>= \c -> runProbC p c params s)

irCumulativeC :: CompiledPrograms -> String -> Program -> [IRValue] -> IRValue -> IRValue
irCumulativeC envs n p params s = either error id (lookupCompiled envs n >>= \c -> runIntegC p c params s)

-- Does a drawn sample match the expected value? Float coordinate @i@
-- (numbered left to right over the value) is matched within the window
-- @tol i@ (maximum norm: @|a - e| <= w / 2@), or ignored when @tol i@ is
-- 'Nothing' -- see 'coordinateSubsets' for why ignoring one is ever the right
-- thing to do. Discrete components are matched exactly either way: they carry
-- no dimension, so they are never a coordinate to project onto. An ANY slot
-- matches anything.
sampleMatchesWith :: (Int -> Maybe Double) -> IRValue -> IRValue -> Bool
sampleMatchesWith tol expected actual = fst (go 0 expected actual)
  where
    go i (VFloat e) (VFloat a) = (maybe True (\w -> abs (a - e) <= w / 2) (tol i), i + 1)
    go i (VInt e) (VInt a) = (e == a, i)
    go i (VBool e) (VBool a) = (e == a, i)
    go i (VSymbol e) (VSymbol a) = (e == a, i)
    go i VUnit VUnit = (True, i)
    go i VAny _ = (True, i)
    go i (VEither (Left e)) (VEither (Left a)) = go i e a
    go i (VEither (Right e)) (VEither (Right a)) = go i e a
    go i (VADT ce es) (VADT ca as)
      | ce /= ca || length es /= length as = (False, i)
      | otherwise = foldl (\(ok, j) (ev, av) -> let (ok', j') = go j ev av in (ok && ok', j')) (True, i) (zip es as)
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
floatCoordCount (VEither e) = either floatCoordCount floatCoordCount e
floatCoordCount (VADT _ fs) = sum (map floatCoordCount fs)
floatCoordCount _ = 0

-- Which coordinate windows 'judgeSampledRow' should try, given the ambient
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
-- subset alone, and 'judgeSampledRow' accepts if ANY of them reproduces the
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
-- it drops exactly the coordinates that decide that -- so 'judgeSampledRow'
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
coordinateSubsets :: [Int] -> Int -> [Maybe [Int]]
coordinateSubsets coords dim
  | dim <= 0 || length coords <= dim = [Nothing]
  | otherwise = map Just (subsetsOfSize dim coords)

subsetsOfSize :: Int -> [a] -> [[a]]
subsetsOfSize 0 _ = [[]]
subsetsOfSize _ [] = []
subsetsOfSize k (x:xs) = map (x:) (subsetsOfSize (k - 1) xs) ++ subsetsOfSize k xs

-- | Can a window over drawn samples estimate this result at all? Only if the
-- reported dim does not exceed the query value's continuous coordinates. A
-- density needs as many continuous coordinates as it has dimensions to be a
-- density OVER the sample space; with fewer, it is the density of a
-- null-probability event of a continuous latent -- a point comparison like
-- @x == 0.0@ observed True, whose output is a discrete value (task
-- sampling-matches-pdf-continuous-equality-density: @draw x = Normal in if
-- x == 0.0 then 0 else 2@ answers @p(0) = (N(0), dim 1)@ by design). Almost no
-- sample lands on such an event, so the empirical estimate is 0 whatever the
-- density is: the comparison is a category error, not a weak check. A general
-- rule on the result's shape, not a list of programs.
densityLivesOnSamples :: IRValue -> Int -> Bool
densityLivesOnSamples inp d = d <= floatCoordCount inp

-- Shapes judgeSampledRow can estimate a PDF for; everything else is discarded.
-- Discrete leaves match a draw exactly, so they need no window; an ANY slot
-- matches every draw ('sampleMatchesWith'). Left out: a list with an ANY tail
-- (its length is open, and 'sampleMatchesWith' compares lengths), an ANY-except
-- slot, and the function, tensor and theta-tree values no row queries.
sampleable :: IRValue -> Bool
sampleable (VFloat _) = True
sampleable (VInt _) = True
sampleable (VBool _) = True
sampleable (VSymbol _) = True
sampleable VUnit = True
sampleable VAny = True
sampleable (VEither e) = either sampleable sampleable e
sampleable (VADT _ fs) = all sampleable fs
sampleable (VTuple a b) = sampleable a && sampleable b
sampleable (VList l) = closedList l && all sampleable l
  where closedList EmptyList = True
        closedList (ListCont _ xs) = closedList xs
        closedList AnyList = False
sampleable _ = False

-- | 'SamplesInSupport' on one parameter list: draw @samples@ values from the
-- forward sampler and require each to have a finite, positive density under
-- the probability variant. A sampler that leaves the support (a wrong branch,
-- an off-by-one constructor, a mis-shifted latent) fails at the first draw
-- the density calls impossible.
checkSamplesInSupport :: CompiledPrograms -> String -> Bool -> Program -> [IRValue] -> Int -> Property
checkSamplesInSupport envs n mayFail p params samples = ioProperty $ do
  let compiledEnv = either error id (lookupCompiled envs n)
  Draws _ drawn raised <- drawSamples envs n p params samples
  let judge s = case runProbC p compiledEnv params s of
        Right (VProbDim pr _) | pr > 0 && not (isInfinite pr) && not (isNaN pr) -> Nothing
        Right r -> Just (show s ++ " has density " ++ show r)
        Left err -> Just (show s ++ ": " ++ err)
      bad = [ "the sampler raised: " ++ r | r <- raised, not mayFail ] ++ [ m | Just m <- map judge drawn ]
  return $ if null bad then property True
    else counterexample (show (length bad) ++ " of " ++ show samples ++ " draws outside the support, e.g. "
                         ++ unlines (take 3 bad)) False

-- | The window an atom is matched in: wide enough for float noise like
-- 0.1+0.2, narrow enough to separate deliberately-close .tst atoms.
atomWindow :: Double
atomWindow = 1e-9

-- | What 'SamplingMatchesPDF' made of one row.
data RowVerdict = RowPass | RowSkip String | RowFail String

-- | Draws from a program's sampler at one parameter list: how many were
-- attempted, the values, and the messages of the ones that raised.
data Draws = Draws Int [IRValue] [String]

-- | Draw @k@ values. Each draw gets its own generator, so a draw that raises
-- costs only itself.
drawSamples :: CompiledPrograms -> String -> Program -> [IRValue] -> Int -> IO Draws
drawSamples envs n p params k = do
  let compiledEnv = either error id (lookupCompiled envs n)
  attempts <- replicateM k (try (evaluate . forceValue =<< evalRandIO (runGenC p compiledEnv params)))
  return (Draws k [ v | Right v <- attempts ] [ takeWhile (/= '\n') (show (e :: SomeException)) | Left e <- attempts ])

-- | Sample PDF against expected PDF, for every row of one program at one
-- parameter list: the rows share their draws, and the rows that miss are
-- retried on twice as many fresh draws, up to five times. On a
-- @no-normalization@ program (@mayFail@) a raising draw is the program's
-- failure mass and falls in no window, which is what a sub-probability's
-- estimate needs; anywhere else it fails the row.
samplingRows :: CompiledPrograms -> String -> Bool -> Program -> [IRValue] -> [(IRValue, (Double, Int))] -> IO [((IRValue, (Double, Int)), RowVerdict)]
samplingRows envs n mayFail p params = go 1000 (5 :: Int)
  where
    go k retries pending = do
      ds <- drawSamples envs n p params k
      let verdicts = [ (r, judgeSampledRow mayFail ds r) | r <- pending ]
          missed = [ r | (r, RowFail _) <- verdicts ]
      if null missed || retries == 0
        then return verdicts
        else do
          retried <- go (k * 2) (retries - 1) missed
          return ([ v | v@(_, verdict) <- verdicts, not (isRowFail verdict) ] ++ retried)
    isRowFail (RowFail _) = True
    isRowFail _ = False

-- | One row against a set of draws.
--
-- Which float coordinates are continuous is read off the draws: one some draw
-- hits exactly ('atomWindow') is an atom at the query, matched exactly and
-- carrying no dimension (the 1.0 of @((0.0, ANY), 1.0)@ on
-- @(e, if snd e then 1.0 else 2.0)@). The windows range over the rest. When
-- the reported dim exceeds the continuous coordinates left, the result is the
-- density of a null event -- the 'densityLivesOnSamples' category error, seen
-- here only once an atom is recognised (@(0.0, v0 == 1.0)@ at @(0.0, True)@)
-- -- and the row is passed with a label rather than estimated.
judgeSampledRow :: Bool -> Draws -> (IRValue, (Double, Int)) -> RowVerdict
judgeSampledRow mayFail (Draws samples drawn raised) (inp, (out, outDim))
  | not (sampleable inp) = RowFail ("not a sampleable query: " ++ show inp)
  | not (null raised) && not mayFail =
      RowFail ("the sampler raised on " ++ show (length raised) ++ " of " ++ show samples ++ " draws: " ++ head raised)
  | outDim > length continuous && out > 0 = RowSkip "density of a null event"
  | any (\e -> abs (e - out) <= samplingTolerance) estimates = RowPass
  | atBoundary = RowSkip "point on a support boundary or density jump"
  | otherwise = RowFail ("Sampled PDF is: " ++ show estimates ++ ", but should be: " ++ show out
                         ++ " (" ++ show samples ++ " draws)")
  where
    epsilon = if outDim == 0 then atomWindow else 0.05
    -- A one-coordinate window straddling a support edge or a jump estimates the
    -- average of its two sides. The two half windows tell: draws matching the
    -- discrete part, on each side of the point, differ sharply (one may be
    -- empty). Only consulted once the estimate has missed.
    atBoundary = case (outDim, continuous) of
      (1, [c]) ->
        let e = fromMaybe 0 (lookup c queried)
            offsets = [ a - e | d <- drawn, sampleMatchesWith (const Nothing) inp d
                              , Just a <- [lookup c (floatCoordValues inp d)] ]
            lft = length [ o | o <- offsets, o < 0, o >= negate (epsilon / 2) ]
            rgt = length [ o | o <- offsets, o > 0, o <= epsilon / 2 ]
        in max lft rgt >= 10 && 3 * min lft rgt < max lft rgt
      _ -> False
    queried = floatCoordValues inp inp
    atomic = [ i | (i, e) <- queried
                 , any (\d -> any (\(j, a) -> j == i && abs (a - e) <= atomWindow / 2) (floatCoordValues inp d)) drawn ]
    continuous = filter (`notElem` atomic) (map fst queried)
    -- The maximum norm creates an outDim-dimensional hypercube of volume
    -- epsilon^outDim; for purely discrete samples outDim is 0 and no
    -- division happens. One estimate per candidate coordinate window -- a
    -- single all-coordinate one unless the support is a lower-dimensional
    -- manifold, see 'coordinateSubsets'.
    tolOn :: Maybe [Int] -> Int -> Maybe Double
    tolOn sel i
      | i `elem` atomic = Just atomWindow
      | maybe True (i `elem`) sel = Just epsilon
      | otherwise = Nothing
    estimateOn sel =
      let countInside = length (filter (sampleMatchesWith (tolOn sel) inp) drawn)
          ratioInside = fromIntegral countInside / fromIntegral samples
      in ratioInside / (epsilon ^ outDim)
    windows = coordinateSubsets continuous outDim
    -- On a manifold the ambient window no longer carries the measure, so it
    -- serves as the support test instead: no draw inside it means the query is
    -- off-support and the density is 0. Where the ambient window IS the only
    -- window (full-dimensional support) this is subsumed -- an empty window
    -- already estimates 0 -- so the branch changes nothing there.
    onSupport = windows == [Nothing] || any (sampleMatchesWith (tolOn Nothing) inp) drawn
    estimates = if onSupport then map estimateOn windows else [0 :: Double]

-- | A draw's float coordinates, numbered as the query numbers them, wherever
-- the draw's shape follows the query's (the same constructor, branch and list
-- length down to the coordinate). Discrete leaves are not compared: this is
-- what each coordinate is, whatever the rest of the draw holds.
floatCoordValues :: IRValue -> IRValue -> [(Int, Double)]
floatCoordValues query draw = fst (go 0 query draw)
  where
    go i (VFloat _) (VFloat a) = ([(i, a)], i + 1)
    go i (VFloat _) _ = ([], i + 1)
    go i (VEither (Left e)) (VEither (Left a)) = go i e a
    go i (VEither (Right e)) (VEither (Right a)) = go i e a
    go i (VADT ce es) (VADT ca as) | ce == ca && length es == length as = many i (zip es as)
    go i (VTuple e1 e2) (VTuple a1 a2) = many i [(e1, a1), (e2, a2)]
    go i (VList e) (VList a) | length (toList e) == length (toList a) = many i (zip (toList e) (toList a))
    go i e _ = ([], i + floatCoordCount e)
    many i = foldl (\(acc, j) (e, a) -> let (xs, j') = go j e a in (acc ++ xs, j')) ([], i)

-- | Force a drawn value all the way down, so a draw that raises does so
-- inside the 'try' that is waiting for it.
forceValue :: IRValue -> IRValue
forceValue v = length (show v) `seq` v

-- Threshold=0 never prunes any branch, so results must match exact inference.
checkTopKZeroMatchesExact :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkTopKZeroMatchesExact topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  case (topKResult, exactResult) of
    (VProbDim topKP topKD, VProbDim exactP exactD) ->
      return $ VFloat topKP `reasonablyClose` VFloat exactP
          .&&. topKD === exactD
    _ -> return $ counterexample "Return type was no tuple" False

-- Pruning can only zero out branches, never inflate probability above the exact value.
checkTopKNeverInflates :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
checkTopKNeverInflates topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  return (topKNeverInflates topKResult exactResult)

-- | The CDF half of 'checkTopKNeverInflates' (task
-- topk-inflates-probability-int-comparison-mix): a CDF is a probability too,
-- and the cumulative path has its own complement site (the change-of-variables
-- flip under a decreasing inverse, 'scaleCoV') that the point-query pool never
-- exercises -- 'topKComplementCdfFlip' is its canary.
checkTopKNeverInflatesCdf :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (Double, Int)) -> Property
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
