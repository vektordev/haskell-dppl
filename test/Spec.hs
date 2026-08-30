{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck hiding (verbose)
import Test.Tasty (TestTree, testGroup, defaultMain, localOption)
import Test.Tasty.QuickCheck (testProperty, testProperties, QuickCheckMaxRatio(..))
import System.Environment (lookupEnv, setEnv)
import System.FilePath (takeBaseName)
import Data.Maybe (isNothing, fromMaybe)

import SPLL.Examples
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Validator
import Control.Monad.Random.Lazy (evalRandIO, replicateM)
import Data.Foldable
import SPLL.Parser
import TestParser (parserTests)
import TestInternals (internalsTests, slowInternalsTests)
import TestRejection (rejectionTests)
import TestModality (modalityTests)
import TestModalityInfer (modalityInferTests)
import TestDeterminism (determinismTests)
import TestEncodeProperties (encodeTests, encodeRoundtripTests)
import TestShowcase (showcaseTests)
import End2EndTesting (end2endTests, slowEnd2EndTests, getAllTestFiles, selectPassDifferentialTests, batchedPythonTests, slowBatchedPythonTests, batchedRefusalTests, branchCountBackendTests)
import TestFuzz (fuzzTests, superSlowFuzzTests)
import TestCaseParser (parseProgram, parseTestCases, TestCase(..), Backend(..))
import TestTolerances (probTolerance, reasonablyCloseTolerance, samplingTolerance)
import SPLL.Prelude
import qualified SPLL.CodeGenPyTorch
import qualified SPLL.CodeGenJulia
import Data.List (isInfixOf, nubBy)
import Data.Function (on)
import qualified Data.Map.Strict as Map


normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

-- The expected-value tables that used to live here have moved into the
-- testCases/*.ppl + *.tst corpus (see the End2End groups). The metamorphic
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
    (backends, _slow, tcs) <- parseTestCases tst
    return (takeBaseName ppl, prog, backends, tcs)) files
  let usable = [(n, p, tcs) | (n, p, backends, tcs) <- pairs, Interpreter `elem` backends, null (neurals p)]
  return [(n, (p, queryPoint, params, expected)) | (n, p, tcs) <- usable, ProbTestCase _ queryPoint params expected _ <- tcs]

-- | A .tst probability expectation is always a (prob, dim) pair of floats;
-- anything else means the corpus parser handed us a malformed row, which is a
-- broken fixture rather than a property counterexample.
expectedProbDim :: (IRValue, IRValue) -> (Double, Double)
expectedProbDim (VFloat out, VFloat outDim) = (out, outDim)
expectedProbDim other = error ("malformed probability expectation in .tst corpus: " ++ show other)

-- | A compile the test asserts must succeed. Failing here is a broken fixture,
-- so surface the compiler's own message instead of a pattern-match panic.
expectCompiled :: Either CompilerError IREnv -> IREnv
expectCompiled (Right env) = env
expectCompiled (Left err)  = error ("test fixture failed to compile: " ++ show err)

invalidTestCases :: [Program]
invalidTestCases = [invalidDuplicateDecl1, invalidDuplicateDecl2, invalidDuplicateDecl3, invalidDuplicateDecl4, invalidDuplicateDecl5, invalidMissingDecl, invalidMissingInjF, invalidReservedName, invalidReservedName2, invalidWrongArgCount]

prop_CheckInvalidPrograms :: Property
prop_CheckInvalidPrograms = forAll (elements invalidTestCases) checkInvalidPrograms

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
corpusTests :: [CorpusProbCase] -> TestTree
corpusTests probPool = localOption (QuickCheckMaxRatio 20) $ testGroup "Corpus"
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
  ]
  where
    -- Compile each corpus program once per config, shared by every invariant and
    -- every .tst line drawn from that program (compile depends only on the pair,
    -- never on the queried sample/params).
    progs = uniqueCorpusPrograms probPool
    defaultEnvs = compileCorpusPrograms defaultCompilerConfig progs
    topK005Envs = compileCorpusPrograms (topKConf 0.05) progs
    topK0Envs   = compileCorpusPrograms (topKConf 0.0) progs
    topK01Envs  = compileCorpusPrograms (topKConf 0.1) progs
    bcEnvs      = compileCorpusPrograms bcConf progs
    logEnvs     = compileCorpusPrograms (defaultCompilerConfig {logSpace = True}) progs
    topK005LogEnvs = compileCorpusPrograms (topKConf 0.05) {logSpace = True} progs
    -- Enumerate the whole (filtered) pool deterministically so any failing corpus
    -- case surfaces on every run, rather than only when a random draw selects it.
    forAllNamedIn pool f = once $ conjoin [counterexample ("corpus case: " ++ n) (f n tc) | (n, tc) <- pool]
    forAllNamed = forAllNamedIn probPool
    samplingEps outDim = if outDim == VFloat 0 then 1e-9 else 0.05

prop_TopK :: Property
prop_TopK = once $ ioProperty $ do
  let actualOutput0 = irDensity (topKConf 0.1) testTopK (VFloat 0) []
  let actualOutput1 = irDensity (topKConf 0.1) testTopK (VFloat 1) []
  case (actualOutput0, actualOutput1) of
    (VProbDim a _, VProbDim b _) -> return $ (b == 0.95) && (a == 0)
    _ -> return False

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing1 :: Property
prop_CheckReadmeCodeListing1 = ioProperty $ do
  let twoDice = Program [("main", dice 6 #<+># dice 6)] [] [] []
  case runGen defaultCompilerConfig twoDice [] of
    Left err -> return $ counterexample err False
    Right gen' -> do
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig twoDice [] gen of
        Left err -> return $ counterexample err False
        Right (VProbDim prob _dim) -> do
          -- Original Listing above, Tests below
          if gen == (VInt 2) || gen == (VInt 12) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 1/36)
          else if gen == (VInt 3) || gen == (VInt 11) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 2/36)
          else if gen == (VInt 4) || gen == (VInt 10) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 3/36)
          else if gen == (VInt 5) || gen == (VInt 9) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 4/36)
          else if gen == (VInt 6) || gen == (VInt 8) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 5/36)
          else if gen == (VInt 7) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 6/36)
          else
            return $ counterexample ("No valid dice roll " ++ show gen) False
        Right other -> return $ counterexample ("probability query returned " ++ show other
                                                 ++ ", not a (prob, dim) pair") False

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing2 :: Property
prop_CheckReadmeCodeListing2 = ioProperty $ do
  let dist = Program [("main", normal #*# constF 2 #+# constF 1)] [] [] []
  case runGen defaultCompilerConfig dist [] of
    Left err -> return $ counterexample err False
    Right gen' -> do 
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig dist [] gen of
        Left err -> return $ counterexample err False
        Right (VProbDim prob _dim) -> case gen of
          -- Original Listing above, Tests below
          VFloat genF ->
            return $ (VFloat prob) `reasonablyClose` (VFloat (normalPDF ((genF - 1) / 2) / 2))
          other -> return $ counterexample ("expected a float sample, got " ++ show other) False
        Right other -> return $ counterexample ("probability query returned " ++ show other
                                                 ++ ", not a (prob, dim) pair") False

checkValidPrograms :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkValidPrograms (p, _, _, _) = case validateProgram p of
  Right _ -> property True
  Left err -> counterexample err False

checkInvalidPrograms :: Program -> Property
checkInvalidPrograms p = case validateProgram p of
  Left _ -> property True
  Right _ -> counterexample "Program validates even though it should not" False


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
  , "observeTwoSidedInterval"
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

checkProbAny :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbAny envs n (p, _, params, _) = ioProperty $ do
  let actualOutput = irDensityC envs n p params VAny
  case actualOutput of
    VProbDim a _ -> return $ VFloat a `reasonablyClose` VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False

-- All test compilation goes through the public SPLL.Prelude entry points, so the
-- tests exercise exactly the pipeline production uses. The CompilerConfig argument
-- selects the topK / branch-counting variants.
topKConf :: Double -> CompilerConfig
topKConf thresh = defaultCompilerConfig {topKThreshold = Just thresh}

topKBCConf :: Double -> CompilerConfig
topKBCConf thresh = (topKConf thresh) {countBranches = True}

bcConf :: CompilerConfig
bcConf = defaultCompilerConfig {countBranches = True}

irDensity :: CompilerConfig -> Program -> IRValue -> [IRValue] -> IRValue
irDensity conf p s params = either error id $ runProb conf p params s

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

reasonablyClose :: IRValue -> IRValue -> Property
reasonablyClose (VFloat a) (VFloat b) = counterexample (show a ++ "/=" ++ show b) (property $ abs (a - b) <= reasonablyCloseTolerance)
reasonablyClose a b = a === b

-- Does a drawn sample match the expected value, within an epsilon-wide window
-- (maximum norm) on continuous components and exactly on discrete ones?
sampleMatches :: Double -> IRValue -> IRValue -> Bool
sampleMatches epsilon (VFloat expected) (VFloat actual) = abs (actual - expected) <= epsilon / 2
sampleMatches _ (VInt expected) (VInt actual) = expected == actual
sampleMatches epsilon (VTuple e1 e2) (VTuple a1 a2) = sampleMatches epsilon e1 a1 && sampleMatches epsilon e2 a2
sampleMatches epsilon (VList expected) (VList actual) =
  length es == length as && and (zipWith (sampleMatches epsilon) es as)
  where (es, as) = (toList expected, toList actual)
sampleMatches _ _ _ = False

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
    let countInside = length (filter (sampleMatches epsilon inp) drawn)
    let ratioInside = fromIntegral countInside / fromIntegral samples
    -- The maximum norm creates an outDim-dimensional hypercube of volume
    -- epsilon^outDim; for purely discrete samples outDim is 0 and no division happens.
    let estimatePDF = ratioInside / (epsilon ** outDim)
    let valid = abs (estimatePDF - out) <= samplingTolerance
    if valid then
      return $ property True
    else
      if retries > 0 then
        return $ testSamplingProb envs n epsilon (samples * 2) (retries - 1) tc
      else
        return $ counterexample ("Sampled PDF is: " ++ show estimatePDF ++ ", but should be: " ++ show out) (property valid)
testSamplingProb _ _ _ _ _ _ = False ==> False

-- Two-level nesting: inner true branch has global prob 0.12*0.12=0.0144 < thresh=0.1, so it is
-- pruned by global topK but would survive local topK (local condT=0.12 > 0.1).
prop_TopKNestedPrunesDeeper :: Property
prop_TopKNestedPrunesDeeper = once $ ioProperty $ do
  let twoLevel = Program [("main",
        ifThenElse (bernoulli 0.12)
          (ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0))
          (constF 2.0))] [] [] []
  let topKResult = irDensity (topKConf 0.1) twoLevel (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig twoLevel (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (VFloat exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Cross-function: accProb passes through a _prob call boundary.
-- main = if bernoulli(0.12) then inner else 2.0
-- inner = if bernoulli(0.12) then 1.0 else 0.0
-- With thresh=0.1: main's true branch has accProb=0.12, inner receives it;
-- inner's true branch has global prob 0.12*0.12=0.0144 < 0.1 → pruned, P(1.0)=0.
prop_TopKCrossFunction :: Property
prop_TopKCrossFunction = once $ ioProperty $ do
  let crossFunc = Program
        [ ("main",  ifThenElse (bernoulli 0.12) (var "inner") (constF 2.0))
        , ("inner", ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0)) ]
        [] [] []
  let topKResult = irDensity (topKConf 0.1) crossFunc (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig crossFunc (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (VFloat exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

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
  case (topKResult, exactResult) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ counterexample (show topKP ++ " > " ++ show exactP) (topKP <= exactP + 1e-9)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC counts both if-else leaf branches and InjF enumerable branches.
-- testDiceAdd = plusI(dice6, dice6): for P(sum=7), all 6 die combinations are valid,
-- so without topK BC=6.  With threshold=0.2 (>1/6), accProb*(1/6)<0.2 → all 6 pruned → BC=0.
prop_TopKFewerBranches :: Property
prop_TopKFewerBranches = once $ ioProperty $ do
  let topKBCResult = irDensity (topKBCConf 0.2) testDiceAdd (VInt 7) []
  let noBCResult   = irDensity bcConf           testDiceAdd (VInt 7) []
  case (topKBCResult, noBCResult) of
    (VProbDimBC _ _ topKBC, VProbDimBC _ _ noBC) ->
      return $ counterexample (show topKBC ++ " >= " ++ show noBC ++ " (topK should reduce branch count when a branch is pruned)") (topKBC < noBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- Higher threshold prunes more InjF enum branches: BC(high_thresh) ≤ BC(low_thresh).
-- testDiceAdd at P(sum=7): each d6 face has P=1/6.
--   threshold=0.1 (<1/6): accProb*(1/6)>0.1 → all 6 branches kept → BC=6
--   threshold=0.2 (>1/6): accProb*(1/6)<0.2 → all 6 branches pruned → BC=0
prop_TopKMonotonicBranches :: Property
prop_TopKMonotonicBranches = once $ ioProperty $ do
  let bcLow  = irDensity (topKBCConf 0.1) testDiceAdd (VInt 7) []
  let bcHigh = irDensity (topKBCConf 0.2) testDiceAdd (VInt 7) []
  case (bcLow, bcHigh) of
    (VProbDimBC _ _ lowBC, VProbDimBC _ _ highBC) ->
      return $ counterexample (show highBC ++ " > " ++ show lowBC ++ " (higher threshold should prune at least as much)") (highBC <= lowBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC for if-else: each leaf emits 1, IfThenElse uses formula cond+left+right-1.
-- A 3-leaf if-else (if b then (if b2 then uniform else 3.0) else 1.0) should give BC=3.
-- inner: cond(1)+uniform(1)+const3(1)-1=2; outer: cond(1)+2+const1(1)-1=3.
prop_BCLeafCountIfElse :: Property
prop_BCLeafCountIfElse = once $ ioProperty $ do
  let prog = Program [("main", ifThenElse (bernoulli 0.5) (ifThenElse (bernoulli 0.5) uniform (constF 3.0)) (constF 1.0))] [] [] []
  let result = irDensity bcConf prog (VFloat 0.5) []
  case result of
    VProbDimBC _ _ bc -> return $ counterexample ("Expected BC=3, got " ++ show bc) (bc == 3.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 is a pure if-else tree with 6 leaves. BC should equal 6 for any query.
-- dice1=1; dice(n)=cond(1)+constI(n)(1)+dice(n-1)-1 = dice(n-1)+1; so dice(6)=6.
prop_BCDiceIfElse :: Property
prop_BCDiceIfElse = once $ ioProperty $ do
  let result = irDensity bcConf testDice (VInt 3) []
  case result of
    VProbDimBC _ _ bc -> return $ counterexample ("Expected BC=6, got " ++ show bc) (bc == 6.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Consistency: dice6 as if-else (BC=6) and testDiceAdd as InjF (BC=6 for P(7)) agree.
prop_BCConsistency :: Property
prop_BCConsistency = once $ ioProperty $ do
  let diceResult    = irDensity bcConf testDice    (VInt 3) []
  let diceAddResult = irDensity bcConf testDiceAdd (VInt 7) []
  case (diceResult, diceAddResult) of
    (VProbDimBC _ _ diceBC, VProbDimBC _ _ diceAddBC) ->
      return $ counterexample ("dice BC=" ++ show diceBC ++ ", diceAdd BC=" ++ show diceAddBC ++ " (expected both=6)") (diceBC == diceAddBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- Leaf-anchor consistency (task bc-recursive-prob-divergence). Branch count is
-- anchored on "every terminal leaf resolution counts 1, deterministic or
-- random", so the same deterministic value carried into the same branch
-- position must produce the same count regardless of which AST constructor
-- spells it. These three programs are the same distribution, reached through
-- three different toIRInference leaf cases:
--   x          -- Var-is-a-local-variable
--   x + 0.0    -- InjF with no probabilistic parameter
--   ident x    -- deterministic Apply (closure applied to a deterministic arg)
-- All three must agree AND equal 2 (one leaf per if-arm: the leaf under test,
-- plus the constant 3.0 in the else). The absolute value is pinned as well as
-- the agreement because before the fix all three sites returned 0 branches --
-- they agreed with each other at BC=1 (the outer if's condition alone, via the
-- old cond+left+right-1 formula) while every one of them was wrong.
prop_BCLeafSpellingIndependence :: Property
prop_BCLeafSpellingIndependence = once $ ioProperty $ do
  let srcs = [ ("bare Var",              "f x = if Uniform < 0.5 then x else 3.0\nmain = f 2.0")
             , ("InjF, no prob param",   "f x = if Uniform < 0.5 then x + 0.0 else 3.0\nmain = f 2.0")
             , ("deterministic Apply",   "ident y = y\nf x = if Uniform < 0.5 then ident x else 3.0\nmain = f 2.0") ]
  return $ conjoin
    [ case tryParseProgram lbl src of
        Left err -> counterexample ("parse failed for " ++ lbl ++ ": " ++ show err) False
        Right prog -> case irDensity bcConf prog (VFloat 2.0) [] of
          VProbDimBC _ _ bc -> counterexample (lbl ++ ": expected BC=2, got " ++ show bc) (bc == 2.0)
          x -> counterexample (lbl ++ ": unexpected result shape: " ++ show x) False
    | (lbl, src) <- srcs ]

-- Recursion-depth fidelity (task bc-recursive-prob-divergence). testCases/dice.ppl
-- is genuinely self-recursive (dice x = ... else dice (x-1), from dice 4.0), unlike
-- the dice 6 builder above which is a Haskell-side unrolled if-tree. Its branch
-- count must be exactly the recursion depth, 4 -- one leaf resolution per level --
-- and independent of the queried value, since only the recursion-control conditions
-- (x == 1.0, Uniform < 1/x) decide which paths are dead, never the sample. Two
-- separate bugs used to show up right here: the count diverged outright (the dead
-- arm's recursive call was evaluated strictly, so x counted down past 1.0 forever),
-- and once that was fixed it collapsed to a constant 1.0 (every level's leaf was a
-- bare Var, which contributed 0). 5.0 is out of support: probability 0, but the
-- compiled artifact still traverses the same 4 leaves.
prop_BCRecursiveDiceDepth :: Property
prop_BCRecursiveDiceDepth = once $ ioProperty $ do
  prog <- parseProgram "testCases/dice.ppl"
  return $ conjoin
    [ case irDensity bcConf prog (VFloat v) [] of
        VProbDimBC _ _ bc -> counterexample ("p(" ++ show v ++ "): expected BC=4, got " ++ show bc) (bc == 4.0)
        x -> counterexample ("p(" ++ show v ++ "): unexpected result shape: " ++ show x) False
    | v <- [1.0, 2.0, 3.0, 4.0, 5.0] ]

-- dice 6 has equal 1/6 marginal probability per face regardless of tree structure.
-- Global topK therefore either prunes all branches or none:
--   threshold=0.1 (<1/6): accumulated prob of every branch is ~1/6 > 0.1 → nothing pruned, P(3)=1/6
--   threshold=0.2 (>1/6): accumulated prob of every branch is ~1/6 < 0.2 → all pruned, P(3)=0
-- Local topK would behave differently because the raw bernoulli probabilities vary by depth.
prop_TopKDiceAllOrNothing :: Property
prop_TopKDiceAllOrNothing = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDice (VInt 3) []
  let high  = irDensity (topKConf 0.2)        testDice (VInt 3) []
  let exact = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (low, high, exact) of
    (VProbDim lowP _, VProbDim hP _, VProbDim exactP _) ->
      return $ VFloat lowP `reasonablyClose` VFloat exactP
            .&&. counterexample ("threshold=0.2 should prune all branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- testDiceAdd = plusI(dice, dice): InjF enumerates discrete values of the left arg.
-- Each d6 face has P=1/6; InjF branch filter is (accProb * pLeft > threshold).
--   threshold=0.1 (<1/6): 1.0*(1/6)=0.167 > 0.1 → all enum branches kept, P(7)=6/36
--   threshold=0.2 (>1/6): 1.0*(1/6)=0.167 < 0.2 → all enum branches pruned, P(7)=0
prop_TopKInjFEnum :: Property
prop_TopKInjFEnum = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDiceAdd (VInt 7) []
  let high  = irDensity (topKConf 0.2)        testDiceAdd (VInt 7) []
  let exact = irDensity defaultCompilerConfig testDiceAdd (VInt 7) []
  case (low, high, exact) of
    (VProbDim lowP _, VProbDim hP _, VProbDim exactP _) ->
      return $ VFloat lowP `reasonablyClose` VFloat exactP
            .&&. counterexample ("threshold=0.2 should prune all InjF enum branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Parses testCases/dice.ppl (d4, equal P=0.25 per face) and runs it through the full
-- parsing + compilation pipeline with topK enabled, via the public runProb API
-- (which threads the initial acc_prob for topK-compiled programs).
-- threshold=0.1 (<0.25): no branch is pruned; each face should have P=0.25.
prop_TopKEndToEnd :: Property
prop_TopKEndToEnd = once $ ioProperty $ do
  prog <- parseProgram "testCases/dice.ppl"
  let results = map (\v -> irDensity (topKConf 0.1) prog (VFloat v) []) [1.0, 2.0, 3.0, 4.0]
  return $ conjoin
    [ case r of
        VProbDim p _ -> VFloat p `reasonablyClose` VFloat 0.25
        x -> counterexample ("Unexpected result shape: " ++ show x) False
    | r <- results ]

-- testConditionalLambdaBC: named deterministic selector applied to a coin-flip argument.
-- Routes through IsConditional + toIREnumerate path in IRCompiler.
-- Argument has 2 discrete values; each iteration traverses one if-else arm → BC = 2.
prop_BCConditionalLambda :: Property
prop_BCConditionalLambda = once $ ioProperty $ do
  let result = irDensity bcConf testConditionalLambdaBC (VFloat 1.0) []
  case result of
    VProbDimBC _ _ bc ->
      return $ counterexample ("Expected BC=2, got " ++ show bc) (bc == 2.0)
    _ -> return $ counterexample ("Unexpected result shape: " ++ show result) False

-- killAll coverage: a program that calls a sub-function via Var with a non-trivial
-- change-of-variables correction.  testNormalScaledViaVar uses injF "mult" with factor
-- 2.0, whose inverse derivative is 1/2.  If killAll fails to rewrite the dim extraction
-- from the sub-function result (IRTFst(IRTSnd(IRVar x)) → IRTSnd(IRVar x)), dim would
-- be 0 and the CoV factor would be skipped, giving normalPDF(1.0) instead of
-- the correct normalPDF(1.0) * 0.5.
-- P(main = 2.0) = normalPDF(1.0) * 0.5.
prop_killAllVarExtraction :: Property
prop_killAllVarExtraction = once $ ioProperty $ do
  let result = irDensity defaultCompilerConfig testNormalScaledViaVar (VFloat 2.0) []
  case result of
    VProbDim p _ ->
      return $ counterexample ("Expected normalPDF(1)*0.5≈" ++ show (normalPDF 1.0 * 0.5) ++ ", got " ++ show p)
        (abs (p - normalPDF 1.0 * 0.5) < 1e-6)
    _ -> return $ counterexample ("Unexpected shape: " ++ show result) False

-- Enabling countBranches must not alter probability values, only add a third field.
-- Verify on testDice that P(X=3) is the same with and without branch counting.
prop_BCDoesNotChangeProbability :: Property
prop_BCDoesNotChangeProbability = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withBC, withoutBC) of
    (VProbDim pBC _, VProbDim pNone _) ->
      return $ counterexample
        ("P with BC=" ++ show pBC ++ " /= P without BC=" ++ show pNone)
        (abs (pBC - pNone) < 1e-9)
    _ -> return $ counterexample
      ("Unexpected result shapes: " ++ show withBC ++ ", " ++ show withoutBC) False

-- stripBranchCount structural check: countBranches=False must drop the branch
-- count from the result and nothing else.  The result always carries the
-- impossibility flag as its last field (design inference-result-side-channels),
-- so the layouts are (prob, (dim, (bc, imposs))) and (prob, (dim, imposs)) --
-- what this pins is that exactly the bc slot disappears.
-- Also exercises the killAll IRVar path: testDice's main calls the dice sub-expression
-- via Var, so killAll must rewrite the bc/flag extractions from the called
-- function's result to the shortened layout.
prop_stripBranchCountReturnShape :: Property
prop_stripBranchCountReturnShape = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  let hasBC (VTuple _ (VTuple _ (VTuple _ (VBool _)))) = True
      hasBC _                                          = False
      noBC  (VTuple _ (VTuple _ (VBool _)))            = True
      noBC  _                                          = False
  return $
    counterexample ("countBranches=True should return (p, (d, (bc, imposs))), got: " ++ show withBC)
      (hasBC withBC)
    .&&.
    counterexample ("countBranches=False should return (p, (d, imposs)), got: " ++ show withoutBC)
      (noBC withoutBC)

-- When topKThreshold is set, IREnv should contain exactly one constant named TOP_K_CUTOFF
-- with the value matching the config.
prop_TopKConstantPresentInEnv :: Property
prop_TopKConstantPresentInEnv = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.005 }
      irEnv = expectCompiled (compile conf testDice)
      IREnv _ _ consts = irEnv
  return $ case lookup "TOP_K_CUTOFF" consts of
    Just (VFloat v) -> counterexample ("Expected 0.005, got " ++ show v) (abs (v - 0.005) < 1e-12)
    Just other      -> counterexample ("Expected VFloat, got " ++ show other) False
    Nothing         -> counterexample "TOP_K_CUTOFF constant absent from IREnv" False

-- When topKThreshold is Nothing, no TOP_K_CUTOFF constant should appear in IREnv.
prop_TopKConstantAbsentWithoutFlag :: Property
prop_TopKConstantAbsentWithoutFlag = once $ ioProperty $ do
  let irEnv = expectCompiled (compile defaultCompilerConfig testDice)
      IREnv _ _ consts = irEnv
  return $ counterexample "TOP_K_CUTOFF should not appear when topK is disabled"
    (isNothing (lookup "TOP_K_CUTOFF" consts))

-- The generated Python should contain a plain assignment `TOP_K_CUTOFF = <value>`,
-- not a class definition.
prop_TopKPythonConstantIsPlainAssignment :: Property
prop_TopKPythonConstantIsPlainAssignment = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.001 }
      irEnv = expectCompiled (compile conf testDice)
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
  let hasAssignment = any ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
      hasClass       = any ("class TOP_K_CUTOFF" `isInfixOf`) pyLines
  return $ counterexample ("Expected plain assignment, lines: " ++ unlines pyLines)
    (hasAssignment && not hasClass)

-- The value in the generated Python assignment must match the threshold passed in.
prop_TopKPythonConstantValueMatchesConfig :: Property
prop_TopKPythonConstantValueMatchesConfig = once $ ioProperty $ do
  let thresh = 0.0042 :: Double
      conf = defaultCompilerConfig { topKThreshold = Just thresh }
      irEnv = expectCompiled (compile conf testDice)
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
      assignmentLines = filter ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
  return $ case assignmentLines of
    [line] -> counterexample ("Assignment line: " ++ line)
                (show thresh `isInfixOf` line)
    other  -> counterexample ("Expected exactly one assignment line, got: " ++ show other) False

-- A log-space compile must render its zero as a literal the *target language*
-- knows. Haskell's 'show' spells the non-finite doubles @Infinity@/@-Infinity@/
-- @NaN@, and log space reaches them constantly -- its zero is @-1/0@
-- ('SPLL.Semiring.negInfIR'), so every impossible arm carries one. @Infinity@
-- is not a Python name and @-Infinity@ is not Julia syntax, so emitting it
-- produced code that died with a NameError at run time rather than failing the
-- compile.
--
-- The suite missed this for as long as it existed because the log-space corpus
-- properties route through the interpreter, which never renders a literal --
-- these two are the only tests that put a log-space compile through a text
-- backend.
--
-- Both halves are asserted deliberately: the "no bare Infinity" half is the
-- regression, and the "does emit the mapped literal" half is what keeps the
-- test from going vacuous if log-space zero ever stops reaching codegen.
prop_LogSpacePythonRendersInfinity :: Property
prop_LogSpacePythonRendersInfinity = once $ ioProperty $ do
  let conf = defaultCompilerConfig { logSpace = True }
      src  = unlines (SPLL.CodeGenPyTorch.generateFunctions True
                        (expectCompiled (compile conf testDice)))
  return $ counterexample ("emitted Python:\n" ++ src)
    (not ("Infinity" `isInfixOf` src) && "float('-inf')" `isInfixOf` src)

prop_LogSpaceJuliaRendersInfinity :: Property
prop_LogSpaceJuliaRendersInfinity = once $ ioProperty $ do
  let conf = defaultCompilerConfig { logSpace = True }
      src  = unlines (SPLL.CodeGenJulia.generateFunctions
                        (expectCompiled (compile conf testDice)))
  return $ counterexample ("emitted Julia:\n" ++ src)
    (not ("Infinity" `isInfixOf` src) && "-Inf" `isInfixOf` src)

-- The interpreter must resolve IRVar "TOP_K_CUTOFF" via the constant in IREnv:
-- a topK compile with threshold=0.001 on testDice should agree with exact inference
-- (all branches kept since 1/6 >> 0.001).
prop_TopKConstantResolvedByInterpreter :: Property
prop_TopKConstantResolvedByInterpreter = once $ ioProperty $ do
  let withTopK = irDensity (topKConf 0.001)      testDice (VInt 3) []
  let exact    = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withTopK, exact) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ VFloat topKP `reasonablyClose` VFloat exactP
    _ -> return $ counterexample "Return type was no tuple" False

return []

specTests :: TestTree
specTests = localOption (QuickCheckMaxRatio 20) $ testProperties "Spec" $(allProperties)

main :: IO ()
main = do
  -- Quiet-on-success by default: only failures (and the summary line) are printed.
  -- tasty reads option defaults from TASTY_* environment variables, so setting it
  -- here (only when unset) keeps it overridable: TASTY_HIDE_SUCCESSES=false stack test
  -- prints the full test tree including per-test timings.
  hideSuccesses <- lookupEnv "TASTY_HIDE_SUCCESSES"
  if isNothing hideSuccesses then setEnv "TASTY_HIDE_SUCCESSES" "true" else return ()
  e2e <- end2endTests
  selectDiff <- selectPassDifferentialTests
  batchedPy <- batchedPythonTests
  branchCountBackends <- branchCountBackendTests
  detTests <- determinismTests
  showcase <- showcaseTests
  corpusPool <- loadCorpusCases
  encodeRoundtrip <- encodeRoundtripTests
  -- A handful of tests (deep plan enumeration, mainly) are expensive enough
  -- to noticeably slow day-to-day `stack test` while rarely catching
  -- regressions outside the code they pin. They're skipped unless
  -- NEST_SLOW_TESTS is set, e.g. `NEST_SLOW_TESTS=1 stack test --ta '-p Slow'`.
  runSlow <- lookupEnv "NEST_SLOW_TESTS"
  slow <- if isNothing runSlow then return (testGroup "Slow" []) else do
    slowE2e <- slowEnd2EndTests
    slowBatchedPy <- slowBatchedPythonTests
    return $ testGroup "Slow" [slowInternalsTests, slowE2e, slowBatchedPy, fuzzTests]
  -- 'prop_Fuzz_SamplingMatchesPDF' (the sampling-vs-PDF cross-check between
  -- `generate` and `probability`) draws up to tens of thousands of forward
  -- samples per case, dwarfing every other Slow test's runtime, so it gets
  -- its own further opt-in tier: `NEST_SUPERSLOW_TESTS=1 stack test --ta '-p SuperSlow'`.
  runSuperSlow <- lookupEnv "NEST_SUPERSLOW_TESTS"
  let superSlow = if isNothing runSuperSlow then testGroup "SuperSlow" [] else testGroup "SuperSlow" [superSlowFuzzTests]
  defaultMain $ testGroup "Tests"
    [ specTests
    , corpusTests corpusPool
    , parserTests
    , internalsTests
    , rejectionTests
    , modalityTests
    , modalityInferTests
    , detTests
    , encodeTests
    , encodeRoundtrip
    , showcase
    , e2e
    , selectDiff
    , batchedPy
    , batchedRefusalTests
    , branchCountBackends
    , slow
    , superSlow
    ]
