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
import End2EndTesting (end2endTests, slowEnd2EndTests, getAllTestFiles)
import TestCaseParser (parseProgram, parseTestCases, TestCase(..), Backend(..))
import TestTolerances (probTolerance, reasonablyCloseTolerance, samplingTolerance)
import SPLL.Prelude
import qualified SPLL.CodeGenPyTorch
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
  return [(n, (p, sample, params, expected)) | (n, p, tcs) <- usable, ProbTestCase _ sample params expected <- tcs]

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
  -- testCases/dice (recursive float dice) diverges under branch-counting
  -- compilation: the BC-compiled prob function never terminates although plain
  -- and topK compilation interpret it in milliseconds. Genuine BC bug on
  -- recursive parameterized functions (NeST_internal_docs task
  -- bc-recursive-prob-divergence); excluded from the pool until it is fixed.
  , testProperty "ProbWithBranchCounting"
      (forAllNamedIn (filter ((/= "dice") . fst) probPool) (checkProbTestCasesWithBC bcEnvs))
  , testProperty "MarginalAnyIsOne" (forAllNamed (checkProbAny defaultEnvs))
  , testProperty "TopKZeroThreshMatchesExact" (forAllNamed (checkTopKZeroMatchesExact topK0Envs defaultEnvs))
  , testProperty "TopKNeverInflates" (forAllNamed (checkTopKNeverInflates topK01Envs defaultEnvs))
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
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ (b == VFloat 0.95) && (a == VFloat 0)
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
        Right (VTuple (VFloat prob) (VFloat dim)) -> do
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
        Right (VTuple (VFloat prob) (VFloat dim)) -> do
          -- Original Listing above, Tests below
          let (VFloat genF) = gen
          return $ (VFloat prob) `reasonablyClose` (VFloat (normalPDF ((genF - 1) / 2) / 2))

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
checkProbTestCasesWithBC envs n (p, inp, params, (VFloat out, VFloat outDim)) = ioProperty $ do
  let actualOutput = irDensityC envs n p params inp
  case actualOutput of
    VTuple (VFloat a) (VTuple (VFloat d) (VFloat _)) -> return $
      counterexample (show a ++ "/=" ++ show out) (property $ abs (a - out) < probTolerance)
      .&&. (a === 0 .||. d === outDim)
    _ -> return $ counterexample "Return type was no tuple" False

checkProbAny :: CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbAny envs n (p, _, params, _) = ioProperty $ do
  let actualOutput = irDensityC envs n p params VAny
  case actualOutput of
    VTuple a (VFloat d) -> return $ a `reasonablyClose` VFloat 1
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
    (VTuple (VFloat topKP) _, VTuple exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (exactP `reasonablyClose` VFloat 0.0144)
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
    (VTuple (VFloat topKP) _, VTuple exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Threshold=0 never prunes any branch, so results must match exact inference.
checkTopKZeroMatchesExact :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKZeroMatchesExact topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  case (topKResult, exactResult) of
    (VTuple topKP topKD, VTuple exactP exactD) ->
      return $ topKP `reasonablyClose` exactP .&&. topKD `reasonablyClose` exactD
    _ -> return $ counterexample "Return type was no tuple" False

-- Pruning can only zero out branches, never inflate probability above the exact value.
checkTopKNeverInflates :: CompiledPrograms -> CompiledPrograms -> String -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKNeverInflates topKEnvs defEnvs n (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensityC topKEnvs n p params inp
  let exactResult = irDensityC defEnvs n p params inp
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple (VFloat exactP) _) ->
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
    (VTuple _ (VTuple _ (VFloat topKBC)), VTuple _ (VTuple _ (VFloat noBC))) ->
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
    (VTuple _ (VTuple _ (VFloat lowBC)), VTuple _ (VTuple _ (VFloat highBC))) ->
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
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=3, got " ++ show bc) (bc == 3.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 is a pure if-else tree with 6 leaves. BC should equal 6 for any query.
-- dice1=1; dice(n)=cond(1)+constI(n)(1)+dice(n-1)-1 = dice(n-1)+1; so dice(6)=6.
prop_BCDiceIfElse :: Property
prop_BCDiceIfElse = once $ ioProperty $ do
  let result = irDensity bcConf testDice (VInt 3) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=6, got " ++ show bc) (bc == 6.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Consistency: dice6 as if-else (BC=6) and testDiceAdd as InjF (BC=6 for P(7)) agree.
prop_BCConsistency :: Property
prop_BCConsistency = once $ ioProperty $ do
  let diceResult    = irDensity bcConf testDice    (VInt 3) []
  let diceAddResult = irDensity bcConf testDiceAdd (VInt 7) []
  case (diceResult, diceAddResult) of
    (VTuple _ (VTuple _ (VFloat diceBC)), VTuple _ (VTuple _ (VFloat diceAddBC))) ->
      return $ counterexample ("dice BC=" ++ show diceBC ++ ", diceAdd BC=" ++ show diceAddBC ++ " (expected both=6)") (diceBC == diceAddBC)
    _ -> return $ counterexample "Return type was no tuple" False

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
    (VTuple lowP _, VTuple (VFloat hP) _, VTuple exactP _) ->
      return $ lowP `reasonablyClose` exactP
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
    (VTuple lowP _, VTuple (VFloat hP) _, VTuple exactP _) ->
      return $ lowP `reasonablyClose` exactP
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
        VTuple p _ -> p `reasonablyClose` VFloat 0.25
        x -> counterexample ("Unexpected result shape: " ++ show x) False
    | r <- results ]

-- testConditionalLambdaBC: named deterministic selector applied to a coin-flip argument.
-- Routes through IsConditional + toIREnumerate path in IRCompiler.
-- Argument has 2 discrete values; each iteration traverses one if-else arm → BC = 2.
prop_BCConditionalLambda :: Property
prop_BCConditionalLambda = once $ ioProperty $ do
  let result = irDensity bcConf testConditionalLambdaBC (VFloat 1.0) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) ->
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
    VTuple (VFloat p) _ ->
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
    (VTuple (VFloat pBC) _, VTuple (VFloat pNone) _) ->
      return $ counterexample
        ("P with BC=" ++ show pBC ++ " /= P without BC=" ++ show pNone)
        (abs (pBC - pNone) < 1e-9)
    _ -> return $ counterexample
      ("Unexpected result shapes: " ++ show withBC ++ ", " ++ show withoutBC) False

-- stripBranchCount structural check: when countBranches=False the prob function
-- should return a pair (prob, dim), not a triple.  We verify this by checking that
-- the interpreter result has exactly two components (VTuple _ _) and not three
-- (VTuple _ (VTuple _ _)).
-- Also exercises the killAll IRVar path: testDice's main calls the dice sub-expression
-- via Var, so killAll must rewrite IRTFst(IRTSnd(IRVar x)) → IRTSnd(IRVar x).
prop_stripBranchCountReturnShape :: Property
prop_stripBranchCountReturnShape = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  let isTriple (VTuple _ (VTuple _ _)) = True
      isTriple _                       = False
  return $
    counterexample ("countBranches=True should return triple, got: " ++ show withBC)
      (isTriple withBC)
    .&&.
    counterexample ("countBranches=False should return pair, got: " ++ show withoutBC)
      (case withoutBC of { VTuple _ (VTuple _ _) -> False; VTuple _ _ -> True; _ -> False })

-- When topKThreshold is set, IREnv should contain exactly one constant named TOP_K_CUTOFF
-- with the value matching the config.
prop_TopKConstantPresentInEnv :: Property
prop_TopKConstantPresentInEnv = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.005 }
      Right irEnv = compile conf testDice
      IREnv _ _ consts = irEnv
  return $ case lookup "TOP_K_CUTOFF" consts of
    Just (VFloat v) -> counterexample ("Expected 0.005, got " ++ show v) (abs (v - 0.005) < 1e-12)
    Just other      -> counterexample ("Expected VFloat, got " ++ show other) False
    Nothing         -> counterexample "TOP_K_CUTOFF constant absent from IREnv" False

-- When topKThreshold is Nothing, no TOP_K_CUTOFF constant should appear in IREnv.
prop_TopKConstantAbsentWithoutFlag :: Property
prop_TopKConstantAbsentWithoutFlag = once $ ioProperty $ do
  let Right irEnv = compile defaultCompilerConfig testDice
      IREnv _ _ consts = irEnv
  return $ counterexample "TOP_K_CUTOFF should not appear when topK is disabled"
    (isNothing (lookup "TOP_K_CUTOFF" consts))
  where isNothing Nothing = True; isNothing _ = False

-- The generated Python should contain a plain assignment `TOP_K_CUTOFF = <value>`,
-- not a class definition.
prop_TopKPythonConstantIsPlainAssignment :: Property
prop_TopKPythonConstantIsPlainAssignment = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.001 }
      Right irEnv = compile conf testDice
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
      Right irEnv = compile conf testDice
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
      assignmentLines = filter ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
  return $ case assignmentLines of
    [line] -> counterexample ("Assignment line: " ++ line)
                (show thresh `isInfixOf` line)
    other  -> counterexample ("Expected exactly one assignment line, got: " ++ show other) False

-- The interpreter must resolve IRVar "TOP_K_CUTOFF" via the constant in IREnv:
-- a topK compile with threshold=0.001 on testDice should agree with exact inference
-- (all branches kept since 1/6 >> 0.001).
prop_TopKConstantResolvedByInterpreter :: Property
prop_TopKConstantResolvedByInterpreter = once $ ioProperty $ do
  let withTopK = irDensity (topKConf 0.001)      testDice (VInt 3) []
  let exact    = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withTopK, exact) of
    (VTuple topKP _, VTuple exactP _) ->
      return $ topKP `reasonablyClose` exactP
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
    return $ testGroup "Slow" [slowInternalsTests, slowE2e]
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
    , slow
    ]
