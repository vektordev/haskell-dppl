{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Directory (getCurrentDirectory, findExecutable)
import System.IO.Temp (withSystemTempFile)
import System.IO (hPutStr, hClose, hPutStrLn, stderr)
import System.Environment (lookupEnv)
import System.Process (createProcess, proc, readProcessWithExitCode, waitForProcess)
import System.Exit
import Data.List (groupBy)
import Data.Function (on)
import Control.Monad.Random
import Data.Maybe
import Data.List (intercalate, nub, isInfixOf, isPrefixOf, stripPrefix, transpose, zip4, sort)
import Data.Text (replace, pack, unpack)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.CodeGenJulia
import SPLL.ReservedNames (juliaReservedIdentifiers)
import Data.Char (isAlphaNum, isAlpha)
import SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import SPLL.Parser (tryParseProgram)
import TestCaseParser
import TestTolerances (probTolerance, writeLogitsSlotTolerance, normalizationTolerance, samplingTolerance)
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.AutoNeural (makePartitionPlan, planIndexOf, resolvePartitionAnnotation, PartitionPlan, getSize, InputSlot(..), inputSlots, inputWidth)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Analysis (annotateEnumsProg)
import Data.Foldable (toList)
import Test.QuickCheck hiding (sample, verbose)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Control.Exception (try, evaluate, throwIO, SomeException, bracket_)
import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.QSem (newQSem, waitQSem, signalQSem)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import IRInterpreter (generateRand, generateDet)
import MockNN (evaluateMockNN, mockInputFor)
import ImpactManifest
import CorpusSweep
import CertifiedCensus (programCensus, uncertifiedConstructs, batchedProgramCensus, batchedUncertifiedConstructs)
import qualified Data.Map as Map

-- | M1 differential test (design pytorch-tensorizer): the IR select pass is a
-- behavioural no-op under scalar lowering, since the interpreter and scalar
-- backends evaluate a SelectIf exactly like a LazyIf. So for every corpus
-- prob/cumulative query point, compiling with @batched = True@ (which runs the
-- select pass) must return the same result as the default pipeline. Reuses the
-- same corpus loader as 'end2endTests', restricted to the non-slow,
-- interpreter-routed cases.
--
-- Each program is compiled once per config here, not once per query point:
-- 'compile' depends only on the (program, config) pair, so re-running it for
-- every row of a multi-row .tst file was pure waste -- measured at ~1100
-- corpus query rows against ~200 eligible programs, that was ~5x more compiles
-- than the differential needs, and this group's own cost (~25s) came from
-- exactly that.
selectPassDifferentialTests :: Corpus -> Manifest -> IO TestTree
selectPassDifferentialTests corpus manifest = corpusSweep corpus SweepSpec
  { sweepName = "SelectPassNoOp", sweepTier = Default, sweepSlow = SkipSlow
  , sweepSelect = interpreterRouted
  , sweepNote = "the IR select pass changes no interpreter answer at any query point" } $ \e ->
    let p = ceProgram e
        tcs = shapedCases e
        scalarEnv  = compile defaultCompilerConfig p
        batchedEnv = compile defaultCompilerConfig{batched = True} p
    in testProperty (ceName e) (once $ cachedProperty manifest "SelectPassNoOp" (ceName e)
                                  (differentialKey manifest selectPassCheckVersion p [scalarEnv, batchedEnv] tcs)
                                  (conjoin (map (selectNoOp p scalarEnv batchedEnv) tcs)))

-- | Interpreter-routed in its @.tst@ header.
interpreterRouted :: CorpusEntry -> Bool
interpreterRouted e = Interpreter `elem` ceBackends e

-- | A corpus entry's rows with their neural inputs shaped, as 'loadCorpusPair'
-- returns them.
shapedCases :: CorpusEntry -> [TestCase]
shapedCases e = map (shapeNeuralTestCase (ceProgram e)) (ceCases e)

-- | The plan engine against dense enumeration, at every interpreter-routed,
-- non-slow query point of a neural corpus program (task
-- of-annotation-and-auto-derived-enumeration-divergence). Every neural read is
-- tagged with its resolved annotation, so dense enumeration takes every
-- under-budget domain first and the plan engine is reached by default only
-- above the budget. Budget 0 sends the same programs to the plan engine;
-- wherever both answer, they must agree.
--
-- A program with no engine at budget 0 -- the compile refuses, or, as most
-- refusals surface, its probability body refuses when run -- is not compared:
-- dense enumeration is its only engine, and its own .tst rows check it.
-- Except for 'planEngineCorpus', the programs that reached the plan engine by
-- default before, which must still answer here.
--
-- Non-neural programs are 'budgetZeroDifferentialTests'' instead: budget 0
-- reaches no plan engine there, so the name would mislead.
--
-- The default group skips the @slow@-headered programs, which include most of
-- 'planEngineCorpus' since the tick-redundant corpus programs were demoted
-- (docs-repo task demote-tick-redundant-corpus-programs-to-slow). Their
-- differentials, and the check that every 'planEngineCorpus' name is in the
-- corpus at all, are 'slowPlanEngineDifferentialTests'.
planEngineDifferentialTests :: Corpus -> Manifest -> IO TestTree
planEngineDifferentialTests corpus manifest = corpusSweepAll corpus SweepSpec
  { sweepName = "PlanEngineMatchesDense", sweepTier = Default, sweepSlow = SkipSlow
  , sweepSelect = planEngineSelect
  , sweepNote = "budget 0 (the plan engine) agrees with dense enumeration wherever it answers" } $ \entries ->
  return $ testGroup "PlanEngineMatchesDense" (map (planEngineDifferential manifest) entries)

-- | The Slow twin of 'planEngineDifferentialTests': the same differential on
-- the @slow@-headered programs, and the check that the programs that must
-- reach the plan engine are in the corpus, which reads the whole corpus
-- ('IgnoreSlow') so that it holds whichever tier a program is in. The
-- programs `slow` for their own compile cost stay out
-- ('notSlowForCompileCost'), as before: at budget 0 they cost minutes each.
slowPlanEngineDifferentialTests :: Corpus -> Manifest -> IO TestTree
slowPlanEngineDifferentialTests corpus manifest = corpusSweepAll corpus SweepSpec
  { sweepName = "Slow.PlanEngineMatchesDense (slow)", sweepTier = Slow, sweepSlow = IgnoreSlow
  , sweepSelect = \e -> planEngineSelect e && notSlowForCompileCost e
  , sweepNote = "the plan-engine differential on the slow programs, and every planEngineCorpus name present" } $ \entries -> do
  let missing = filter (`notElem` map ceName entries) planEngineCorpus
  return $ testGroup "PlanEngineMatchesDense (slow)" $
    [ testProperty "the programs that must reach the plan engine are in the corpus" $
        counterexample ("not found: " ++ show missing) (null missing) ]
    ++ map (planEngineDifferential manifest) (filter ceSlow entries)

planEngineSelect :: CorpusEntry -> Bool
planEngineSelect e = interpreterRouted e && not (null (neurals (ceProgram e)))

planEngineDifferential :: Manifest -> CorpusEntry -> TestTree
planEngineDifferential manifest e =
  testProperty n (once $ cachedProperty manifest "PlanEngineMatchesDense" n
                           (differentialKey manifest planEngineCheckVersion p [planEnv, denseEnv] tcs)
                           (conjoin (map (planMatchesDense n p planEnv denseEnv) tcs)))
  where
    n = ceName e
    p = ceProgram e
    tcs = shapedCases e
    planEnv  = compile defaultCompilerConfig{materializationCardinality = 0} p
    denseEnv = compile defaultCompilerConfig p

-- | The non-neural sibling of 'planEngineDifferentialTests' (task
-- materialization-budget-zero-observe-any-wrong): @--materializationBudget 0@
-- is a user-facing flag, and on a non-neural program it declines the dense
-- enumerable-'Apply' arm, so dispatch falls through to point inversion and the
-- set-witness engine. Wherever budget 0 answers, it must agree with the default
-- compile at every interpreter-routed, non-slow query point. A program budget 0
-- does not answer is skipped, as there. 'budgetZeroKnownDivergent' lists the
-- programs where the two disagree for a tracked reason, and
-- 'budgetZeroKnownDivergentRows' the single query rows.
budgetZeroDifferentialTests :: Corpus -> Manifest -> IO TestTree
budgetZeroDifferentialTests corpus manifest = corpusSweep corpus SweepSpec
  { sweepName = "BudgetZeroMatchesDefault", sweepTier = Default, sweepSlow = SkipSlow
  , sweepSelect = \e -> interpreterRouted e && null (neurals (ceProgram e))
                       && ceName e `notElem` budgetZeroKnownDivergent
  , sweepNote = "--materializationBudget 0 agrees with the default compile wherever it answers" } $ \e ->
    let n = ceName e
        p = ceProgram e
        tcs = filter (not . knownDivergentRow n) (shapedCases e)
        zeroEnv = compile defaultCompilerConfig{materializationCardinality = 0} p
        defEnv  = compile defaultCompilerConfig p
    in testProperty n (once $ cachedProperty manifest "BudgetZeroMatchesDefault" n
                                (differentialKey manifest budgetZeroCheckVersion p [zeroEnv, defEnv] tcs)
                                (conjoin (map (planMatchesDense n p zeroEnv defEnv) tcs)))
  where
    knownDivergentRow n tc = case tc of
      ProbTestCase _ sample _ _ -> (n, sample) `elem` budgetZeroKnownDivergentRows
      _                         -> False

-- | Non-neural corpus programs whose budget-0 answer differs from the default
-- compile's, each for a reason tracked elsewhere.
budgetZeroKnownDivergent :: [String]
budgetZeroKnownDivergent = []

-- | Single query rows (program, probability sample) where the budget-0 answer
-- differs from the default compile's, for a reason tracked elsewhere. The
-- program's other rows are still compared. Their budget-0 answers are pinned
-- in 'TestInternals.setWitnessIntBoundaryTests'.
budgetZeroKnownDivergentRows :: [(String, IRValue)]
budgetZeroKnownDivergentRows =
  -- The default compile reports the `Right` rows' density at dim 0 where
  -- budget 0 says dim 1 (task enumerated-sum-over-density-body: the default's
  -- enumerated sum reports a mass). The letfree `Right ANY` also differs in
  -- value: budget 0 answers impossible, because the letfree CDF of
  -- `if Normal == 0.5 then 1 else 2` at 1 is a possible zero mass at dim 0
  -- rather than the density (task letfree-cdf-density-atom-reports-zero-mass).
  [ ("observeContinuousEqualsLetfree",  VEither (Right (VInt 1)))
  , ("observeContinuousEqualsLetfree",  VEither (Right VAny))
  , ("observeContinuousEqualsLetBound", VEither (Right (VInt 0)))
  , ("observeContinuousEqualsLetBound", VEither (Right VAny)) ]

-- | A neural corpus program's log-space answer against its linear one: wherever
-- the linear compile answers, the log-space compile must answer exp(log p) = p
-- at the same dimension. Two sweeps over the neural programs, one per world
-- measure ('Corpus.LogSpaceMatchesLinear' covers the non-neural ones):
--
--  * 'planEngineLogSpaceTests' at budget 0 (task worlds-measure-unification):
--    the plan engine, which reads raw logits. A program it does not answer is
--    skipped, as in 'planEngineDifferentialTests'.
--  * 'neuralLogSpaceTests' at the default budget (task
--    read-logits-network-linear-under-logspace): dense enumeration, which
--    measures a read through the network's read-logits reader @<nn>_auto@.
--    That reader used to answer a linear probability under 'logSpace' too, so
--    budget 0 was the only budget a neural program could be compared at, and
--    even there 18 programs whose measure still reached @_auto@ had to be
--    listed out. The reader is built over the compile's semiring now.
planEngineLogSpaceTests, neuralLogSpaceTests :: Corpus -> Manifest -> IO TestTree
planEngineLogSpaceTests = neuralLogSpaceSweep "PlanEngineLogSpaceMatchesLinear" planLogSpaceCheckVersion
  "the plan engine's log-space answer is exp-equal to its linear one"
  defaultCompilerConfig{materializationCardinality = 0}
neuralLogSpaceTests = neuralLogSpaceSweep "NeuralLogSpaceMatchesLinear" neuralLogSpaceCheckVersion
  "a neural program's default-budget log-space answer is exp-equal to its linear one"
  defaultCompilerConfig

neuralLogSpaceSweep :: String -> String -> String -> CompilerConfig -> Corpus -> Manifest -> IO TestTree
neuralLogSpaceSweep name version note conf corpus manifest = corpusSweep corpus SweepSpec
  { sweepName = name, sweepTier = Default, sweepSlow = SkipSlow
  , sweepSelect = \e -> interpreterRouted e && not (null (neurals (ceProgram e)))
  , sweepNote = note } $ \e ->
    -- The rows are unshaped here, as they always were for this group.
    let p = ceProgram e
        linEnv = compile conf p
        logEnv = compile conf{logSpace = True} p
    in testProperty (ceName e) (once $ cachedProperty manifest name (ceName e)
                                  (differentialKey manifest version p [linEnv, logEnv] (ceCases e))
                                  (conjoin (map (logMatchesLinear p linEnv logEnv) (ceCases e))))
  where
    logMatchesLinear p linEnv logEnv tc = case tc of
      ProbTestCase  n sample params _ -> cmp (n ++ " p" ++ show (sample, params)) (\c -> runProbC  p c params sample)
      CumulTestCase n sample params _ -> cmp (n ++ " cdf" ++ show (sample, params)) (\c -> runIntegC p c params sample)
      _ -> property True
      where
        cmp what run = ioProperty $ do
          lin <- forceResult (linEnv >>= run)
          lg  <- forceResult (logEnv >>= run)
          return $ case (lin, lg) of
            (Left _, _) -> property True
            (Right (VProbDim p1 d1), Right (VProbDim lp2 d2)) ->
              counterexample (what ++ ": linear " ++ show (p1, d1) ++ " /= exp of log-space " ++ show (exp lp2, d2))
                (abs (p1 - exp lp2) < probTolerance && (p1 == 0 || d1 == d2))
            _ -> counterexample (what ++ ": linear " ++ show lin ++ " vs log-space " ++ show lg) False

-- | The corpus programs whose default compile took the plan engine until every
-- read was tagged, and which now enumerate densely by default. They were
-- written to exercise the plan engine, so at budget 0 they must answer. Three
-- more moved but are not listed, as they were `slow` for their compile cost
-- when the list was drawn up: planEnumRecJointState, planEnumRecWeightedCount
-- and planEnumRecAlternatingWeightCount.
planEngineCorpus :: [String]
planEngineCorpus =
  [ "adtNeuralSingleCtorNested", "planEnumInline", "planEnumInlineADT", "planEnumInlineBool"
  , "planEnumRecChain", "planEnumRecCount"
  , "planEnumRecJointStateSeparate", "planEnumRecNilCtor"
  , "planEnumRecScan", "planEnumRecThreaded"
  , "planMultiReaderInnerDraw", "planMultiReaderPlusIf", "planMultiReaderTuplePair" ]

planMatchesDense :: String -> Program -> Either CompilerError IREnv -> Either CompilerError IREnv -> TestCase -> Property
planMatchesDense n p planEnv denseEnv tc = case tc of
  ProbTestCase  name sample params _ -> cmp (name ++ " p" ++ show (sample, params)) (\c -> runProbC  p c params sample)
  CumulTestCase name sample params _ -> cmp (name ++ " cdf" ++ show (sample, params)) (\c -> runIntegC p c params sample)
  _ -> property True
  where
    cmp name run = ioProperty $ do
      plan  <- forceResult (planEnv >>= run)
      dense <- forceResult (denseEnv >>= run)
      return $ case plan of
        Left err | n `notElem` planEngineCorpus -> property True
                 | otherwise -> counterexample (name ++ ": the plan engine did not answer: " ++ err) False
        Right _ -> counterexample (name ++ ": plan " ++ show plan ++ " /= dense " ++ show dense)
                     (resultsAgree plan dense)

-- | Assert one corpus query point is unchanged by the select pass. Non-query
-- cases (writeLogits/argmax) are skipped: the pass only touches prob/integ bodies.
-- Takes the program's scalar/batched compiles already done, shared across
-- every query point of that program.
selectNoOp :: Program -> Either CompilerError IREnv -> Either CompilerError IREnv -> TestCase -> Property
selectNoOp p scalarEnv batchedEnv (ProbTestCase  name sample params _) =
  selectNoOpCmp scalarEnv batchedEnv name (\c -> runProbC  p c params sample)
selectNoOp p scalarEnv batchedEnv (CumulTestCase name sample params _) =
  selectNoOpCmp scalarEnv batchedEnv name (\c -> runIntegC p c params sample)
selectNoOp _ _ _ _ = property True

selectNoOpCmp :: Either CompilerError IREnv -> Either CompilerError IREnv -> String -> (IREnv -> Either CompilerError IRValue) -> Property
selectNoOpCmp scalarEnv batchedEnv name run = ioProperty $ do
  scalar  <- forceResult (scalarEnv >>= run)
  batchedRes <- forceResult (batchedEnv >>= run)
  return $ counterexample
    ("select pass is not a no-op for " ++ name ++ ": scalar=" ++ show scalar ++ ", batched=" ++ show batchedRes)
    (resultsAgree scalar batchedRes)

resultsAgree :: Either String IRValue -> Either String IRValue -> Bool
resultsAgree (Right (VProbDim p1 d1)) (Right (VProbDim p2 d2)) = abs (p1 - p2) < probTolerance && d1 == d2
resultsAgree (Right a)                (Right b)                = show a == show b
resultsAgree (Left _)                 (Left _)                 = True
resultsAgree _                        _                        = False

-- | Fully force a compile+run result, turning any exception (or compile error)
-- into a 'Left' so a crash on only one side is a visible disagreement rather
-- than a hang or a mismatched-type comparison.
forceResult :: Either CompilerError IRValue -> IO (Either String IRValue)
forceResult res = do
  r <- try (evaluate (case res of
              Left err -> error ("compileError: " ++ err)
              Right v  -> length (show v) `seq` v)) :: IO (Either SomeException IRValue)
  return $ either (Left . show) Right r

-- | Check a query point's expected impossibility flag, if the .tst line declared
-- one (the optional third expectation component). The flag is read through
-- 'resultImpossible' rather than by matching the result tuple's shape here --
-- that accessor is the emitted layout's only definition outside the compiler
-- (see docs/semiring-presult-internals.md, "Impossibility flag", and design inference-result-side-channels).
checkImposs :: String -> Maybe Bool -> IRValue -> Property
checkImposs _ Nothing _ = property True
checkImposs name (Just expected) v = case resultImpossible v of
  Nothing -> counterexample
    ("Test case " ++ name ++ " expects an impossibility flag but its result carries none: " ++ show v) False
  Just actual -> counterexample
    ("Impossibility flag differs for test case " ++ name ++ ". Expected: " ++ show expected ++ " Got: " ++ show actual)
    (actual == expected)

-- | The transpiled harnesses only ever emit prob/cumulative cases; anything
-- else arriving here means the caller's routing filter and this emitter
-- disagree.
harnessRoutingError :: String -> TestCase -> String
harnessRoutingError backend tc =
  backend ++ " harness: test case " ++ testCaseName tc
          ++ " is neither a probability nor a cumulative case"

-- | Check an actual (prob, dim) result against a query's 'Expectation'. Dim
-- is checked unconditionally for a 'Possible' expectation -- there is no more
-- "skip the dim check because the actual probability happened to be zero"
-- special case (see docs/testing.md, "`.tst` expectations", task
-- tst-dim-unasserted-at-zero-probability) -- and not checked at all for
-- 'Impossible', which asserts prob=0 and imposs=True instead of a dim.
checkExpectation :: String -> String -> Expectation -> Double -> Int -> IRValue -> Property
checkExpectation probLabel name (Possible (VFloat expectedProb) expectedDim mImp) outProb outDim res =
  counterexample (probLabel ++ " differs for test case " ++ name ++ ". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < probTolerance) .&&.
    counterexample ("Dimensionality differs for test case " ++ name ++ ". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outDim === expectedDim) .&&.
    checkImposs name mImp res
checkExpectation _ name (Possible other _ _) _ _ _ =
  counterexample ("malformed expected result in test case " ++ name ++ ": the probability must be a float, got " ++ show other) False
checkExpectation probLabel name Impossible outProb _outDim res =
  counterexample (probLabel ++ " differs for test case " ++ name ++ ". Expected: 0.0 Got: " ++ show outProb) (abs outProb < probTolerance) .&&.
    checkImposs name (Just True) res

testInterpreter :: Program -> Either CompilerError IREnv -> TestCase -> Property
testInterpreter p compiledE (ProbTestCase name sample params expct) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runProbC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right res@(VProbDim outProb outDim)) -> checkExpectation "Probability" name expct outProb outDim res
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (CumulTestCase name sample params expct) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runIntegC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right res@(VProbDim outProb outDim)) -> checkExpectation "Cmulative probability" name expct outProb outDim res
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (WriteLogitsLengthTestCase name target explicitArgs expectedLen) = ioProperty $ do
  let args = writeLogitsArgsFor p explicitArgs
  result <- try $ evaluate $ (compiledE >>= \c -> runWriteLogitsC p c target args) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      counterexample ("Encode length differs for test case " ++ name ++ " (target " ++ target ++ "). Expected: " ++ show expectedLen ++ " Got: " ++ show (length lst)) (length lst == expectedLen)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a list: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised a compiler error: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (WriteLogitsSlotTestCase name target explicitArgs idxOf expected) = ioProperty $ do
  let args = writeLogitsArgsFor p explicitArgs
      plan = endpointPlan p target
      slotIdx = planIndexOf plan idxOf
  result <- try $ evaluate $ (compiledE >>= \c -> runWriteLogitsC p c target args) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      let items = toList lst
      in if slotIdx >= length items
         then counterexample ("Slot index " ++ show slotIdx ++ " out of bounds (list length " ++ show (length items) ++ ") in test case " ++ name) False
         else case items !! slotIdx of
           VFloat actual ->
             counterexample ("WriteLogits slot " ++ show slotIdx ++ " for " ++ name ++ ": expected " ++ show expected ++ ", got " ++ show actual ++ " (tolerance " ++ show writeLogitsSlotTolerance ++ ")") (abs (actual - expected) < writeLogitsSlotTolerance)
           other -> counterexample ("Slot is not VFloat: " ++ show other ++ " in " ++ name) False
    Right (Right x) -> counterexample ("Output is not a list: " ++ show x ++ " in " ++ name) False
    Right (Left err) -> counterexample ("Compiler error in " ++ name ++ ": " ++ show err) False
    Left err -> counterexample ("Exception in " ++ name ++ ": " ++ show err) False
-- argmax_p(params) = res asserts that `res` is a mode of main's output
-- distribution given `params` (spiked mock NN inputs). Rather than drawing a
-- fixed number of samples and checking each against p(res), we exploit
-- normalization (checked elsewhere): once the summed probability of the
-- distinct values seen so far ("known mass") leaves less than p(res) of
-- probability mass unaccounted for, no unseen value can possibly exceed
-- p(res), and the test can stop -- often immediately, since p(res) > 0.5
-- alone proves it's the mode.
testInterpreter p compiledE (ArgmaxPTestCase name params res) = ioProperty $ do
  let mockedParams = argmaxParams p params
  case compiledE of
    Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Right compiled -> case runProbC p compiled mockedParams res of
      Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
      Right (VProbDim resP resDim)
        | resDim /= 0 -> return $ counterexample ("Test case " ++ name ++ ": argmax_p does not support continuous (dim > 0) results") False
        | otherwise -> evalRandIO (argmaxLoop p compiled name mockedParams res resP [res] resP 0)
      Right x -> return $ counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
-- No trailing catch-all clause: the five equations above cover every
-- 'TestCase' constructor exhaustively (a malformed prob/cumul expectation is
-- now caught inside 'checkExpectation' instead of by falling through a
-- pattern-match miss here -- see its 'Possible other _ _' case).

-- Number of consecutive repeat draws (samples already in the bucket) after
-- which we give up: if normalization held, the accumulated mass of a fully
-- re-discovered support would already have completed the proof above, so
-- this many repeats without that happening means the probabilities of the
-- distinct values found so far don't sum to 1.
argmaxPatience :: Int
argmaxPatience = 10000

-- | The spiked mock-NN parameters an @argmax_p@ row is evaluated at.
argmaxParams :: Program -> [IRValue] -> [IRValue]
argmaxParams p params = shapeNeuralParams p [VTuple (VInt 1) (VTuple par (VInt seed)) | (par, seed) <- zip params [0..]]

argmaxLoop :: RandomGen g => Program -> IREnv -> String -> [IRValue] -> IRValue -> Double -> [IRValue] -> Double -> Int -> Rand g Property
argmaxLoop p compiled name mockedParams res resP bucket knownMass consecutiveDuplicates
  | 1 - knownMass < resP = return (property True)
  | consecutiveDuplicates >= argmaxPatience = return $ counterexample
      ("Test case " ++ name ++ ": probabilities of the " ++ show (length bucket) ++ " distinct values found sum to "
        ++ show knownMass ++ ", which leaves more than p(" ++ show res ++ ") = " ++ show resP
        ++ " of probability mass unaccounted for even after " ++ show argmaxPatience
        ++ " consecutive repeat draws -- distribution appears to not be normalized to 1") False
  | otherwise = do
      sample <- runGenC p compiled mockedParams
      if sample `elem` bucket
        then argmaxLoop p compiled name mockedParams res resP bucket knownMass (consecutiveDuplicates + 1)
        else case runProbC p compiled mockedParams sample of
          Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
          Right (VProbDim sampleP sampleDim)
            -- A continuous value can never beat a discrete res (lower dimensionality
            -- always wins) and isn't part of the dim-0 probability ledger.
            | sampleDim /= 0 -> argmaxLoop p compiled name mockedParams res resP (sample:bucket) knownMass 0
            | sampleP > resP && sample /= res -> return $ counterexample
                ("Test Case " ++ name ++ ": Sample " ++ show sample ++ " has higher probability (" ++ show sampleP
                  ++ ") than the presumed mode " ++ show res ++ " (" ++ show resP ++ ")") False
            | otherwise -> argmaxLoop p compiled name mockedParams res resP (sample:bucket) (knownMass + sampleP) 0
          Right x -> return $ counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False

-- Force a list of independent pure results concurrently (one thread each).
-- The values are unchanged - this only spreads the evaluation work across cores.
parEval :: [a] -> IO [a]
parEval xs = do
  vars <- mapM (\x -> do
    v <- newEmptyMVar
    _ <- forkIO (try (evaluate x) >>= putMVar v)
    return v) xs
  mapM (\v -> takeMVar v >>= either (\e -> throwIO (e :: SomeException)) return) vars

-- | 'mapM' with at most one action per capability running at a time, results
-- in order (rethrowing the first exception). For setup work done before the
-- test tree is built: each action's result is whatever the action returns, so
-- an action must force its own result if the work is to happen on the worker.
parMapIO :: (a -> IO b) -> [a] -> IO [b]
parMapIO f xs = do
  sem <- newQSem =<< getNumCapabilities
  vars <- mapM (\x -> do
    v <- newEmptyMVar
    _ <- forkIO (bracket_ (waitQSem sem) (signalQSem sem) (try (f x)) >>= putMVar v)
    return v) xs
  mapM (\v -> takeMVar v >>= either (\e -> throwIO (e :: SomeException)) return) vars

-- | A neural program's distribution is normalized at seeded inputs: discrete
-- probabilities sum to one, continuous densities are not degenerate
-- ('normalizationBranch' picks which).
discreteProbsNormalized :: Program -> Either CompilerError IREnv -> Property
discreteProbsNormalized p compiledE = case compiledE of
  Left err -> counterexample ("Compilation failed: " ++ err) False
  Right compiled -> ioProperty $ do
    drawn <- normalizationResults p compiled
    return $ case drawn of
      Left err -> counterexample err False
      Right (counts, t) -> case normalizationBranch t of
        ExactSumToOne ->
          -- Discrete (dim 0): with 500 draws from a small support, every distinct
          -- value is observed, so the probabilities of the distinct observed values
          -- should sum to (approximately) exactly 1. Checking both bounds catches
          -- both missing mass (e.g. wrong probabilities) and double-counted /
          -- unnormalized probabilities (sum > 1), neither of which the old
          -- count-weighted sum (always >> 1 for small supports) could detect.
          let totalProb = sum (map normalizationProb t)
          in counterexample ("Probabilities of distinct sampled values sum to " ++ show totalProb ++ ", expected ~1") (abs (totalProb - 1) < normalizationTolerance)
        DensitiesNotDegenerate ->
          -- Continuous: sampled values are (almost) all distinct, and a sum of
          -- densities has no "=1" meaning - just check the densities aren't degenerate.
          let sumProbSamples = sum (zipWith (\c r -> fromIntegral c * normalizationProb r) counts t)
          in counterexample "Probability of randomly sampled values does not sum to 1" (sumProbSamples >= sufficientlyNormal)
  where
    sufficientlyNormal = 0.99

-- | Which of 'discreteProbsNormalized''s two checks a program's results select.
data NormalizationBranch = ExactSumToOne | DensitiesNotDegenerate
  deriving (Show, Eq)

-- | The exact sum-to-one check applies when every result is a mass (dim 0).
--
-- Kept apart from 'discreteProbsNormalized' so a test can assert which branch
-- a program takes: the check used to compare a 'VFloat' dim against @VInt 0@,
-- which never held, so every discrete program silently got only the weak
-- continuous check, and no test noticed (task presult-dim-as-int).
normalizationBranch :: [IRValue] -> NormalizationBranch
normalizationBranch t
  | all ((== Just 0) . resultDim) t = ExactSumToOne
  | otherwise                       = DensitiesNotDegenerate
  where
    resultDim (VProbDim _ d) = Just d
    resultDim _              = Nothing

normalizationProb :: IRValue -> Double
normalizationProb (VProbDim pr _) = pr
normalizationProb v = error ("not a probability result: " ++ show v)

-- | The interpreter's answers 'discreteProbsNormalized' checks: 500 seeded
-- samples of @main@, and the probability of each distinct sampled value, with
-- how often it was drawn.
--
-- Samples are drawn with replacement from a small discrete support, so the same
-- value tends to come up many times in 500 draws. generateDet's cost depends on
-- the size of that support (it enumerates it), not on sampleCnt, so evaluating it
-- once per *distinct* sampled value (weighted by how often it occurred) gives the
-- exact same sum but skips the redundant repeat evaluations.
normalizationResults :: Program -> IREnv -> IO (Either String ([Int], [IRValue]))
normalizationResults p compiled = case (genFun (lookupIREnv "main" compiled), probFun (lookupIREnv "main" compiled)) of
    -- A program with no probability function cannot have its normalization
    -- checked -- and for an inference compiler, a program we can only sample
    -- from is not a passing test, it is a missing feature. Fail loudly rather
    -- than crash on a partial match (the irrefutable Just-pattern this replaces)
    -- or silently pass. E.g. clevr3_predicate_spatial compares two continuous
    -- neural outputs, which currently yields Bottom and emits no main_prob.
    (Just (genExpr, _), Just (probExpr, _)) -> do
      let (params, randomParamsForSamples) = normalizationDraws p
          gens = map (\args -> generateRand (neurals p) (writeLogitsDecls p) compiled (map IRConst args) genExpr) randomParamsForSamples
          pSamples = evalRand (sequence gens) (mkStdGen 42)
          uniqueSamples = nub pSamples
          counts = map (\u -> length (filter (== u) pSamples)) uniqueSamples
      -- The per-sample prob queries are independent and pure; force them in parallel.
      probResults <- parEval (map (\sam -> generateDet (neurals p) (writeLogitsDecls p) compiled (map IRConst (sam:params)) probExpr) uniqueSamples)
      return ((,) counts <$> sequence probResults)
    _ -> return (Left "main has no probability function (inference unavailable); only generate compiled")

-- | Everything 'discreteProbsNormalized' feeds the interpreter besides the
-- compiled program: the parameters of the probability queries, and the
-- seeded parameter draws for the 500 samples. Shared with
-- 'normalizationKey', so the manifest keys on exactly these values.
normalizationDraws :: Program -> ([IRValue], [[IRValue]])
normalizationDraws p = (params, randomParamsForSamples)
  where
    paramCnt = progParameterCount p
    seedList = [0 .. (paramCnt - 1)]
    params = normalizationParams p (map (VTuple (VInt 0) . VInt) seedList)
    randomParams :: RandomGen g => Rand g [IRValue]
    randomParams = normalizationParams p <$> replicateM paramCnt (fmap (\x -> VTuple (VInt 0) (VInt x)) (getRandomR (1, 100000)))
    randomParamsForSamples = evalRand (replicateM sampleCnt randomParams) (mkStdGen 42)
    -- 500 covers every corpus support: the worst total is 0.99916, the same
    -- as with 1000 draws, against a 0.01 tolerance;
    -- at 300 the 26- and 32-value supports (mNistAdd4,
    -- clevrEqualLargeMetalSphereSplit) start losing mass. The draws are
    -- seeded, so this is deterministic.
    sampleCnt = 500

-- | The random-envelope parameters 'discreteProbsNormalized' draws, made to fit
-- a program whose parameters are not all @Symbol@ handles (task
-- tensor-type-shaped-neural-inputs): a parameter feeding a shaped network
-- directly is shaped from its envelope ('shapeNeuralParams'), and any other
-- parameter of an admissible all-@Float@ neural input type (a @Float@ fed to a
-- network through arithmetic, say) is the all-ones value of that type -- ones
-- rather than zeros, since the shaped mock may read a slot as a sigma.
normalizationParams :: Program -> [IRValue] -> [IRValue]
normalizationParams p vs = zipWith fill (mainParamTypes p ++ repeat TSymbol) (shapeNeuralParams p vs)
  where
    fill ty v
      | isMockEnvelope v, ty /= TSymbol, isNeuralInputType ty, all isFloatSlot (inputSlots ty) =
          mockInputFor ty (replicate (inputWidth ty) 1.0)
      | otherwise = v
    isFloatSlot sl = slotElem sl == TFloat

-- | The types of @main@'s parameters, in order, after type inference.
mainParamTypes :: Program -> [RType]
mainParamTypes p = case addTypeInfo (annotateProg (annotateEnumsProg p)) of
  Right (tp, _) | Just body <- lookup "main" (functions tp) -> args (rType (getTypeInfo body))
  _ -> []
  where
    args (TArrow a b) = a : args b
    args _            = []

progParameterCount :: Program -> Int
progParameterCount Program{functions=f} =
  countLambdas (fromMaybe (error "progParameterCount: program has no 'main'") (lookup "main" f))
  where
    countLambdas (Expr _ (Lambda _ e)) = 1 + countLambdas e
    countLambdas _ = 0

-- | Build the argument list for a writeLogits query from the directive's explicit args.
--
--   * No-NN programs (per-function writeLogits over real values): args are passed verbatim
--     (e.g. `writeLogits_at[isRed](0.3, indexOf(True))` calls isRed's writeLogits with s = 0.3).
--   * Read-logits programs: each explicit arg is the value to spike the mock NN at, wrapped in
--     the mock-sym envelope `(mode=1, (spikeVal, seed=0))` so the mock network peaks there.
--   * Read-logits programs with no explicit args (legacy `writeLogits_len=N`): one neutral
--     mock sym per outer parameter of main.
writeLogitsArgsFor :: Program -> [IRValue] -> [IRValue]
writeLogitsArgsFor p explicitArgs
  | not (null explicitArgs) = if null (neurals p) then explicitArgs else shapeNeuralParams p (map spike explicitArgs)
  | null (neurals p)        = []
  | otherwise               = shapeNeuralParams p (replicate (progParameterCount p) (VTuple (VInt 0) (VInt 42)))
  where spike v = VTuple (VInt 1) (VTuple v (VInt 0))

-- | The logit layout for an endpoint function's own output type, resolved exactly as the
-- compiler resolves it when emitting that function's writeLogitsFun (registry entry, else
-- auto-derive). Used to map an `indexOf(value)` directive to a flat slot index.
endpointPlan :: Program -> String -> PartitionPlan
endpointPlan p target = makePartitionPlan (adts p) rt (resolvePartitionAnnotation (writeLogitsDecls p) rt Nothing)
  where rt = endpointReturnRType p target

endpointReturnRType :: Program -> String -> RType
endpointReturnRType p target =
  case lookup target (functions typed) of
    Just binding -> rType (getTypeInfo (stripLambdasE binding))
    Nothing      -> error ("endpointReturnRType: no function named " ++ target ++ " in program")
  where
    typed = case addTypeInfo (annotateProg (annotateEnumsProg p)) of
      Right (tp, _) -> tp
      Left err      -> error ("endpointReturnRType: type inference failed: " ++ show err)
    stripLambdasE (Expr _ (Lambda _ b)) = stripLambdasE b
    stripLambdasE e = e

-- ===========================================================================
-- Routing neural programs onto the Julia/Python text backends
-- (design route-neural-programs-to-julia-python-backends)
-- ===========================================================================

-- | The names 'main' binds as its own lambda parameters, in order. Mirrors
-- 'progParameterCount', which counts the same spine.
mainParamNames :: Program -> [String]
mainParamNames Program{functions=fs} = go (mainBinding fs)
  where
    go (Expr _ (Lambda n e)) = n : go e
    go _ = []

mainBinding :: [FnDecl] -> Expr
mainBinding fs = fromMaybe (error "mainParamNames: program has no 'main'") (lookup "main" fs)

-- | Every @(paramVar, networkName)@ pair where a 'ReadNN' call is applied
-- directly to a bound variable, anywhere in an expression -- generic over the
-- whole 'ExprF' shape via its derived 'Foldable' instance, so this needs no
-- per-constructor case beyond the one it is looking for and still finds a
-- match nested inside an if/let/tuple. A 'ReadNN' applied to anything other
-- than a bare 'Var' (an indirect argument) yields no pair for that call --
-- the envelope resolution below simply leaves such a parameter's .tst value
-- untouched, which is fine for the corpus this routes (task
-- route-neural-programs-to-julia-python-backends): every neural .tst reads
-- its mock straight off a lambda parameter. A read of a /selected/ parameter
-- (@see (if c then a else b)@, or a selection under a @let@/@draw@) pairs every
-- parameter the selection can yield, the same arms and bodies
-- 'SPLL.CalleeNormalize' distributes the read into (task
-- symbol-chosen-by-inline-coin-refused).
readNNOfVar :: Expr -> [(String, String)]
readNNOfVar (Expr _ e) = case e of
  ReadNN name s -> [ (v, name) | v <- selectedVars s ] ++ rest
  _             -> rest
  where
    rest = concatMap readNNOfVar (toList e)
    selectedVars (Expr _ x) = case x of
      Var v                           -> [v]
      IfThenElse _ t f                -> selectedVars t ++ selectedVars f
      Apply (Expr _ (Lambda y b)) _   -> filter (/= y) (selectedVars b)
      _                               -> []

-- | The 'PartitionPlan' governing a declared network's mock output -- the
-- same construction 'IRInterpreter' builds at the special-cased
-- @IRApply (IRVar name) sym@ site, mirrored here because the plan only needs
-- the network's own declaration, not a compiled IR.
networkPlan :: Program -> String -> PartitionPlan
networkPlan p name = case lookupNeural name (neurals p) of
  Nothing -> error ("networkPlan: no neural declaration named " ++ name)
  Just (rt, tag) ->
    let realRT = fromMaybe
          (error ("networkPlan: " ++ name ++ " is not declared Symbol -> _"))
          (neuralValueType rt)
    in makePartitionPlan (adts p) realRT (resolvePartitionAnnotation (writeLogitsDecls p) realRT tag)

-- | Per parameter position of 'main', the input type and plan of the network it
-- feeds directly (as @net(paramVar)@), or 'Nothing' for a position that feeds no
-- network.
paramNetworks :: Program -> [Maybe (RType, PartitionPlan)]
paramNetworks p = [ (\nm -> (networkInput p nm, networkPlan p nm)) <$> lookup v varToNet | v <- mainParamNames p ]
  where varToNet = readNNOfVar (mainBinding (functions p))

-- | A declared network's input type ('TSymbol' for the classic opaque handle).
networkInput :: Program -> String -> RType
networkInput p name = case lookupNeural name (neurals p) of
  Just (rt, _) | Just inp <- neuralInputType rt -> inp
  _ -> error ("networkInput: no valid neural declaration named " ++ name)

-- | Is a value one of the three mock-NN envelopes ('evaluateMockNN')?
isMockEnvelope :: IRValue -> Bool
isMockEnvelope (VTuple (VInt k) _) = k `elem` [0, 1, 2]
isMockEnvelope _                   = False

-- | Replace every mock-NN envelope given for a parameter that feeds a /shaped/
-- network (task tensor-type-shaped-neural-inputs: a @Float@, @Tensor@ or tuple
-- input) by a correctly shaped input that makes the shaped mock answer the
-- logits the envelope stands for ('MockNN.mockInputFor'). So a @.tst@ written
-- against a @Symbol@ network runs unchanged against the same network retyped to
-- take a @Tensor[784] Float@, with a real 784-element tensor passed through the
-- compiled program on every backend. A parameter that is already a value of the
-- input type is passed as it is.
shapeNeuralParams :: Program -> [IRValue] -> [IRValue]
shapeNeuralParams p ps
  | null (neurals p) = ps
  | otherwise = zipWith shape (paramNetworks p ++ repeat Nothing) ps
  where
    shape (Just (inTy, plan)) v
      | inTy /= TSymbol, isMockEnvelope v, inputWidth inTy >= SPLL.AutoNeural.getSize plan =
          mockInputFor inTy (map asDouble (logitsOf (evaluateMockNN plan v)))
    shape _ v = v
    logitsOf (VList l) = toList l
    logitsOf v = error ("shapeNeuralParams: mock NN returned a non-vector: " ++ show v)
    asDouble (VFloat x) = x
    asDouble (VInt i)   = fromIntegral i
    asDouble v          = error ("shapeNeuralParams: non-numeric logit " ++ show v)

-- | Can every mock envelope @main@ takes be passed to its network: a @Symbol@
-- network takes the envelope itself, a shaped one needs an input wide enough to
-- carry the logits ('shapeNeuralParams'). A @Float -> Float@ network cannot
-- carry its two Gaussian logits in one slot, so a property that drives @main@
-- with arbitrary logit vectors does not apply to it.
envelopesShapeable :: Program -> Bool
envelopesShapeable p = and [ inTy == TSymbol || inputWidth inTy >= SPLL.AutoNeural.getSize plan
                           | Just (inTy, plan) <- paramNetworks p ]

-- | 'shapeNeuralParams' over a test case's parameters. Applied once, where the
-- corpus is loaded ('loadCorpusPair'), so every backend sees the same shaped
-- inputs.
shapeNeuralTestCase :: Program -> TestCase -> TestCase
shapeNeuralTestCase p tc = case tc of
  ProbTestCase n s ps e  -> ProbTestCase n s (shapeNeuralParams p ps) e
  CumulTestCase n s ps e -> CumulTestCase n s (shapeNeuralParams p ps) e
  _                      -> tc

-- | Parse a corpus @.ppl@/@.tst@ pair, with the test cases' neural inputs shaped
-- ('shapeNeuralTestCase').
loadCorpusPair :: (FilePath, FilePath) -> IO (Program, ([Backend], Bool, Maybe ExpectFailure, [TestCase]))
loadCorpusPair (pplPath, tstPath) = do
  prog <- parseProgram pplPath
  (bs, slow, ef, tcs) <- parseTestCases tstPath
  return (prog, (bs, slow, ef, map (shapeNeuralTestCase prog) tcs))

-- | Replace every parameter that is a mock-NN envelope (@(0, seed)@ random,
-- @(1, (spike, seed))@ spiking, or @(2, [logits])@ literal) with the raw logit
-- vector 'evaluateMockNN' computes for it -- the same computation
-- 'IRInterpreter'\'s special-cased 'ReadNN' case performs at run time. Julia
-- and Python have no such mock dispatch built in (their emitted code just
-- calls the network's bare name, since a real deployment supplies it): the
-- harness installs an identity network (@net(sym) = sym@,
-- 'juliaBatchTestCode'\/'testPython') and hands it this pre-resolved vector
-- directly, so a mode-0/1 envelope never needs MockNN's RNG reimplemented in
-- either target language -- only mode-2's plain vector-passthrough would work
-- for those two identically, which is why this resolves *all three* modes to
-- one shape uniformly rather than special-casing mode-2 as already-done.
--
-- Only a @Symbol@ network's parameter is resolved. A shaped network's parameter
-- is real data ('shapeNeuralParams'), and its harness mock is the same
-- projection the interpreter uses ('NetMock').
resolveNeuralParams :: Program -> [IRValue] -> [IRValue]
resolveNeuralParams p params = zipWith resolve (paramNetworks p ++ repeat Nothing) params
  where
    resolve (Just (TSymbol, plan)) v = evaluateMockNN plan v
    resolve _                      v = v

-- | 'resolveNeuralParams' applied to a query test case's own parameter list.
-- A no-op on a non-neural program (every parameter position resolves to
-- 'Nothing') and on any non-prob/cumulative case.
resolveNeuralTestCase :: Program -> TestCase -> TestCase
resolveNeuralTestCase p (ProbTestCase n s ps e)  = ProbTestCase  n s (resolveNeuralParams p ps) e
resolveNeuralTestCase p (CumulTestCase n s ps e) = CumulTestCase n s (resolveNeuralParams p ps) e
resolveNeuralTestCase _ tc                       = tc

-- | The network a text-backend harness installs in place of a declared one. A
-- @Symbol@ network is the identity: its parameter arrives pre-resolved to raw
-- logits ('resolveNeuralParams'). A shaped network gets the projection mock
-- 'MockNN.shapedMockLogits' implements for the interpreter: the input flattened
-- in layout order, truncated or padded with @1.0@ to the plan's width.
data NetMock = NetMock
  { netMockName  :: String
  , netMockInput :: RType
  , netMockWidth :: Int
  } deriving (Show)

-- | A program's declared networks, in declaration order -- what the
-- Julia/Python harnesses install mocks for.
networkMocks :: Program -> [NetMock]
networkMocks p = [ NetMock nm (networkInput p nm) (SPLL.AutoNeural.getSize (networkPlan p nm)) | (nm, _, _) <- neurals p ]

-- | Just the declared network names, for harnesses that install identity mocks
-- (BackendAgreement).
networkNames :: Program -> [String]
networkNames p = [ nm | (nm, _, _) <- neurals p ]

-- | The Python definition of a mock network.
pyMockDef :: NetMock -> String
pyMockDef (NetMock nm TSymbol _) = "def " ++ nm ++ "(s):\n    return s\n"
pyMockDef (NetMock nm _ n) = unlines
  [ "def " ++ nm ++ "(s):"
  , "    def _flat(v):"
  , "        if isinstance(v, T): return _flat(v.t1) + _flat(v.t2)"
  , "        if isinstance(v, list): return [float(x) for x in v]"
  , "        return [float(v)]"
  , "    return (_flat(s) + [1.0] * " ++ show n ++ ")[:" ++ show n ++ "]" ]

-- | The Julia definitions of a module's mock networks (inside the module, after
-- @using ..JuliaSPPLLib@, so the runtime's tuple 'T' is in scope).
juliaMockDefs :: [NetMock] -> String
juliaMockDefs nets =
  (if any ((/= TSymbol) . netMockInput) nets
     then "_nest_flat(v::Number) = [Float64(v)]\n\
          \_nest_flat(v::AbstractVector) = Float64[Float64(x) for x in v]\n\
          \_nest_flat(v::T) = vcat(_nest_flat(v.t1), _nest_flat(v.t2))\n"
     else "")
  ++ concatMap def nets
  where
    def (NetMock nm TSymbol _) = nm ++ "(s) = s\n"
    def (NetMock nm _ n) = nm ++ "(s) = vcat(_nest_flat(s), fill(1.0, " ++ show n ++ "))[1:" ++ show n ++ "]\n"

-- | The batched-Python mock: a column of @[B, ...]@ inputs in, @[B, n]@ logits
-- out. A tensor input has its trailing axes flattened, row-major. A scalar or
-- a tuple of scalars is the batched twin of 'pyMockDef': its leaves flattened
-- left to right into @[B, k]@, padded with ones and cut to @n@ columns. Any
-- other input raises, so a @batched@ declaration on such a program fails
-- loudly rather than passing on the identity.
batchedMockExpr :: NetMock -> String
batchedMockExpr (NetMock _ TSymbol _) = "(lambda s: s)"
batchedMockExpr (NetMock _ (TTensor sh _) n) =
  "(lambda s: s.flatten(" ++ show (negate (shapeRank sh)) ++ ")[..., :" ++ show n ++ "])"
batchedMockExpr (NetMock nm ty n) = case flatCols ty "s" of
  Just flat ->
    "(lambda s: (lambda x: torch.cat([x, torch.ones(x.shape[0], " ++ show n ++ ")], -1)[..., :"
    ++ show n ++ "])(" ++ flat ++ "))"
  Nothing ->
    "(lambda s: (_ for _ in ()).throw(NotImplementedError(" ++ show ("no batched mock for network " ++ nm ++ " with input " ++ prettyRType ty) ++ ")))"
  where
    -- A column (@[B]@, or a broadcast Python scalar) of the input's leaves as
    -- a float @[B, k]@ (@[1, k]@ for a scalar) block.
    flatCols t v
      | t `elem` [TFloat, TInt, TBool] =
          Just ("torch.as_tensor(" ++ v ++ ", dtype=torch.float).reshape(-1, 1)")
    flatCols (Tuple a b) v = do
      fa <- flatCols a (v ++ ".t1")
      fb <- flatCols b (v ++ ".t2")
      -- broadcast the batch axis only: the two blocks' widths differ
      Just ("(lambda a, b: torch.cat([a.expand(max(a.shape[0], b.shape[0]), -1), "
            ++ "b.expand(max(a.shape[0], b.shape[0]), -1)], -1))(" ++ fa ++ ", " ++ fb ++ ")")
    flatCols _ _ = Nothing

-- | How many julia processes the corpus is split across ('testJuliaAll').
juliaShards :: Int
juliaShards = 4

-- | Flags for every julia process the tests start. Each emitted module is run
-- on a handful of points, so JIT-compiling it through LLVM costs far more than
-- it saves: @--compile=min@ interprets most of it instead and halves the
-- Julia groups' wall time. The arithmetic is the same Float64 either way.
juliaTestFlags :: [String]
juliaTestFlags = ["--compile=min"]

-- | The network names attached to each program feed a per-module identity
-- mock (@net(sym) = sym@, task route-neural-programs-to-julia-python-backends):
-- the .tst rows' mock-NN parameters are already resolved to raw logit vectors
-- by 'resolveNeuralTestCase' before they reach here, so the network itself
-- only has to be pass-through. Empty for a non-neural program.
testJuliaAll :: [(Either CompilerError IREnv, [TestCase], [NetMock])] -> Property
testJuliaAll programCases = ioProperty $ do
  let results = [(c, tcs, nets) | (c, tcs, nets) <- programCases, not (null tcs)]
  case [err | (Left err, _, _) <- results] of
    (err:_) -> return $ counterexample err False
    [] -> do
      let srcs = [(intercalate "\n" (SPLL.CodeGenJulia.generateFunctions c), tcs, nets) | (Right c, tcs, nets) <- results]
      projectDir <- getCurrentDirectory
      code <- withSystemTempFile "julia_batch.jl" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle (juliaBatchTestCode projectDir srcs)
        hClose tmpHandle
        (_, _, _, handle) <- createProcess (proc "julia" (juliaTestFlags ++ [tmpPath]))
        waitForProcess handle
      return $ case code of
        ExitSuccess -> True === True
        ExitFailure _ -> counterexample "Julia batch test failed. See Julia error message above." False

-- | Every name emitted Julia refers to without defining it -- a call
-- @name(@ or a type test @isa Name@ -- must be one 'juliaMangle' escapes
-- (task python-runtime-name-shadowing). A user binder spelled like such a name
-- would shadow it for the code emitted inside its scope: a parameter @randn@
-- turned the body's @Normal@ draw, @randn()@, into a call of the parameter.
--
-- 'SPLL.ReservedNames.juliaBaseNames' is a curated subset of @Base@ (the whole
-- of it is far too large to list), so this is what keeps it in step with
-- codegen: a new @Base@ call in 'SPLL.CodeGenJulia' fails here, naming it.
-- The scan is sound because codegen never prints a user binder directly
-- before an argument list: applications and callables are emitted
-- parenthesised (@(f)(x)@, @(name)()@), so an identifier immediately followed
-- by @(@ is one of the module's own definitions or a name codegen spelled out.
-- String literals and comments (diagnostics quoting @p(main)@, doc lines) are
-- stripped first. Programs whose Julia codegen refuses are skipped: that
-- refusal is the Julia group's business, not this one's.
-- The sweep runs without julia installed: it only reads the emitted text. It
-- lives in Slow and reads the `slow`-headered programs too ('IgnoreSlow')
-- (docs-repo task demote-tick-redundant-corpus-programs-to-slow): the check
-- needs more than 100 programs, so as not to go vacuous, and the
-- default corpus left after the tick-redundant programs were demoted has
-- fewer. Its long-run home is backend agreement over synthetic IR (docs-repo
-- task ir-fuzz-generator), which can draw adversarial names.
juliaFreeNamesTests :: Corpus -> IO TestTree
juliaFreeNamesTests corpus = corpusSweepAll corpus SweepSpec
  { sweepName = "Slow.Julia free names are escaped", sweepTier = Slow, sweepSlow = IgnoreSlow
  , sweepSelect = notSlowForCompileCost
  , sweepNote = "no free name of an emitted Julia module collides with a Julia builtin" } $ \es ->
    return $ testProperty "Julia free names are escaped"
      (once $ testJuliaFreeNamesEscaped
         [ (ceName e, c, networkMocks (ceProgram e)) | e <- es, Right c <- [compile defaultCompilerConfig (ceProgram e)] ])

testJuliaFreeNamesEscaped :: [(String, IREnv, [NetMock])] -> Property
testJuliaFreeNamesEscaped programs = ioProperty $ do
  results <- forM programs $ \(n, c, nets) -> do
    r <- try (evaluate (forceList (SPLL.CodeGenJulia.generateFunctions c))) :: IO (Either SomeException [String])
    return $ case r of
      Left _    -> Nothing
      Right src -> Just (n, [ x | x <- juliaFreeReferences (unlines src)
                                , x `notElem` juliaReservedIdentifiers, x `notElem` map netMockName nets ])
  let checked = catMaybes results
      bad = [ (n, nub xs) | (n, xs) <- checked, not (null xs) ]
  return $ counterexample
    ("emitted Julia refers to names juliaMangle does not escape (add them to \
     \SPLL.ReservedNames.juliaBaseNames): " ++ show bad)
    (length checked > 100 && null bad)
  where
    forceList xs = length (concat xs) `seq` xs

-- | Names a Julia source calls (@name(@, or parenthesised as @(name)(@, which
-- is how codegen spells every application -- the shape @(listConcat)(..)@
-- slipped through as, task writelogits-text-backends-broken) or type-tests
-- (@isa Name@) that it does not itself define (@function name(@, @struct Name@, or @name(...) =@ /
-- @name = @ at the start of a line). String literals and @#@ comments are
-- removed first.
juliaFreeReferences :: String -> [String]
juliaFreeReferences src = nub [ x | x <- used, x `notElem` defined ]
  where
    code = stripJulia src
    ls = lines code
    defined = concatMap definedOn ls ++ letBound code
    -- an inline @let name = ...;@, which codegen emits for an IR let mid-expression
    letBound str = case str of
      [] -> []
      ('l':'e':'t':' ':more) -> takeWhile isIdentChar more : letBound more
      (_:more) -> letBound more
    definedOn l = case words l of
      -- the function and its parameters: a higher-order parameter is called
      -- as @(f)(x)@, which the parenthesised-callee rule below reads as a use
      ("function" : _) -> functionNames (drop (length "function") (dropWhile (== ' ') l))
      ("struct" : rest : _)   -> [takeWhile isIdentChar rest]
      ("mutable" : "struct" : rest : _) -> [takeWhile isIdentChar rest]
      (w : _) | not (null (takeWhile isIdentChar w)), isAlpha (head w) || head w == '_'
              -> [takeWhile isIdentChar w]
      _ -> []
    -- @name(a, b)@ -> the name and every parameter (each up to a @::@ or @=@)
    functionNames sig =
      let (fname, rest) = span isIdentChar (dropWhile (== ' ') sig)
          params = takeWhile (/= ')') (drop 1 rest)
      in fname : [ takeWhile isIdentChar (dropWhile (== ' ') prm) | prm <- splitOn ',' params ]
    splitOn ch str = case break (== ch) str of
      (x, [])       -> [x]
      (x, _ : more) -> x : splitOn ch more
    used = scan ' ' code
    scan _ [] = []
    scan prev s@(c:_)
      | (isAlpha c || c == '_') && not (isIdentChar prev) && prev /= '.' =
          let (ident, rest) = span isIdentChar s
          in if ident == "isa"
               then let (t, r) = span isIdentChar (dropWhile (== ' ') rest) in t : scan ' ' r
               else [ ident | take 1 rest == "(" || (prev == '(' && take 2 rest == ")(") ] ++ scan (last ident) rest
    scan _ (c:rest) = scan c rest
    isIdentChar ch = isAlphaNum ch || ch == '_' || ch == '!'

-- | Blank out Julia string literals (with backslash escapes) and @#@ comments.
stripJulia :: String -> String
stripJulia = go
  where
    go [] = []
    go ('"':rest) = '"' : inStr rest
    go ('#':rest) = go (dropWhile (/= '\n') rest)
    go (c:rest) = c : go rest
    inStr [] = []
    inStr ('\\':_:rest) = inStr rest
    inStr ('"':rest) = '"' : go rest
    inStr (_:rest) = inStr rest

-- The program goes to a temp file rather than @python3 -c@, matching
-- 'testJuliaAll'. An emitted program is not argv-sized: several -O0 compiles
-- exceed the kernel's per-argument limit and the spawn fails with "Argument
-- list too long" -- a harness failure indistinguishable, in the report, from
-- the program being wrong.
--
-- @netNames@ (empty for a non-neural program) gets one identity-mock
-- definition apiece -- see 'testJuliaAll'\'s note.
testPython :: [NetMock] -> Either CompilerError IREnv -> [TestCase] -> Property
testPython netNames compiledE tc = ioProperty $ do
  case compiledE of
    Left err -> return $ counterexample err False
    Right compiled -> do
      projectDir <- getCurrentDirectory
      code <- withSystemTempFile "spll_test.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle (pythonTestScript projectDir netNames compiled tc)
        hClose tmpHandle
        (_, _, _, handle) <- createProcess (proc "python3" [tmpPath])
        waitForProcess handle
      case code of
        ExitSuccess -> return $ True === True
        ExitFailure _ -> return $ counterexample ("Python test " ++ testCaseName (head tc) ++ " failed. See Python error message") False

-- | The complete, self-contained script 'testPython' runs: the emitted module
-- for @compiled@, one identity mock per network name, and the row checks from
-- 'pythonTestCode' (each raising on a mismatch, so exit 0 means every row
-- matched). Shared with "TestKnownIssues", whose @broken@ check asks the same
-- question in reverse. The script is meant to run as a file, so sys.path[0]
-- is its temp dir rather than the project; pythonLib has to be put back on
-- the path explicitly, which is what @projectDir@ is for.
pythonTestScript :: FilePath -> [NetMock] -> IREnv -> [TestCase] -> String
pythonTestScript projectDir netNames compiled tc =
  "import sys\nsys.path.insert(0, " ++ show projectDir ++ ")\n" ++ mockDefs ++ pythonTestCode src tc
  where
    src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True compiled)
    mockDefs = concatMap pyMockDef netNames

-- | One writeLogits row as the text backends check it: the endpoint, its
-- arguments as the emitted function takes them, and what to assert about the
-- returned vector. The arguments are 'writeLogitsArgsFor''s, with a mock-NN
-- envelope resolved to the raw vector the identity mock passes through, as
-- 'resolveNeuralTestCase' does for a query row (only @main@'s parameters feed
-- a network, so only @main@'s are resolved).
data WriteLogitsRow = WriteLogitsRow
  { wlName   :: String
  , wlTarget :: String
  , wlArgs   :: [IRValue]
  , wlCheck  :: WriteLogitsCheck }

-- | The vector's length, or (0-based) slot index and expected value.
data WriteLogitsCheck = WLLength Int | WLSlot Int Double

writeLogitsRow :: Program -> TestCase -> WriteLogitsRow
writeLogitsRow p tc = case tc of
  WriteLogitsLengthTestCase n t ex len -> WriteLogitsRow n t (argsFor t ex) (WLLength len)
  WriteLogitsSlotTestCase n t ex v e   -> WriteLogitsRow n t (argsFor t ex) (WLSlot (planIndexOf (endpointPlan p t) v) e)
  _ -> error ("writeLogitsRow: not a writeLogits row: " ++ testCaseName tc)
  where
    argsFor t ex = (if t == "main" then resolveNeuralParams p else id) (writeLogitsArgsFor p ex)

-- | Each row calls the endpoint's emitted @writeLogits@ method and raises on a
-- wrong length or slot, so exit 0 means every row matched.
testPythonWriteLogits :: [NetMock] -> Either CompilerError IREnv -> [WriteLogitsRow] -> Property
testPythonWriteLogits netNames compiledE rows = ioProperty $ case compiledE of
  Left err -> return $ counterexample err False
  Right compiled -> do
    projectDir <- getCurrentDirectory
    code <- withSystemTempFile "spll_writelogits.py" $ \tmpPath tmpHandle -> do
      hPutStr tmpHandle (pythonWriteLogitsScript projectDir netNames compiled rows)
      hClose tmpHandle
      (_, _, _, handle) <- createProcess (proc "python3" [tmpPath])
      waitForProcess handle
    return $ case code of
      ExitSuccess -> property True
      ExitFailure _ -> counterexample ("Python writeLogits test " ++ wlName (head rows) ++ " failed. See Python error message") False

-- | The script 'testPythonWriteLogits' runs: the emitted module, one identity
-- mock per network, and the row checks.
pythonWriteLogitsScript :: FilePath -> [NetMock] -> IREnv -> [WriteLogitsRow] -> String
pythonWriteLogitsScript projectDir netNames compiled rows = script
  where
    src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True compiled)
    script = "import sys\nsys.path.insert(0, " ++ show projectDir ++ ")\n"
          ++ concatMap pyMockDef netNames
          ++ unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") (pack src))
          ++ "\n" ++ concatMap row rows
    row r =
          "_wl = list(" ++ wlTarget r ++ ".writeLogits(" ++ intercalate ", " (map pyVal (wlArgs r)) ++ "))\n"
          ++ case wlCheck r of
               WLLength n ->
                 "if len(_wl) != " ++ show n ++ ":\n\
                 \  raise ValueError(\"writeLogits length \" + str(len(_wl)) + \" != " ++ show n ++ " in test case " ++ wlName r ++ "\")\n"
               WLSlot i e ->
                 "if not (" ++ show i ++ " < len(_wl) and abs(_wl[" ++ show i ++ "] - " ++ pyVal (VFloat e) ++ ") < " ++ show writeLogitsSlotTolerance ++ "):\n\
                 \  raise ValueError(\"writeLogits slot " ++ show i ++ " wrong: \" + str(_wl) + \" in test case " ++ wlName r ++ "\")\n"

-- | The Julia twin of 'testPythonWriteLogits', every program in one julia
-- process (one module each), like 'testJuliaAll'.
testJuliaWriteLogitsAll :: [(Either CompilerError IREnv, [WriteLogitsRow], [NetMock])] -> Property
testJuliaWriteLogitsAll programs = ioProperty $ case [err | (Left err, _, _) <- programs] of
  (err:_) -> return $ counterexample err False
  [] -> do
    projectDir <- getCurrentDirectory
    let script = "include(\"" ++ projectDir ++ "/juliaLib.jl\")\nusing .JuliaSPPLLib\n"
                 ++ juliaWriteLogitsBody [ (c, rows, nets) | (Right c, rows, nets) <- programs ]
    code <- withSystemTempFile "julia_writelogits.jl" $ \tmpPath tmpHandle -> do
      hPutStr tmpHandle script
      hClose tmpHandle
      (_, _, _, handle) <- createProcess (proc "julia" [tmpPath])
      waitForProcess handle
    return $ case code of
      ExitSuccess -> property True
      ExitFailure _ -> counterexample "Julia writeLogits batch failed. See Julia error message above." False

-- | The modules and row checks 'testJuliaWriteLogitsAll' runs, one module
-- per program, without the runtime's @include@ line.
juliaWriteLogitsBody :: [(IREnv, [WriteLogitsRow], [NetMock])] -> String
juliaWriteLogitsBody programs = concatMap (\(idx, (c, rows, nets)) ->
          let m = "WLProg" ++ show (idx :: Int)
          in "module " ++ m ++ "\nusing ..JuliaSPPLLib\n"
             ++ juliaMockDefs nets
             ++ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions c) ++ "\nend\n"
             ++ concatMap (row m) rows) (zip [0 ..] programs)
  where
        row m r =
          "_wl = collect(" ++ m ++ "." ++ wlTarget r ++ "_writeLogits(" ++ intercalate ", " (map (juliaVal . qualifyConstructors m) (wlArgs r)) ++ "))\n"
          ++ case wlCheck r of
               WLLength n ->
                 "if length(_wl) != " ++ show n ++ "\n\
                 \  error(\"writeLogits length \" * string(length(_wl)) * \" != " ++ show n ++ " in test case " ++ wlName r ++ "\")\nend\n"
               WLSlot i e ->
                 "if !(" ++ show i ++ " < length(_wl) && abs(_wl[" ++ show (i + 1) ++ "] - " ++ juliaVal (VFloat e) ++ ") < " ++ show writeLogitsSlotTolerance ++ ")\n\
                 \  error(\"writeLogits slot " ++ show i ++ " wrong: \" * string(_wl) * \" in test case " ++ wlName r ++ "\")\nend\n"

juliaBatchTestCode :: FilePath -> [(String, [TestCase], [NetMock])] -> String
juliaBatchTestCode projectDir allCases =
  "include(\"" ++ projectDir ++ "/juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n" ++
  concatMap (\(idx, (src, tcs, nets)) ->
    let modName = "Prog" ++ show (idx :: Int)
    in "module " ++ modName ++ "\nusing ..JuliaSPPLLib\n" ++
       juliaMockDefs nets ++
       src ++ "\nend\n" ++
       juliaModuleTestCases modName tcs
  ) (zip [0..] allCases)

-- The compiled result is (prob, (dim, impossible)) -- the trailing field is the
-- internal impossibility flag (design inference-result-side-channels), which is
-- not stripped from the emitted code, hence the nested dim access below. The
-- dim's value is checked only when the .tst row's 'Expectation' actually
-- states a dim ('Possible') -- unconditionally, not gated on the runtime
-- probability any more -- and not for 'Impossible' rows, which have none to
-- check (see docs/testing.md, "`.tst` expectations"). Its type (an Int) is
-- checked on every row.
juliaModuleTestCases :: String -> [TestCase] -> String
juliaModuleTestCases modName tcs =
  modName ++ ".main_gen(" ++ intercalate ", " (map jVal exampleParams) ++ ")\n" ++
  concat (map (\tc ->
    let (name, sample, params, expct) = unpackTestCase tc
        call = modName ++ "." ++ mainName tc ++ "(" ++ jVal sample ++ ", " ++ intercalate ", " (map jVal params) ++ ")"
        outProb = VFloat (expectationProb expct)
        -- The dim is an Int on every row, 'Impossible' ones included: Julia's
        -- @0 == 0.0@ holds, so a value comparison alone would pass a float dim.
        dimCheck =
          "if typeof(tmp[2][1]) != Int\n\
          \  error(\"Dimensionality is not an Int: \" * repr(tmp[2][1]) * \" in test case " ++ name ++ "\")\n\
          \end\n" ++
          case expectationDim expct of
            Nothing -> ""
            Just d  ->
              "if tmp[2][1] != " ++ show d ++ "\n\
              \  error(\"Dimensionality wrong: \" * string(tmp[2][1]) * \"/=" ++ show d ++ " in test case " ++ name ++ "\")\n\
              \end\n"
    in "tmp = " ++ call ++ "\n\
       \if abs(tmp[1] - " ++ juliaVal outProb ++ ") > " ++ show probTolerance ++ "\n\
       \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ ") * \"in test case " ++ name ++ "\")\n\
       \end\n" ++ dimCheck ++ juliaImpossCheck name (expectationImposs expct)
    ) tcs)
  where
    (_, _, exampleParams, _) = unpackTestCase (head tcs)
    unpackTestCase (ProbTestCase name sample params expct) = (name, sample, params, expct)
    unpackTestCase (CumulTestCase name sample params expct) = (name, sample, params, expct)
    unpackTestCase tc = error (harnessRoutingError "Julia" tc)
    mainName (ProbTestCase _ _ _ _) = "main_prob"
    mainName (CumulTestCase _ _ _ _) = "main_integ"
    mainName tc = error (harnessRoutingError "Julia" tc)
    -- Each program is wrapped in its own module, so its ADT constructors are
    -- not in scope where the harness writes the query point. Python's harness
    -- splices the source into the same namespace and needs no such qualifying.
    jVal = juliaVal . qualifyConstructors modName

-- | Prefix every ADT constructor name in a value with @modName.@, so an
-- ADT-valued query point names constructors that live inside the generated
-- module.
qualifyConstructors :: String -> IRValue -> IRValue
qualifyConstructors modName = go
  where
    go (VADT cn fs)          = VADT (modName ++ "." ++ cn) (map go fs)
    go (VTuple a b)          = VTuple (go a) (go b)
    go (VEither (Left a))    = VEither (Left (go a))
    go (VEither (Right b))   = VEither (Right (go b))
    go (VList l)             = VList (goList l)
    go (VTensor sh xs)       = VTensor sh (map go xs)
    go v                     = v
    goList EmptyList         = EmptyList
    goList AnyList           = AnyList
    goList (ListCont x xs)   = ListCont (go x) (goList xs)

-- The emitted result is (prob, (dim, impossible)), so the impossibility flag --
-- checked only when the .tst line declared an expectation for it -- sits at
-- tmp[2][2].
juliaImpossCheck :: String -> Maybe Bool -> String
juliaImpossCheck _ Nothing = ""
juliaImpossCheck name (Just expected) =
  "if tmp[2][2] != " ++ juliaVal (VBool expected) ++ "\n\
  \  error(\"Impossibility flag wrong: \" * string(tmp[2][2]) * \"/=\" * string(" ++ juliaVal (VBool expected) ++ ") * \"in test case " ++ name ++ "\")\n\
  \end\n"

pythonTestCode :: String -> [TestCase] -> String
pythonTestCode src tcs = 
  unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") (pack src)) ++ "\n" ++   -- Importing pyTorch is really slow and not needed
  "main.generate(" ++ intercalate ", " (map pyVal exampleParams) ++ ")\n" ++
  concatMap pyCase tcs
  where
    (_, _, exampleParams, _) = unpackTestCase (head tcs)
    unpackTestCase (ProbTestCase name sample params expct) = (name, sample, params, expct)
    unpackTestCase (CumulTestCase name sample params expct) = (name, sample, params, expct)
    unpackTestCase tc = error (harnessRoutingError "Python" tc)
    mainName (ProbTestCase _ _ _ _) = "main.forward"
    mainName (CumulTestCase _ _ _ _) = "main.integrate"
    mainName tc = error (harnessRoutingError "Python" tc)
    -- The dim's value is checked only when the .tst row's 'Expectation'
    -- states a dim ('Possible') -- unconditionally, not gated on the runtime
    -- probability any more -- and not for 'Impossible' rows, which have none
    -- to check (see docs/testing.md, "`.tst` expectations"). Its type is
    -- checked on every row.
    pyCase tc =
      let (name, sample, params, expct) = unpackTestCase tc
          outProb = VFloat (expectationProb expct)
          -- The dim is an int on every row, 'Impossible' ones included:
          -- Python's @0 == 0.0@ holds, so a value comparison alone would
          -- pass a float dim. @type(...) is int@ also refuses a bool.
          dimCheck =
            "if type(tmp[1][0]) is not int:\n\
            \  raise ValueError(\"Dimensionality is not an int: \" + repr(tmp[1][0]) + \" in test case " ++ name ++ "\")\n" ++
            case expectationDim expct of
              Nothing -> ""
              Just d  ->
                "if tmp[1][0] != " ++ show d ++ ":\n\
                \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1][0]) + \"/=" ++ show d ++ " in test case " ++ name ++ "\")\n"
      in
        "tmp = " ++ mainName tc ++ "(" ++  pyVal sample ++ ", " ++ intercalate ", " (map pyVal params) ++ ")\n\
        \if abs(tmp[0] - " ++ pyVal outProb ++ ") > " ++ show probTolerance ++ ":\n\
        \  raise ValueError(\"Probability wrong: \" + str(tmp[0]) + \"!=\" + str(" ++ pyVal outProb ++ ") + \"in test case " ++ name ++ "\")\n" ++
        dimCheck ++ pyImpossCheck name (expectationImposs expct)

-- The emitted result is (prob, (dim, impossible)), so the impossibility flag --
-- checked only when the .tst line declared an expectation for it -- sits at
-- tmp[1][1].
pyImpossCheck :: String -> Maybe Bool -> String
pyImpossCheck _ Nothing = ""
pyImpossCheck name (Just expected) =
  "if bool(tmp[1][1]) != " ++ pyVal (VBool expected) ++ ":\n\
  \  raise ValueError(\"Impossibility flag wrong: \" + str(tmp[1][1]) + \"!=\" + str(" ++ pyVal (VBool expected) ++ ") + \"in test case " ++ name ++ "\")\n"

-- ===========================================================================
-- Batched PyTorch differential test (design pytorch-tensorizer, M2)
-- ===========================================================================

-- | For every corpus program eligible for batched mode (its prob/integ body
-- lies in the tensor fragment, so 'generateFunctionsBatched' returns 'Right'),
-- run the emitted batched code over a /batch/ of the program's query points at
-- once and check each element matches the point's expected @.tst@ value -- the
-- same ground truth the scalar Python test checks per point. This exercises the
-- real torch code path: @torch.where@ selects, tensor densities, structure-of-
-- arrays tuple leaves, and per-element @dim@ tensors.
--
-- The batched backend emits @torch@ ops, so a torch-enabled Python interpreter
-- is required. It is looked up via @NEST_TORCH_PYTHON@, then a conventional
-- venv path, then @python3@; if none imports torch the value differential
-- fails ('noTorch'), unless @NEST_SKIP_TORCH=1@ opts out of it. Torch import is
-- slow, so every eligible program runs in one shared interpreter process.
--
-- Which programs participate is a first-class @.tst@ routing declaration: the
-- @batched@ token in the @backends:@ header (see TestCaseParser). For every
-- program that lists it, eligibility is /asserted/ (`declared-batched-eligible`)
-- rather than filtered — a change that makes a program fall out of the tensor
-- fragment names it and quotes the refusal diagnostic instead of silently
-- shrinking the group. That assertion is pure Haskell (compile +
-- 'generateFunctionsBatched' + 'batchGroups') and therefore runs whether or not
-- torch is available.
--
-- The reverse direction (a program that is eligible but does not declare it)
-- is only a stderr note, not a failure: eligibility /loss/ is the regression
-- worth breaking the build over, while eligibility /gain/ happens whenever
-- someone adds an ordinary scalar program.
--
-- The same declared set feeds the M5 topK differential ('topKEntries' /
-- 'runBatchedTopK'), which recompiles each program at a cutoff and checks batched
-- topK is a per-element decision.
--
-- (Before this became a declaration, the selection condition was
-- @Python \`elem\` bs || not (null (neurals p))@: neural programs are
-- Interpreter-routed, since their networks are undefined in the emitted scalar
-- code, but batched mode supplies a torch mock, so they were admitted
-- regardless of the Python routing header (design pytorch-tensorizer M2b). That
-- special case is gone — a neural program simply lists @batched@ itself.)
-- | Everything both 'batchedPythonTests' and 'slowBatchedPythonTests' need:
-- loading the corpus once, working out batched/dense eligibility, and finding
-- a torch-enabled python. Shared so the two functions agree on exactly which
-- programs are eligible, at the cost of loading the corpus twice when both
-- run (only NEST_SLOW_TESTS=1 does that, and corpus loading itself is cheap --
-- the expense here is the torch subprocess, not the Haskell side).
batchedPythonFixtures :: [CorpusEntry]
                      -> IO ( [(String, Either String (String, [BatchGroup], [NetMock]))]
                             , [String]
                             , [(String, String, [BatchGroup], [NetMock])]
                             , [(String, String, [BatchGroup], [NetMock])]
                             , ([(String, String, [BatchGroup], [NetMock])], [String], [String])
                             , [(String, String, [BatchGroup], [NetMock])]
                             , Maybe FilePath
                             , [(String, [String])] )
batchedPythonFixtures corpusEntries' = do
  -- `slow`-headered programs stay out of batched coverage by construction, the
  -- same way they stay out of the Interpreter groups (both sweeps' 'SkipSlow').
  let entries = [ (ceName e, ceProgram e, ceBackends e, shapedCases e) | e <- corpusEntries' ]
      -- The topK differential (M5) recompiles the `batched`-declaring programs
      -- at a cutoff, so it draws from the same declaration, not from a second
      -- eligibility condition of its own.
      batchedDeclared = [ (n, p, tcs) | (n, p, bs, tcs) <- entries, Batched `elem` bs ]
      denseNames = [ n | (n, _, bs, _) <- entries, Dense `elem` bs ]
  -- Each eligibility check is a whole batched compile, and there is one per
  -- corpus program. They run here, before the tree exists, spread over the
  -- capabilities ('parMapIO'); serially they cost ~10 s of startup.
  --
  -- They are deliberately *not* deferred into the tests that read them. Several
  -- BatchedPython tests start together and walk these lists from the head, so
  -- deferred results are expensive shared thunks forced by many tasty threads
  -- at once -- the shape that deadlocked the Slow Fuzz group on a 12-core
  -- machine (docs-repo task fuzz-tier-blackhole-deadlock-at-property-start).
  -- And 'batchedEligibility' catches every exception, so a tasty timeout or a
  -- ^C landing in whichever test happened to force one would have recorded
  -- that program as "crashed" for every other test too.
  let eligibility (n, p, _, tcs) = (,) n <$> batchedEligibility p tcs
  declaredC <- parMapIO (\(n, p, _, tcs) -> (,) n <$> batchedEligibilityCensus p tcs)
                        [ e | e@(_, _, bs, _) <- entries, Batched `elem` bs ]
  undeclared <- parMapIO eligibility [ e | e@(_, _, bs, _) <- entries, Batched `notElem` bs ]
  let declared = [ (n, fmap fst r) | (n, r) <- declaredC ]
      -- Per eligible program, the constructs of its batched compile the
      -- batched fuzz arm does not certify ('batchedUncertifiedConstructs').
      censuses = [ (n, c) | (n, Right (_, c)) <- declaredC ]
      eligible = [ (n, src, gs, nets) | (n, Right (src, gs, nets)) <- declared ]
      gained   = [ n | (n, Right _) <- undeclared ]
      topkEligible = topKEntries batchedDeclared
      -- M3: a program declaring `dense` must actually get dense entry points.
      -- Read off the emitted source, which is where the capability is visible;
      -- a `dense` declaration on a program that is not even batched-eligible is
      -- already caught above.
      denseDeclared = [ e | e@(n, _, _, _) <- eligible, n `elem` denseNames ]
      -- M3 x M5: the same topK-recompiled entries the per-element topK
      -- differential uses, narrowed to the dense-declaring programs. Their
      -- expectations are already retargeted to the *interpreter's* value at
      -- that threshold, so running them through the dense path checks dense
      -- mode inherits topK rather than merely agreeing with itself.
      denseTopK = [ e | let (pairs, _, _) = topkEligible, e@(n, src, _, _) <- pairs
                      , takeWhile (/= '@') n `elem` denseNames
                      , not (null (denseEntryPoints src)) ]
  mpy <- findTorchPython
  return (declared, gained, eligible, denseDeclared, topkEligible, denseTopK, mpy, censuses)

-- | The cheap, always-on half of the batched-mode differential: pure-Haskell
-- eligibility bookkeeping (no torch, no subprocess) plus the value
-- differentials cheap enough to run on every `stack test`
-- ('runBatchedPython'/'runBatchedGradients'/'runBatchedGenerate' -- each
-- well under 5s). The topK-threshold
-- differentials live in 'slowBatchedPythonTests' instead -- see there for why.
-- So do the two dense checks: every dense-declaring program is `slow` since the
-- tick-redundant corpus programs were demoted (docs-repo task
-- demote-tick-redundant-corpus-programs-to-slow), and this group skips them.
batchedPythonTests :: Corpus -> Manifest -> IO TestTree
batchedPythonTests corpus manifest = corpusSweepAll corpus SweepSpec
  { sweepName = "BatchedPython", sweepTier = Default, sweepSlow = SkipSlow, sweepSelect = const True
  , sweepNote = "batched/dense eligibility of every program, and the batched value differentials" } $ \entries -> do
  (declared, gained, eligible, denseDeclared, _, _, mpy, censuses) <- batchedPythonFixtures entries
  mtorch <- traverse (\py -> (,) py <$> torchFingerprint py) mpy
  let refused  = [ (n, msg) | (n, Left msg) <- declared ]
      -- Batched reference compliance (docs-repo task
      -- batched-backend-reference-compliance): the interpreter is the
      -- reference, and the batched fuzz arm certifies the batched backend
      -- against it construct by construct ('CertifiedCensus.batchedCertifiedConstructs').
      -- A program's rows run on the batched backend only when its batched
      -- census leaves that set; the check stays keyed with the torch
      -- fingerprint. The gradient and generate checks are not certified by
      -- the fuzzer and run on every eligible program.
      uncertifiedBatched = [ n | (n, c) <- censuses, not (null c) ]
      valueRouted = [ e | e@(n, _, _, _) <- eligible, n `elem` uncertifiedBatched ]
      denseNames = map (\(n, _, _, _) -> n) denseDeclared
      denseGained = [ n | (n, src, _, _) <- eligible
                        , n `notElem` denseNames, not (null (denseEntryPoints src)) ]
  return $ testGroup "BatchedPython" $
    [ testProperty "declared-batched-eligible" (once (declaredEligibleProp (length declared) refused))
    , testProperty "eligibility-gain-note" (once (gainNoteProp gained))
    , testProperty "dense-eligibility-gain-note" (once (denseGainNoteProp denseGained))
    , testProperty "dense-domain-boundary" (once (denseBoundaryProp eligible))
    ] ++ case mtorch of
      Nothing ->
        [ testProperty "torch-python-found" $ once $ ioProperty $
            noTorchProperty "BatchedPython value differential" ]
      Just (py, torch) ->
        [ testProperty "batched-vs-expected" (once (certifiedNote censuses (length eligible) valueRouted
                                                     (cachedTorch manifest torch "batched-vs-expected" valueRouted (runBatchedPython py))))
        , testProperty "gradients-nan-free" (once (cachedTorch manifest torch "gradients-nan-free" eligible (runBatchedGradients py)))
        , testProperty "generate-density-matches-expected"
            (once (cachedTorch manifest torch "generate-density-matches-expected" eligible (runBatchedGenerate py))) ]

-- | Each value differential runs every program in one torch process, so it
-- is a batch: only the programs whose key changed are run, and an
-- all-unchanged differential starts no python. An empty selection runs
-- as it is, so the differential's own "nothing eligible" failure stands.
cachedTorch :: Manifest -> String -> String -> [(String, String, [BatchGroup], [NetMock])]
            -> ([(String, String, [BatchGroup], [NetMock])] -> Property) -> Property
cachedTorch manifest torch name entries run
  | null entries = run entries
  | otherwise = cachedBatch manifest ("BatchedPython." ++ name)
                  [ (n, batchedKey manifest torch name x, x) | x@(n, _, _, _) <- entries ] run

-- | The topK-threshold half of the M5 differential ('topk-is-per-element',
-- 'dense-inherits-topk'): each recompiles every batched-declaring program at
-- every threshold in 'topKDiffThresholds' (batched, scalar and interpreter
-- variants) and runs the lot through one torch subprocess. Measured at ~30s
-- and ~19s respectively -- the two most expensive individual tests in the
-- whole suite, well out of proportion to the rest of the batched differential
-- (each under 5s). They pin a real behaviour (topK pruning survives the
-- batched/dense lowering) but a narrower one than 'batched-vs-expected'
-- itself, so -- same tradeoff as 'test_planEnumRecTopKAndBC' in
-- TestInternals.hs -- they move to the opt-in Slow group
-- (NEST_SLOW_TESTS=1) rather than taxing every default run.
--
-- The dense checks live here too, 'declared-dense-eligible' and
-- 'dense-matches-expected': every dense-declaring program is `slow` since the
-- tick-redundant corpus programs were demoted (docs-repo task
-- demote-tick-redundant-corpus-programs-to-slow). This group reads the
-- `slow`-headered programs ('IgnoreSlow'), so that a declaration is checked
-- whichever tier its program is in. Only the programs declaring `batched` or
-- `dense` are selected; none of the programs `slow` for their compile cost
-- declares either.
slowBatchedPythonTests :: Corpus -> Manifest -> IO TestTree
slowBatchedPythonTests corpus manifest = corpusSweepAll corpus SweepSpec
  { sweepName = "Slow.BatchedPython (slow)", sweepTier = Slow, sweepSlow = IgnoreSlow
  , sweepSelect = \e -> Batched `elem` ceBackends e || Dense `elem` ceBackends e
  , sweepNote = "dense eligibility and values, and the batched topK differentials, recompiling every batched program per threshold" } $ \entries -> do
  (_, _, eligible, denseDeclared, topkEligible, denseTopK, mpy, _) <- batchedPythonFixtures entries
  mtorch <- traverse (\py -> (,) py <$> torchFingerprint py) mpy
  let denseNames = map (\(n, _, _, _) -> n) denseDeclared
      denseRefused = [ n | n <- denseNames
                         , n `notElem` [ m | (m, src, _, _) <- eligible, not (null (denseEntryPoints src)) ] ]
  return $ testGroup "BatchedPython (slow)" $
    testProperty "declared-dense-eligible" (once (declaredDenseProp (length denseNames) denseRefused))
    : case mtorch of
        Nothing ->
          [ testProperty "torch-python-found" $ once $ ioProperty $
              noTorchProperty "BatchedPython (slow) dense and topK differentials" ]
        Just (py, torch) ->
          [ testProperty "dense-matches-expected" (once (cachedTorch manifest torch "dense-matches-expected" denseDeclared (runBatchedDense False py)))
          , testProperty "dense-inherits-topk" (once (runBatchedDense True py denseTopK))
          , testProperty "topk-is-per-element" (once (runBatchedTopK py topkEligible)) ]

-- | @batched-vs-expected@ under batched reference compliance: a stderr note
-- of how many eligible programs the batched fuzz arm certifies (their rows do
-- not run on the batched backend) and which uncertified constructs keep the
-- rest, then the check over the rest. With none left it passes on the note.
certifiedNote :: [(String, [String])] -> Int -> [a] -> Property -> Property
certifiedNote censuses nEligible routed check = ioProperty $ do
  let uncertified = sort (nub (concatMap snd censuses))
  hPutStrLn stderr ("BatchedPython.batched-vs-expected: " ++ show (nEligible - length routed) ++ " of "
                    ++ show nEligible ++ " eligible programs are certified by the batched fuzz arms; "
                    ++ show (length routed) ++ " run, for " ++ show uncertified)
  return (if null routed then property True else check)

-- | Everything the batched differential needs from one corpus program, or a
-- diagnostic saying why batched mode cannot take it: the three eligibility
-- conditions (a batched 'compile', a 'generateFunctionsBatched' emission, and
-- batchable query samples) plus the precondition that the @.tst@ file has
-- prob/cumulative points at all. Runs in IO so that a compiler @error@ (rather
-- than a @Left@) becomes a named diagnostic instead of derailing the group.
batchedEligibility :: Program -> [TestCase] -> IO (Either String (String, [BatchGroup], [NetMock]))
batchedEligibility p tcs = fmap fst <$> batchedEligibilityCensus p tcs

-- | 'batchedEligibility', with the constructs of the batched compile the
-- batched fuzz arm does not certify ('batchedUncertifiedConstructs').
batchedEligibilityCensus :: Program -> [TestCase] -> IO (Either String ((String, [BatchGroup], [NetMock]), [String]))
batchedEligibilityCensus p tcs = do
  r <- try (evaluate (force (go p tcs))) :: IO (Either SomeException (Either String ((String, [BatchGroup], [NetMock]), [String])))
  return $ either (\e -> Left ("crashed while compiling for batched mode: " ++ show e)) id r
  where
    force res = case res of
      Left msg              -> length msg `seq` res
      Right ((src, gs, nets), c) -> length src `seq` length gs `seq` length nets `seq` length (concat c) `seq` res
    go prog cs = do
      let qtcs = filter (\t -> isProbTestCase t || isCumulTestCase t) cs
          netNames = networkMocks prog
      if null qtcs
        then Left "the .tst file declares no p()/cdf() query points to batch"
        else Right ()
      env <- compile defaultCompilerConfig{batched = True} prog
      srcLines <- generateFunctionsBatched True env
      groups <- maybe (Left "query samples are not structure-of-arrays batchable") Right
                      (batchGroups (collapsedEnumCtors (adts prog) (intercalate "\n" srcLines)) (not (null netNames)) qtcs)
      let census = batchedUncertifiedConstructs (batchedProgramCensus (Right env :: Either () IREnv))
      return ((intercalate "\n" srcLines, groups, netNames), census)

-- | The point of the @batched@ routing token: a program that declares it must
-- still be batched-eligible. Each refusal names the program and quotes the
-- diagnostic.
declaredEligibleProp :: Int -> [(String, String)] -> Property
declaredEligibleProp 0 _ = counterexample
  "no .tst file declares `batched` in its backends header; batched mode has no coverage" False
declaredEligibleProp _ refused = counterexample
  ("programs declaring `batched` in their .tst backends header are no longer batched-eligible:\n"
   ++ unlines [ "  " ++ n ++ ": " ++ msg | (n, msg) <- refused ])
  (null refused)

-- | A visible note (never a failure) for programs batched mode /could/ take but
-- whose @.tst@ file does not say so.
gainNoteProp :: [String] -> Property
gainNoteProp gained = ioProperty $ do
  if null gained
    then return ()
    else hPutStrLn stderr ("BatchedPython: " ++ show (length gained) ++ " program(s) are batched-eligible but do not\n\
      \  declare `batched` in their .tst backends header (add the token to gain coverage):\n"
      ++ unlines [ "    " ++ n | n <- gained ])
  return True

-- ===========================================================================
-- Batched-mode refusal coverage (design pytorch-tensorizer)
-- ===========================================================================

-- | Table-driven coverage of the batched fragment refusals a /real corpus
-- program/ reaches: one row per refused construct, asserting the program
-- compiles fine (so the refusal is genuinely the batched backend's, not an
-- unrelated earlier failure) and only then that 'generateFunctionsBatched'
-- returns 'Left' with a diagnostic naming that construct.
--
-- This group deliberately lives outside 'batchedPythonTests': refusals are pure
-- Haskell and must be checked on a torch-less machine too, whereas the value
-- differential skips itself there (the single predecessor of this table,
-- @refusalProp@, sat inside the torch-gated branch and so never ran without
-- torch). Refusals with no corpus trigger — list membership, the @VAnyExcept@
-- sentinel, a residual (not-at-root) @IRConformsTo@, a composite-'MultiValue'
-- @IRIsPossible@, and generate-only recursion — are covered by the
-- synthetic-IR rows in "TestInternals" (@batchedRefusalUnitTests@), because on
-- any real program another guard always fires first.
batchedRefusalTests :: TestTree
batchedRefusalTests = testGroup "BatchedRefusal" $
  [ testProperty (prog ++ " -- " ++ needle) (once (refusalRow prog needle))
  | (prog, needle) <- batchedRefusalTable ]
  ++ [ testProperty (prog ++ " -- scalar advisory reports eligible")
         (once (ioProperty (advisoryRow prog Nothing <$> (corpusPplPath prog >>= parseProgram))))
     -- The advisory's other direction: on a program batched mode *does* take,
     -- it must stay quiet rather than cry wolf. Two shapes, since the guard has
     -- two independent halves (the per-body fragment walk and the call graph):
     -- a plain scalar program and a neural one whose read-logits network batches.
     | prog <- ["coin", "mNistAdd"] ]

-- | @(corpus program base name, diagnostic substring pinning the construct)@.
-- The substring names the offending IR node rather than quoting prose, so a
-- reworded diagnostic does not break a row, but a *different* refusal firing
-- first does. Every row was read off the actual diagnostic
-- (@stack run -- -i FILE --batched compile -l python@ — note @--batched@ is a
-- global flag and must precede the @compile@ subcommand).
batchedRefusalTable :: [(String, String)]
batchedRefusalTable =
  -- lists. With M1 (design heterogeneous-batch-inference) the list *spine*
  -- operations are in the fragment -- within a shape bucket they are uniform
  -- Python structure over [B] leaves -- so what is refused here is what
  -- bucketing does not rescue. A non-empty list *constant* is in the
  -- fragment since task batched-refuses-list-constants-with-data (spelled as
  -- the runtime's cons structure over constant leaves), so
  -- `listLiteralDeconstruction` and `andInsideListOverDraws` (the `[ANY]` a
  -- per-mask variant introduces) left this table and declare `batched`.
  -- `map`, `mapMultList`, `partialInjFMapPlus` and `wrappedHoAdt` left this
  -- table with task batched-refuses-list-map, and `either_arith_inv`, `injApply`
  -- and `twiceApplication` with task batched-refuses-inner-lambda: a list map is a
  -- Python walk over the bucketed spine and an inner lambda a Python closure.
  -- They declare `batched`.
  -- Either. Since heterogeneous M2 the tag is *structure*: it is part of the
  -- bucket signature, so the constructors, destructors and predicates are all
  -- in the fragment (`either`, `either_const`, `eitherDeconstruction`,
  -- `nestedDeconstruction`, `either_both_cont` are eligible programs now). The
  -- dichotomy's other half -- a value-dependent select between two arms, as
  -- isLeft's inverse in `either_isleft` -- left this table with task
  -- batched-value-dependent-structure-select: the batch is split at the
  -- select ('pythonLibBatched.split_retry'). What the split does not cover (a
  -- per-element structure select inside a tensor map's body) has no corpus
  -- trigger; its refusal is a synthetic-IR row in "TestInternals".
  -- `eitherNeural`'s read-logits network (Either Int Bool) used to be refused here too --
  -- not for the Either shape itself (M2 handles that), but because its Bool
  -- arm's enum-index lookup built an `indexOf(x, [True, False])` call that
  -- 'SPLL.IROptimizer.indexmagic' could not fold (only `[0..n]` naturals lists
  -- folded), so the `VList` constant survived to codegen with no batched
  -- representation. Fixed by task batched-bool-enum-index (indexmagic now
  -- folds any constant scalar enumeration, not just naturals); `eitherNeural`
  -- itself has no `p()`/`cdf()` query points in its `.tst` (argmax_p only), so
  -- it does not appear in the eligible/gained lists either -- it simply drops
  -- out of this refusal table.
  -- ADT declarations: the bail at the top of 'generateFunctionsBatched'
  -- ADTs. The declarations themselves are emittable since heterogeneous M2
  -- (constructor tag = structure = part of the bucket signature), so `adtCoin`,
  -- `recursiveAdt`, `planEnumInline`/`Wide` are eligible programs now. `adt`
  -- and `adtNeuralCounting` used to be refused here for an unrelated reason --
  -- their prob path evaluates a deterministic helper by calling its generate
  -- method -- until task batched-prob-path-calls-helper-generate inlined such
  -- calls ('inlineDetGenCalls'); both are eligible now, and so is `flip`.
  -- prob/integ recursion. Structure-directed recursion is admitted since M1
  -- (its depth is uniform within a shape bucket, so it runs unchanged over [B]
  -- leaves -- `gaussList` is an eligible program now, checked in
  -- 'batchedPythonTests'). Value-dependent recursion left this table with task
  -- batched-value-dependent-recursion: the batch is split at every
  -- value-dependent branch guarding the recursion ('splitStructureSelects',
  -- and 'splitGenRecursion' for generate), so each element recurses as deep as
  -- on the scalar backend -- `dice` (bounded by its batch-uniform parameter)
  -- and `recursionDepthFromSample` (whose guard reads the sample) batch. An
  -- entry call from outside the recursion (`nestedIfEmptyListIntCdf`'s
  -- `main = rec`) is no longer judged as recursion. What the split does not
  -- reach (a recursive call under a select inside a tensor map's body) has no
  -- corpus trigger; its refusal is a synthetic row in "TestInternals".
  -- A prob/integ path reaching a recursive deterministic generator
  -- (`factorial`, the plan-enumeration folds) or a helper's Gaussian
  -- parameters (`normalThroughFunctionNested`) left this table with tasks
  -- batched-prob-path-calls-recursive-helper-gen and
  -- batched-prob-path-calls-helper-normal-params: both are pure callees,
  -- emitted as ordinary batched methods. A call to a *random* recursive
  -- generator is still refused; its only corpus trigger is a known-issues
  -- miscompile (`namedHofRandomFunctionArg`), so it is a synthetic row in
  -- "TestInternals" ('test_batchedPureCallees').
  --
  -- Refusals pinned as open bugs under universal batched admission (task
  -- batched-admission-universal), one row per refusal class without a row
  -- above. Each fails, as every row here does, the day batched mode accepts
  -- the program; the row then leaves the table with its ticket.
  []

-- ===========================================================================
-- Batched ADT-cdf NaN guard (task batched-adt-cdf-refusal-becomes-nan)
-- ===========================================================================
--
-- A cdf() query on an ADT-valued program has no order to integrate along
-- ('SPLL.IRCompiler.compareValueExpr's TADT case), so it answers 'IRError'.
-- Unlike every other 'IRError' arm, this one is not behind a select: it *is*
-- the whole body, so the batched backend's usual "poison() gets selected
-- away by an enclosing torch.where" story does not apply, and the query used
-- to silently answer @NaN@ instead of a refusal. The decision recorded on the
-- task (2026-09-01 review) was not to add a new compile-time refusal --
-- batched mode already has a narrower contract than the scalar backends, and
-- the ADT-cdf refusal is exactly the kind of thing that contract already
-- excludes -- but to make the existing NaN self-diagnosing: every emitted
-- forward/integrate/generate return is routed through
-- @pythonLibBatched.check_result@, which raises naming the two live causes
-- (a malformed float op, or an unmasked @poison()@) rather than returning
-- @NaN@ silently.
--
-- 'adtValuedProgSrc' in "TestRejection" pins the *scalar*/interpreter refusal
-- on a recursive ADT (@DTree@), which is batched-ineligible for an unrelated
-- reason (value-dependent recursion) and so cannot see this at all. This
-- fixture is deliberately non-recursive so it stays batched-eligible.

-- | Two nullary constructors, no recursion -- the smallest program whose
-- query type is a TADT and which batched mode actually accepts.
adtCdfCoinSrc :: String
adtCdfCoinSrc = unlines
  [ "data Coin = Heads | Tails"
  , "main = if Uniform < 0.3 then Heads else Tails"
  ]

-- | Compile 'adtCdfCoinSrc' for batched mode, or fail the property naming
-- where the pipeline broke (parse/compile/batched-emission), so a genuine
-- regression in an earlier stage does not masquerade as this guard missing.
compiledAdtCdfCoin :: IO (Either String [String])
compiledAdtCdfCoin = return $ do
  p <- either (Left . ("fixture failed to parse: " ++) . show) Right
              (tryParseProgram "" adtCdfCoinSrc)
  env <- either (Left . ("fixture failed to compile: " ++)) Right
                (compile defaultCompilerConfig{batched = True} p)
  let refusalPrefix = "batched mode refused the non-recursive ADT fixture (it "
                    ++ "should be eligible -- see adtCdfCoinSrc's header): "
  either (Left . (refusalPrefix ++)) Right (generateFunctionsBatched True env)

batchedAdtCdfNaNGuardTests :: TestTree
batchedAdtCdfNaNGuardTests = testGroup "batched ADT-cdf NaN guard" $
  [ testProperty "the emitted integrate body routes its return through check_result, not a bare poison()" $
      once $ ioProperty $ do
        res <- compiledAdtCdfCoin
        return $ case res of
          Left err -> counterexample err False
          Right srcLines ->
            let code = unlines srcLines in
            counterexample ("expected \"return check_result(\" somewhere in main's integrate "
                            ++ "method; got:\n" ++ code)
              ("return check_result(" `isInfixOf` code)
  , testProperty "running it raises a diagnostic naming the poison, instead of returning NaN" $
      once $ ioProperty $ do
        mpy <- findTorchPython
        case mpy of
          Nothing -> noTorchProperty "batched ADT-cdf NaN guard"
          Just py -> do
            res <- compiledAdtCdfCoin
            case res of
              Left err -> return (counterexample err False)
              Right srcLines -> do
                cwd <- getCurrentDirectory
                let code = unlines srcLines
                    script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ code
                      ++ unlines
                         [ "try:"
                         , "    r = main.integrate(Heads())"
                         , "    print('NO_EXCEPTION:' + repr(r))"
                         , "except Exception as e:"
                         , "    print('EXCEPTION:' + str(e))"
                         ]
                (exitCode, out, err) <- withSystemTempFile "adt_cdf_nan_guard.py" $ \tmpPath tmpHandle -> do
                  hPutStr tmpHandle script
                  hClose tmpHandle
                  readProcessWithExitCode py [tmpPath] ""
                return $ case exitCode of
                  ExitFailure _ -> counterexample ("script crashed instead of catching the exception:\n" ++ out ++ err) False
                  ExitSuccess
                    | "NO_EXCEPTION" `isPrefixOf` out ->
                        counterexample ("cdf() on the ADT-valued fixture returned a value instead of raising: " ++ out) False
                    | not ("EXCEPTION:" `isPrefixOf` out) ->
                        counterexample ("unexpected script output:\n" ++ out ++ err) False
                    | not ("poison()" `isInfixOf` out) ->
                        counterexample ("raised, but the message does not name the unmasked poison() as a cause:\n" ++ out) False
                    | otherwise -> property True
  ]

-- ===========================================================================
-- Wide neural domains (task neural-categorical-sampler-nests-v-deep)
-- ===========================================================================

-- | A read-logits network's categorical sampler used to be emitted as one
-- nested @if@/@else@ per domain value, re-summing the remaining weights at
-- each level. CPython refuses a module past 100 indentation levels, so any
-- @neural@ declaration with 99 or more values produced a Python module that
-- failed at /import/ -- 'forward' included, since the helper is emitted with
-- or without @-G@. The known-issues corpus cannot pin this: it runs programs
-- through the interpreter, which has no indentation limit.
--
-- So these compile a 250-value declaration to scalar Python and run it. 250 is past
-- the old 98-value ceiling, and past 200, where @main@'s writeLogits -- one
-- @main.forward(v, img)[0]@ cell per value, consed right-nested -- used to
-- trip CPython's parenthesis limit and fail the import the same way (task
-- writelogits-cons-chain-nests-v-deep; the scalar backend now spills that
-- chain, see 'SPLL.CodeGenPyTorch.spillable'). The scalar case also reads the
-- writeLogits vector back. The batched case runs at 250 too, and reads the
-- probability back as well as drawing: its table domain's value-to-slot
-- lookup used to be a nested @where_anchored@ chain V deep in the same way,
-- and is now one flat @table_select@ (task
-- batched-table-domain-lookup-nests-v-deep). The network is a mock returning a
-- one-hot weight vector, so the draw is deterministic whatever the random
-- stream does, and a wrong slot or a wrong slot-to-value mapping fails
-- outright rather than statistically.
--
-- Two domains, one per slot-to-value mapping in 'SPLL.AutoNeural.lottery':
-- a contiguous 0-based range (the slot is the value) and an even-number one
-- (read out of a constant table).
wideNeuralDomainTests :: TestTree
wideNeuralDomainTests = testGroup "wide neural domain (neural-categorical-sampler-nests-v-deep)"
  [ testGroup "Python" [ testProperty name (once (scalarCase domain)) | (name, domain) <- domains 250 ]
  , testGroup "BatchedPython" [ testProperty name (once (batchedCase domain)) | (name, domain) <- domains 250 ]
  ]
  where
    hot = 137 :: Int
    domains :: Int -> [(String, [Int])]
    domains width = [ ("contiguous 0.." ++ show (width - 1), [0 .. width - 1])
                    , ("table 0,2.." ++ show (2 * (width - 1)), [0, 2 .. 2 * (width - 1)]) ]
    src domain = unlines
      [ "neural readDigit :: (Symbol -> Int) of [" ++ intercalate ", " (map show domain) ++ "]"
      , "main img = readDigit img" ]
    compiled batchedMode domain = do
      p <- either (Left . ("fixture failed to parse: " ++) . show) Right (tryParseProgram "" (src domain))
      either (Left . ("fixture failed to compile: " ++)) Right
             (compile defaultCompilerConfig{batched = batchedMode} p)
    oneHot domain = "[" ++ intercalate ", " [ if i == hot then "1.0" else "0.0" | i <- [0 .. length domain - 1] ] ++ "]"
    runScript py name script = do
      (code, out, err) <- withSystemTempFile name $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle script
        hClose tmpHandle
        readProcessWithExitCode py [tmpPath] ""
      return $ case code of
        ExitSuccess -> property True
        ExitFailure _ -> counterexample ("the emitted module failed:\n" ++ out ++ err) False
    scalarCase domain = ioProperty $ case compiled False domain of
      Left err -> return (counterexample err False)
      Right env -> do
        cwd <- getCurrentDirectory
        let code = unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n")
                                   (pack (intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True env))))
        runScript "python3" "wide_neural_domain.py" $ unlines
          [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", code
          , "def readDigit(s):", "    return s"
          , "w = " ++ oneHot domain
          , "for _ in range(20):"
          , "    r = main.generate(w)"
          , "    if r != " ++ show (domain !! hot) ++ ":"
          , "        raise ValueError('generate drew ' + repr(r) + ', expected " ++ show (domain !! hot) ++ "')"
          , "if abs(main.forward(" ++ show (domain !! hot) ++ ", w)[0] - 1.0) > 1e-9:"
          , "    raise ValueError('forward disagrees with the one-hot network')"
          , "logits, cell = [], main.writeLogits(w)"
          , "while isinstance(cell, ConsInferenceList):"
          , "    logits.append(cell.value)"
          , "    cell = cell.next"
          , "if logits != w:"
          , "    raise ValueError('writeLogits does not return the one-hot vector: ' + repr(logits))"
          ]
    batchedCase domain = ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> noTorchProperty "wide neural domain: batched case"
        Just py -> case compiled True domain >>= generateFunctionsBatched True of
          Left err -> return (counterexample err False)
          Right srcLines -> do
            cwd <- getCurrentDirectory
            runScript py "wide_neural_domain_batched.py" $ unlines
              [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", unlines srcLines
              , "import torch"
              , "def readDigit(s):", "    return s"
              , "B = 64"
              , "w = torch.tensor(" ++ oneHot domain ++ ").expand(B, -1)"
              , "r = main.generate(w, B)"
              , "if not bool((torch.as_tensor(r) == " ++ show (domain !! hot) ++ ").all()):"
              , "    raise ValueError('batched generate drew ' + repr(r) + ', expected all " ++ show (domain !! hot) ++ "')"
              , "q = torch.tensor([" ++ show (domain !! hot) ++ ", " ++ show (domain !! (hot + 1)) ++ "]).repeat(B // 2)"
              , "p = torch.as_tensor(main.forward(q, w)[0])"
              , "if not bool((p == torch.tensor([1.0, 0.0], dtype=p.dtype).repeat(B // 2)).all()):"
              , "    raise ValueError('batched forward disagrees with the one-hot network: ' + repr(p))"
              ]

-- ===========================================================================
-- Deep expressions are spilled (task python-codegen-exceeds-parser-nesting-limit)
-- ===========================================================================
--
-- CPython refuses a line nested more than 200 brackets deep, and the IR builds
-- long sums right-nested with every level parenthesised, so a plan route with
-- ~190 top-level worlds compiled to a module that could not be imported. The
-- scalar backend now let-binds deep pure subterms of such a line into
-- temporaries, and leaves every line that already parsed alone.
--
-- The fixture is hand-built IR rather than a program, since the smallest
-- program known to reach the limit (isbn_checksum at depth 6) takes minutes to
-- compile. One summand is a laziness canary: its arm divides by zero and its
-- guard is never true, so hoisting the arm out of the conditional (rather than
-- the whole conditional) raises at import-and-call time.
deepExpressionSpillTests :: TestTree
deepExpressionSpillTests = testGroup "deep expression spill (python-codegen-exceeds-parser-nesting-limit)"
  [ testProperty "a 300-term sum imports and evaluates" (once deepCase)
  , testProperty "a 60-term sum is emitted without spilling" (once shallowCase)
  , testProperty "a 300-term sum whose guarded arms bind a let imports and evaluates" (once letArmCase)
  , testProperty "a comprehension whose body is too deep becomes a loop, imports and evaluates" (once deepComprehensionCase)
  , testProperty "a shallow comprehension stays a comprehension" (once shallowComprehensionCase)
  , testProperty "24 nested noisy ifs over an enumerated draw import and match the idealized value" (once enumIfChainCase)
  , testGroup "BatchedPython"
      [ testProperty "24 nested noisy ifs over an enumerated draw import batched and match the idealized value" (once enumIfChainBatchedCase) ]
  , testProperty "a too-deep comprehension nested in another's body becomes nested loops, imports and evaluates" (once nestedComprehensionCase)
  , testProperty "a chain of 11 two-field answers under an enumerated latent imports and matches the idealized values" (once chainedAnswersCase)
  ]
  where
    x = IRVar "x"
    lit = IRConst . VFloat
    term i = IRIf (IROp OpGreaterThan x (lit i)) (lit 1.0) (lit 0.0)
    canary = IRIf (IROp OpGreaterThan x (lit 1.0e9)) (IROp OpDiv (lit 1.0) (lit 0.0)) (lit 0.0)
    sumOf n = foldr1 (IROp OpPlus) (canary : map (term . fromIntegral) [1 .. n :: Int])
    -- Task plan-fold-enum-mass-sum-exceeds-parser-nesting: a plan-path fold's
    -- enumerated mass is a right-nested sum of guarded summands whose arms
    -- carry CSE lets. The let is scoped inside its summand, so the summand is
    -- still pure arithmetic and the spine above it must stay spillable. The
    -- canary's let value divides by zero, so hoisting the let out of its arm
    -- (rather than moving the whole conditional) raises.
    letName i = "l_" ++ show i
    letTerm i = IRIf (IROp OpGreaterThan x (lit (fromIntegral i)))
                     (IRLetIn (letName i) (IROp OpMult x (lit 0.0))
                              (IROp OpPlus (IRVar (letName i)) (lit 1.0)))
                     (lit 0.0)
    letCanary = IRIf (IROp OpGreaterThan x (lit 1.0e9))
                     (IRLetIn "l_canary" (IROp OpDiv (lit 1.0) (lit 0.0)) (IRVar "l_canary"))
                     (lit 0.0)
    letSumOf n = foldr1 (IROp OpPlus) (letCanary : map letTerm [1 .. n :: Int])
    -- Task python-emitted-expression-exceeds-parser-nesting: an enumerated
    -- draw sums a comprehension, @sum([body for b in xs])@, and the depth is
    -- inside the body, where nothing can be cut out of the line. The body here
    -- is a chain of lets and guarded conditionals, as the optimizer emits for
    -- nested ifs over the latent: level k is
    -- @let c_k = x * 1 in (if c_k > 0 then c_k + level (k-1) else 1/0)@, so
    -- over x in [1, 2] it sums to 3k. The never-taken arm is a laziness
    -- canary. The comprehension's variable is also named @x@, like the
    -- function's parameter, and the line adds the outer @x@ after the sum: a
    -- loop that bound @x@ itself would clobber the parameter.
    compLevel :: Int -> IRExpr
    compLevel 0 = lit 0.0
    compLevel k = let c = IRVar ("c_" ++ show k)
                  in IRLetIn ("c_" ++ show k) (IROp OpMult x (lit 1.0))
                       (IRIf (IROp OpGreaterThan c (lit 0.0))
                             (IROp OpPlus c (compLevel (k - 1)))
                             (IROp OpDiv (lit 1.0) (lit 0.0)))
    comprehensionSum k =
      IROp OpPlus
        (IRBuiltin (BReduce ROpAdd 0)
          [IRBuiltin BMap [ IRLambda "x" (compLevel k)
                          , IRBuiltin (BTensor [EFixed 2]) [lit 1.0, lit 2.0] ]])
        x
    comprehensionSource k = sourceOf (envWith (comprehensionSum k))
    envOf n = envWith (sumOf n)
    envWith body = IREnv [IRFunGroup { groupName = "main", refusedVariants = [], genFun = Nothing
                                , probFun = Just (IRLambda "x" body, "")
                                , integFun = Nothing, writeLogitsFun = Nothing
                                , normalFun = Nothing, groupDoc = "", sampleDomain = Nothing, maskVariantOf = Nothing }] [] []
    source n = sourceOf (envOf n)
    sourceOf = torchFreePythonModule
    spillLines = filter (isPrefixOf "_s" . dropWhile (== ' ')) . lines
    deepCase = runsTo (source 300)
    letArmCase = runsTo (sourceOf (envWith (letSumOf 300)))
    runsTo src = ioProperty $ do
      cwd <- getCurrentDirectory
      (code, out, err) <- withSystemTempFile "deep_expression_spill.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle $ unlines
          [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", src
          , "for q, want in [(150.5, 150.0), (-1.0, 0.0), (1000.0, 300.0)]:"
          , "    got = main.forward(q)"
          , "    if got != want:"
          , "        raise ValueError('forward(%r) = %r, expected %r' % (q, got, want))"
          ]
        hClose tmpHandle
        readProcessWithExitCode "python3" [tmpPath] ""
      return $ counterexample ("the emitted module failed:\n" ++ out ++ err)
                 (code == ExitSuccess)
          .&&. counterexample "no spill temporaries were emitted" (not (null (spillLines src)))
    shallowCase = let src = source 60
                  in counterexample src (null (spillLines src))
    deepComprehensionCase = ioProperty $ do
      let depth = 80
          src = comprehensionSource depth
      cwd <- getCurrentDirectory
      (code, out, err) <- withSystemTempFile "deep_comprehension_spill.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle $ unlines
          [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", src
          , "for q in [10.0, 0.5]:"
          , "    got = main.forward(q)"
          , "    want = " ++ show (3 * fromIntegral depth :: Double) ++ " + q"
          , "    if got != want:"
          , "        raise ValueError('forward(%r) = %r, expected %r' % (q, got, want))"
          ]
        hClose tmpHandle
        readProcessWithExitCode "python3" [tmpPath] ""
      return $ counterexample ("the emitted module failed:\n" ++ out ++ err ++ "\n" ++ src)
                 (code == ExitSuccess)
          .&&. counterexample ("the comprehension was not turned into a loop:\n" ++ src)
                 (any (isPrefixOf "for _v" . dropWhile (== ' ')) (lines src))
    -- The ticket's own repro (formerly the known-issues pin
    -- enumLetFreshIfChainPythonParenDepth), through the real pipeline: 24
    -- nested ifs whose conditions are noisy reads of one enumerated latent.
    -- Before the fix its enum-mass line was 200+ brackets deep. It stays out
    -- of the corpus because the corpus's BudgetZeroMatchesDefault sweep
    -- recompiles it at materialization budget 0, whose engines are exponential
    -- in the depth (N = 8 takes over 2 minutes; task
    -- budget-zero-exponential-in-nested-enum-ifs). Batched codegen, the
    -- original blocker, now compiles it in under a second (task
    -- batched-codegen-exponential-in-nested-enum-ifs); its corpus twin at
    -- depth 6 is enumerability/noisyIfChainOverDraw6.
    enumIfChainLevels = 24 :: Int
    enumIfChainProgram =
      let cond = "(if Uniform < 0.1 then (not b) else b)"
          chain = iterate (\e -> "(if " ++ cond ++ " then " ++ e ++ " else False)") "True" !! enumIfChainLevels
      in "main = draw b = Uniform < 0.5 in " ++ chain
    enumIfChainPTrue = 0.5 * 0.9 ^ enumIfChainLevels + 0.5 * 0.1 ^ enumIfChainLevels :: Double
    enumIfChainCase = ioProperty $ do
      let progSrc = enumIfChainProgram
          pTrue = enumIfChainPTrue
      case either (Left . show) Right (tryParseProgram "" progSrc) >>= compile defaultCompilerConfig of
        Left err -> return (counterexample ("fixture failed to compile: " ++ err) False)
        Right env -> do
          let src = sourceOf env
          cwd <- getCurrentDirectory
          (code, out, err) <- withSystemTempFile "enum_if_chain.py" $ \tmpPath tmpHandle -> do
            hPutStr tmpHandle $ unlines
              [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", src
              , "for q, want in [(True, " ++ show pTrue ++ "), (False, " ++ show (1 - pTrue) ++ ")]:"
              , "    got = main.forward(q)[0]"
              , "    if abs(got - want) > " ++ show probTolerance ++ ":"
              , "        raise ValueError('forward(%r) = %r, expected %r' % (q, got, want))"
              ]
            hClose tmpHandle
            readProcessWithExitCode "python3" [tmpPath] ""
          return $ counterexample ("the emitted module failed:\n" ++ out ++ err)
                     (code == ExitSuccess)
    -- Task batched-enum-comprehension-exceeds-parser-nesting: the same
    -- program through the batched backend, whose enum-mass line
    -- @tensor_sum([body for b in xs])@ was 200+ brackets deep. It is spilled
    -- into a loop over the domain, with the domain still a literal so the
    -- latent's structural reads stay Python conditionals.
    enumIfChainBatchedCase = ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> noTorchProperty "deep expression spill: batched enum if chain"
        Just py ->
          case either (Left . show) Right (tryParseProgram "" enumIfChainProgram)
                 >>= compile defaultCompilerConfig{batched = True} >>= generateFunctionsBatched True of
            Left err -> return (counterexample ("fixture failed to compile: " ++ err) False)
            Right srcLines -> do
              cwd <- getCurrentDirectory
              (code, out, err) <- withSystemTempFile "enum_if_chain_batched.py" $ \tmpPath tmpHandle -> do
                hPutStr tmpHandle $ unlines
                  [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")", unlines srcLines
                  , "import torch"
                  , "got = torch.as_tensor(main.forward(torch.tensor([True, False, True]))[0])"
                  , "want = torch.tensor([" ++ show enumIfChainPTrue ++ ", " ++ show (1 - enumIfChainPTrue)
                      ++ ", " ++ show enumIfChainPTrue ++ "], dtype=got.dtype)"
                  , "if not bool(((got - want).abs() <= " ++ show probTolerance ++ ").all()):"
                  , "    raise ValueError('batched forward = %r, expected %r' % (got, want))"
                  ]
                hClose tmpHandle
                readProcessWithExitCode py [tmpPath] ""
              return $ counterexample ("the emitted module failed:\n" ++ out ++ err)
                         (code == ExitSuccess)
                  .&&. counterexample "the enum-mass comprehension was not spilled into a loop over the literal domain"
                         (any (\l -> "for _v" `isPrefixOf` dropWhile (== ' ') l && " in [True, False]:" `isInfixOf` l)
                              (concatMap lines srcLines))
    shallowComprehensionCase =
      let src = comprehensionSource 5
      in counterexample src (" for x in " `isInfixOf` src && null (spillLines src))
    -- Task chained-answers-exceed-python-paren-depth: an enumerated draw's
    -- comprehension whose body holds another enumerated draw's comprehension.
    -- The inner one sits under the outer one's binder, out of the spill's
    -- reach, so the outer one has to move whole -- which needs a pure
    -- comprehension to count as pure. Over y in [1, 2]:
    -- (1 + 3k) + (2 + 3k), plus the parameter.
    nestedComprehensionCase = ioProperty $ do
      let depth = 80
          outer = IROp OpPlus
                    (IRBuiltin (BReduce ROpAdd 0)
                      [IRBuiltin BMap [ IRLambda "y" (IROp OpPlus (IRVar "y") (comprehensionSum depth))
                                      , IRBuiltin (BTensor [EFixed 2]) [lit 1.0, lit 2.0] ]])
                    x
          -- 'comprehensionSum' adds @x@ after its sum, outside its own
          -- binder: the parameter, once per outer element. Its inner loop
          -- also binds @x@, so a loop that kept the name would clobber it.
          src = sourceOf (envWith outer)
          loops = length (filter (isPrefixOf "for _v" . dropWhile (== ' ')) (lines src))
      (code, out, err) <- runPythonChecks "nested_comprehension_spill.py" src
        [ "for q in [10.0, 0.5]:"
        , "    got = main.forward(q)"
        , "    want = " ++ show (3 + 6 * fromIntegral depth :: Double) ++ " + 3 * q"
        , "    if got != want:"
        , "        raise ValueError('forward(%r) = %r, expected %r' % (q, got, want))"
        ]
      return $ counterexample ("the emitted module failed:\n" ++ out ++ err ++ "\n" ++ src)
                 (code == ExitSuccess)
          .&&. counterexample ("expected both comprehensions as loops, got " ++ show loops ++ ":\n" ++ src)
                 (loops == 2)
    -- The ticket's repro (formerly the known-issues pin
    -- chainedAnswersPythonParenDepth): an enumerated coin, twelve readings
    -- gated on it, and 11 overlapping two-field answers. Ten loaded before the
    -- fix, eleven did not. Values idealized by brute force over the 2^12
    -- readings. Kept out of the corpus for its compile cost (a few seconds at
    -- 11, growing ~1.6x per question in the compiler, not in codegen).
    chainedAnswersCase = ioProperty $ do
      let n = 11 :: Int
          reading i = "  draw h" ++ show i ++ " = (if s then Uniform < 0.9 else Uniform < 0.2) in"
          answer i | even i    = "(if h" ++ show i ++ " then True else h" ++ show (i + 1) ++ ")"
                   | otherwise = "(if h" ++ show i ++ " then h" ++ show (i + 1) ++ " else False)"
          progSrc = unlines (["main =", "  draw s = Uniform < 0.5 in"] ++ map reading [0 .. n]
                             ++ ["  (s, [" ++ intercalate ", " (map answer [0 .. n - 1]) ++ "])"])
          rows = [ ("T(True, L([True] * 11))", 0.17433922005000008 :: Double)
                 , ("T(False, L([True] * 11))", 5.120000000000003e-08)
                 , ("T('ANY', L([True, False] * 5 + [True]))", 8.75121185e-05) ]
      case either (Left . show) Right (tryParseProgram "" progSrc) >>= compile defaultCompilerConfig of
        Left err -> return (counterexample ("fixture failed to compile: " ++ err) False)
        Right env -> do
          (code, out, err) <- runPythonChecks "chained_answers.py" (sourceOf env) $
            [ "def L(xs):"
            , "    r = EmptyInferenceList()"
            , "    for v in reversed(xs): r = ConsInferenceList(v, r)"
            , "    return r"
            ] ++ concat
            [ [ "got = main.forward(" ++ q ++ ")[0]"
              , "if abs(got - " ++ show want ++ ") > " ++ show probTolerance ++ ":"
              , "    raise ValueError(" ++ show ("forward(" ++ q ++ ") = %r, expected " ++ show want) ++ " % got)" ]
            | (q, want) <- rows ]
          return $ counterexample ("the emitted module failed:\n" ++ out ++ err)
                     (code == ExitSuccess)

-- | The scalar Python module for an 'IREnv', with torch's @Module@ replaced by
-- a stub so that a plain @python3@ can import it.
torchFreePythonModule :: IREnv -> String
torchFreePythonModule env =
  unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n")
                  (pack (intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True env))))

-- | Run a module followed by check lines under @python3@, with the repository
-- root (where @pythonLib.py@ lives) on the path.
runPythonChecks :: String -> String -> [String] -> IO (ExitCode, String, String)
runPythonChecks name src checks = do
  cwd <- getCurrentDirectory
  withSystemTempFile name $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle $ unlines (["import sys", "sys.path.insert(0, " ++ show cwd ++ ")", src] ++ checks)
    hClose tmpHandle
    readProcessWithExitCode "python3" [tmpPath] ""

-- ===========================================================================
-- A let in a comprehension iterable
-- (task backends-agree-python-walrus-in-comprehension-iterable)
-- ===========================================================================
--
-- CPython refuses an assignment expression anywhere in a comprehension's
-- iterable, and at -O2 the cumulative of an int product compiled its
-- materialized cell list, whose cells carry CSE lets, into exactly that, so
-- the module did not load. The corpus program pins the answers on the
-- interpreter, but its constructs are all certified by the agreement
-- fuzzers, so the corpus does not run it on Python; this does. The IR-level
-- cases (scalar, Julia and batched) are in "IRFuzz".
comprehensionIterableLetTests :: TestTree
comprehensionIterableLetTests = testGroup "let in a comprehension iterable (backends-agree-python-walrus-in-comprehension-iterable)"
  [ testProperty name $ once $ ioProperty $ do
      prog <- corpusPplPath name >>= parseProgram
      (_, _, _, tcs) <- corpusTstPath name >>= parseTestCases
      let env = compile defaultCompilerConfig prog
          bindsAnIterable = either (const False) (isInfixOf "((_it" . torchFreePythonModule) env
      return $ counterexample "the module binds no comprehension iterable, so this no longer reaches the fix"
                 bindsAnIterable
          .&&. testPython [] env tcs
  ]
  where name = "intProductLetInComprehensionIterable"

-- ===========================================================================
-- Deeply indented blocks are hoisted
-- (task python-nested-conditionals-exceed-indentation-limit)
-- ===========================================================================
--
-- CPython refuses a line indented 100 levels deep, and statement emission
-- indents once per conditional nested in an arm, so ~97 nested ifs made a
-- module that could not be imported. A method that deep is now regenerated
-- with its deep arms hoisted into flat, closure-converted local functions.
--
-- The fixture chain is hand-built IR: level k binds @c_k = v * 1@ and branches
-- on @c_k > 0@ into level k-1, else 0. The innermost arm reads both the
-- innermost and the outermost let, so it needs variables bound on either side
-- of every hoist, and carries a laziness canary (a division by zero behind a
-- guard that never holds). Over v > 0 the chain is 2v.
deepIndentationHoistTests :: TestTree
deepIndentationHoistTests = testGroup "deep indentation hoist (python-nested-conditionals-exceed-indentation-limit)"
  [ testProperty "a returned 150-deep if chain imports and evaluates" (once (chainCase "return" (chainEnv returned 150)))
  , testProperty "a let-bound 150-deep if chain imports and evaluates" (once (chainCase "let" (chainEnv letBound 150)))
  , testProperty "a comprehension over a 150-deep if chain imports and evaluates" (once comprehensionCase)
  , testProperty "a 60-deep if chain is emitted without hoisting" (once shallowCase)
  , testProperty "100 nested ifs compile through the pipeline and match the idealized value" (once pipelineCase)
  ]
  where
    lit = IRConst . VFloat
    x = IRVar "x"
    cName k = "c_" ++ show k
    chain :: String -> Int -> IRExpr
    chain v n = go n
      where
        go k = IRLetIn (cName k) (IROp OpMult (IRVar v) (lit 1.0))
                 (IRIf (IROp OpGreaterThan (IRVar (cName k)) (lit 0.0)) (inner k) (lit 0.0))
        inner 1 = IRIf (IROp OpGreaterThan (IRVar (cName (1 :: Int))) (lit 1.0e9))
                       (IROp OpDiv (lit 1.0) (lit 0.0))
                       (IROp OpPlus (IRVar (cName (1 :: Int))) (IRVar (cName n)))
        inner k = go (k - 1)
    returned = chain "x"
    -- 'generateLetInStatement' rather than 'generateStatementBlock': the arms
    -- assign @r@ instead of returning.
    letBound n = IRLetIn "r" (chain "x" n) (IROp OpPlus (IRVar "r") (lit 1.0))
    chainEnv body n = IREnv [IRFunGroup { groupName = "main", refusedVariants = [], genFun = Nothing
                                        , probFun = Just (IRLambda "x" (body n), "")
                                        , integFun = Nothing, writeLogitsFun = Nothing
                                        , normalFun = Nothing, groupDoc = "", sampleDomain = Nothing, maskVariantOf = Nothing }] [] []
    hoists = length . filter (isPrefixOf "def _h" . dropWhile (== ' ')) . lines
    expectRuns name src checks = ioProperty $ do
      (code, out, err) <- runPythonChecks name src checks
      return $ counterexample ("the emitted module failed:\n" ++ out ++ err) (code == ExitSuccess)
          -- A hoist per ~32 levels; one per level would be hoisting every arm.
          .&&. counterexample ("expected between 1 and 6 hoisted functions, got " ++ show (hoists src))
                 (hoists src >= 1 && hoists src <= 6)
    check q want = [ "got = main.forward(" ++ show q ++ ")"
                   , "if got != " ++ show want ++ ": raise ValueError('forward(%r) = %r, expected %r' % ("
                       ++ show q ++ ", got, " ++ show want ++ "))" ]
    chainCase kind env =
      let offset = if kind == "let" then 1.0 else 0.0 :: Double
      in expectRuns "deep_indent_chain.py" (torchFreePythonModule env)
           (check (3.0 :: Double) (6.0 + offset) ++ check (-1.0 :: Double) offset)
    -- Statement-level loops come from the bracket spill: the comprehension's
    -- body renders 150 brackets deep, so it becomes a loop, whose body is then
    -- too deeply indented and is hoisted. Over y in [1, 2] plus x: 2 + 4 + x.
    comprehensionCase =
      let body = IROp OpPlus
                   (IRBuiltin (BReduce ROpAdd 0)
                      [IRBuiltin BMap [ IRLambda "y" (chain "y" 150)
                                      , IRBuiltin (BTensor [EFixed 2]) [lit 1.0, lit 2.0] ]])
                   x
          src = torchFreePythonModule (chainEnv (const body) (0 :: Int))
      in expectRuns "deep_indent_loop.py" src (check (0.5 :: Double) (6.5 :: Double))
    shallowCase = let src = torchFreePythonModule (chainEnv returned 60)
                  in counterexample src (hoists src == 0)
    -- The former known-issues pin ifChain100PythonIndentDepth: the generator
    -- (a return-form chain) and the probability method both nest 100 deep.
    pipelineCase = ioProperty $ do
      let levels = 100 :: Int
          progSrc = "main = " ++ iterate (\e -> "(if Uniform < 0.99 then " ++ e ++ " else False)") "True" !! levels
          pTrue = 0.99 ^ levels :: Double
      case either (Left . show) Right (tryParseProgram "" progSrc) >>= compile defaultCompilerConfig of
        Left err -> return (counterexample ("fixture failed to compile: " ++ err) False)
        Right env -> do
          (code, out, err) <- runPythonChecks "deep_indent_pipeline.py" (torchFreePythonModule env)
            [ "for q, want in [(True, " ++ show pTrue ++ "), (False, " ++ show (1 - pTrue) ++ ")]:"
            , "    got = main.forward(q)[0]"
            , "    if abs(got - want) > " ++ show probTolerance ++ ":"
            , "        raise ValueError('forward(%r) = %r, expected %r' % (q, got, want))"
            , "assert main.generate() in (True, False)"
            ]
          return $ counterexample ("the emitted module failed:\n" ++ out ++ err) (code == ExitSuccess)

-- ===========================================================================
-- Batched code is linear in nested tuple-valued selects
-- (task batched-codegen-exponential-in-nested-enum-ifs)
-- ===========================================================================
--
-- Nested ifs over noisy reads of one enumerated latent make every level a
-- tuple-valued select whose arms carry let-spines. Distributing such a select
-- into its tuple leaves used to copy the spines into every leaf, and a spine
-- holding the next level's select copied that one's too: 4^N emitted code (N
-- = 8 took 29 s and 42 MB, N = 24 did not finish). The spines are now hoisted
-- above the select, so doubling the depth roughly doubles the output (the old
-- emission failed this check at 169 KB -> 42 MB, in about 30 s). Pure
-- Haskell (compile + emit), no torch; the program's batched values are checked
-- by the corpus twin enumerability/noisyIfChainOverDraw6.

batchedNestedSelectTests :: TestTree
batchedNestedSelectTests = testGroup "batched nested select distribution (batched-codegen-exponential-in-nested-enum-ifs)"
  [ testProperty "doubling the depth of a nested noisy if chain at most triples the batched output (depth 4 -> 8)" $
      once $ case (emitted 4, emitted 8) of
        (Right small, Right big) ->
          counterexample ("batched output: " ++ show small ++ " chars at depth 4, "
                          ++ show big ++ " at depth 8") (big <= 3 * small)
        (Left err, _) -> counterexample err False
        (_, Left err) -> counterexample err False
  ]
  where
    cond = "(if Uniform < 0.1 then (not b) else b)"
    chain levels = iterate (\e -> "(if " ++ cond ++ " then " ++ e ++ " else False)") "True" !! levels
    emitted :: Int -> Either String Int
    emitted levels = do
      prog <- either (Left . show) Right (tryParseProgram "" ("main = draw b = Uniform < 0.5 in " ++ chain levels))
      env <- either (Left . show) Right (compile defaultCompilerConfig{batched = True} prog)
      srcLines <- generateFunctionsBatched True env
      return (sum (map length srcLines))

-- ===========================================================================
-- Normal upper tails keep their relative precision
-- (task cumulative-normal-upper-tail-cancellation)
-- ===========================================================================
--
-- @P(Normal > z)@ used to be @1 - Phi(z)@, with @Phi@ itself spelled
-- @(1 + erf(z / sqrt 2)) / 2@: both cancel, so a tail of size @P@ kept about
-- @1e-16 / P@ of relative precision (@P(Normal > 8)@ answered 6.66e-16 for
-- 6.22e-16, and Julia's 5-term erf was worse still). Now the compiler spells
-- the complement of a normal CDF leaf as the leaf at @-z@
-- ('SPLL.Semiring.upperTailComplement', 'SPLL.Semiring.complementWhen') and
-- every runtime computes @Phi(x) = erfc(-x / sqrt 2) / 2@.
--
-- The corpus cannot pin this: its tolerance is 1e-4 absolute, which a 1e-16
-- answer passes whatever it is. So each case is checked to 1e-12 relative
-- (linear) or 1e-12 absolute on the log (@--logSpace@), on the interpreter
-- and every text backend, one process per backend. The cases cover each
-- complement site: the four deterministic-bound comparisons, an affine
-- operand, a decreasing transform ('SPLL.Semiring.scaleCoV''s flip, in both
-- a comparison and a plain cdf), and the two-normal comparison. The shift
-- in the last one is itself rounded, so its reference is the CDF at the
-- rounded difference.

-- | (label, source, cumulative query?, query point, exact probability)
normalTailCases :: [(String, String, Bool, IRValue, Double)]
normalTailCases =
  [ ("Normal > 8",                 "main = Normal > 8.0",                 False, VBool True,   q8)
  , ("Normal > 5",                 "main = Normal > 5.0",                 False, VBool True,   q5)
  , ("8 < Normal",                 "main = 8.0 < Normal",                 False, VBool True,   q8)
  , ("Normal < 8 is False",        "main = Normal < 8.0",                 False, VBool False,  q8)
  , ("8 > Normal is False",        "main = 8.0 > Normal",                 False, VBool False,  q8)
  , ("affine operand",             "main = Normal * 2.0 + 3.0 > 19.0",    False, VBool True,   q8)
  , ("decreasing operand",         "main = Normal * (0.0 - 1.0) < -8.0",  False, VBool True,   q8)
  , ("cdf at -8",                  "main = Normal",                       True,  VFloat (-8),  q8)
  , ("cdf of a negated normal",    "main = Normal * (0.0 - 1.0)",         True,  VFloat (-8),  q8)
  , ("two normals",                "main = Normal + 11.313708498984761 < Normal", False, VBool True, q8shifted)
  ]
  where
    q8 = 6.220960574271784e-16
    q5 = 2.866515718791939e-7
    -- Phi(-c / sqrt 2) at the double c, not at 8 * sqrt 2: erfc's own value
    -- at the rounded argument, which agrees with the true tail to ~1e-14.
    q8shifted = 6.220960574271693e-16

normalTailPrecisionTests :: TestTree
normalTailPrecisionTests = testGroup "normal upper-tail precision (cumulative-normal-upper-tail-cancellation)"
  [ testGroup "Interpreter"
      [ testProperty (name_ ++ logLabel ls) $ once $
          case compiledTail ls src of
            Left err -> counterexample err False
            Right (prog, env) ->
              let run = (if cumul then runIntegC else runProbC) prog env [] q
              in case run of
                   Right (VProbDim p _) -> tailClose ls expected p
                   other -> counterexample ("no probability: " ++ show other) False
      | (name_, src, cumul, q, expected) <- normalTailCases, ls <- [False, True] ]
  , testProperty "Python" $ once $ ioProperty $ backendCheck "python" (Just "python3") (const True) pythonScript
  , testProperty "BatchedPython" $ once $ ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> do
          hPutStrLn stderr "normal tail precision: batched case skipped -- no torch-enabled python found (set NEST_TORCH_PYTHON)."
          return (property True)
        -- Linear variants only: the tensor fragment admits no log-space CDF
        -- leaf ('SPLL.CodeGenPyTorchBatched' refuses @IRCumulative _ Log@).
        Just py -> backendCheck "batched" (Just py) not batchedScript
  , testProperty "Julia" $ once $ ioProperty $ do
      mj <- findExecutable "julia"
      case mj of
        Nothing -> do
          hPutStrLn stderr "normal tail precision: Julia case skipped -- no julia on the PATH."
          return (property True)
        Just _ -> backendCheck "julia" Nothing (const True) juliaScript
  ]
  where
    logLabel ls = if ls then " (logSpace)" else ""
    variants = [ (name_ ++ logLabel ls, src, cumul, q, expected, ls)
               | (name_, src, cumul, q, expected) <- normalTailCases, ls <- [False, True] ]
    compiledTail ls src = do
      prog <- either (Left . ("parse: " ++) . show) Right (tryParseProgram "" src)
      env <- either (Left . ("compile: " ++)) Right (compile defaultCompilerConfig{logSpace = ls} prog)
      return (prog, env)
    -- linear: relative error; log space: absolute error of the log, which is
    -- the same measure to first order
    tailClose ls expected got =
      let err = if ls then abs (got - log expected) else abs (got - expected) / expected
      in counterexample ("expected " ++ (if ls then "log " else "") ++ show expected
                         ++ ", got " ++ show got ++ " (error " ++ show err ++ ")")
           (err <= 1e-12)
    -- Every case's emitted module, one per variant; each script prints one
    -- "name_<TAB>value" line per variant, and the Haskell side compares.
    -- @keepLog@ picks variants by their log-space flag.
    backendCheck name mpy keepLog mkScript = do
      cwd <- getCurrentDirectory
      let kept = [ v | v@(_, _, _, _, _, ls) <- variants, keepLog ls ]
      case mapM (\(l, src, c, q, e, ls) -> fmap (\(_, env) -> (l, env, c, q, e, ls)) (compiledTail ls src)) kept of
        Left err -> return (counterexample err False)
        Right compiled -> case mkScript cwd compiled of
          Left err -> return (counterexample (name ++ " codegen: " ++ err) False)
          Right (ext, script) -> do
            (code, out, err) <- withSystemTempFile ("normal_tail." ++ ext) $ \tmpPath tmpHandle -> do
              hPutStr tmpHandle script
              hClose tmpHandle
              case mpy of
                Just py -> readProcessWithExitCode py [tmpPath] ""
                Nothing -> readProcessWithExitCode "julia" (juliaTestFlags ++ [tmpPath]) ""
            let answers = [ (l, v) | ln <- lines out, (l, '\t' : v) <- [break (== '\t') ln] ]
                checks = [ case lookup l answers >>= readTailNum of
                             Just got -> counterexample (name ++ " " ++ l) (tailClose ls e got)
                             Nothing -> counterexample (name ++ " " ++ l ++ ": no answer") False
                         | (l, _, _, _, e, ls) <- compiled ]
            return $ case code of
              ExitSuccess -> conjoin checks
              ExitFailure _ -> counterexample (name ++ " script failed:\n" ++ out ++ err) False
    readTailNum v = case v of
      "-inf" -> Just (-1 / 0)
      "-Inf" -> Just (-1 / 0)
      _ -> readMaybeDouble v
    readMaybeDouble v = case reads (fixExp v) :: [(Double, String)] of
      [(d, "")] -> Just d
      _ -> Nothing
    -- Python's repr writes 1e-05 and Julia 1.0e-5; both are fine for 'reads'
    -- once a mantissa without a point gets one.
    fixExp v = let (m, ex) = break (`elem` "eE") v
                   m' = if '.' `elem` m then m else m ++ ".0"
                   ex' = case ex of
                           (c : '+' : r) -> c : r
                           _ -> ex
               in m' ++ ex'
    pythonScript cwd compiled = Right ("py", unlines $
      [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++
      concat [ [ "_ns = {}"
               , "exec(" ++ show (stubTorchModule (unlines (SPLL.CodeGenPyTorch.generateFunctions True env))) ++ ", _ns)"
               , "print(" ++ show l ++ " + '\\t' + repr(float(_ns['main']." ++ method c ++ "(" ++ pyVal q ++ ")[0])))" ]
             | (l, env, c, q, _, _) <- compiled ])
    batchedScript cwd compiled = do
      blocks <- mapM (\(l, env, c, q, _, _) -> do
                        srcLines <- generateFunctionsBatched True env
                        -- A float sample as float64: 'batchLiteral' leaves it at
                        -- torch's float32 default, and a float32 query is computed
                        -- in float32 (~1e-7 relative), whatever the runtime does.
                        lit <- case q of
                          VFloat f -> Right ("torch.tensor([" ++ show f ++ "], dtype=torch.float64)")
                          _ -> maybe (Left ("no batch literal for " ++ show q)) Right (batchLiteral [q])
                        return [ "_ns = {}"
                               , "exec(" ++ show (unlines srcLines) ++ ", _ns)"
                               , "_r = _ns['main']." ++ method c ++ "(" ++ lit ++ ")[0]"
                               , "print(" ++ show l ++ " + '\\t' + repr(float(_r[0] if torch.is_tensor(_r) and _r.dim() > 0 else _r)))" ])
                     compiled
      return ("py", unlines ([ "import sys, torch", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++ concat blocks))
    juliaScript cwd compiled = Right ("jl", unlines $
      [ "include(" ++ show (cwd ++ "/juliaLib.jl") ++ ")", "using .JuliaSPPLLib" ] ++
      concat [ [ "module Prog" ++ show i, "using ..JuliaSPPLLib" ] ++ SPLL.CodeGenJulia.generateFunctions env ++ [ "end" ]
               ++ [ "println(" ++ show l ++ ", \"\\t\", repr(Float64(Base.invokelatest(Prog" ++ show i ++ "." ++ juliaFn c ++ ", " ++ juliaVal q ++ ")[1])))" ]
             | (i, (l, env, c, q, _, _)) <- zip [0 :: Int ..] compiled ])
    method c = if c then "integrate" else "forward"
    juliaFn c = if c then "main_integ" else "main_prob"
    stubTorchModule = unpack . replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") . pack

-- ===========================================================================
-- A result's dim is an Int on every backend (task presult-dim-as-int)
-- ===========================================================================
--
-- Python and Julia both hold @0 == 0.0@, so every harness that compares a
-- backend's dim by value would pass a float one. These run one emitted module
-- per backend and assert the dim's runtime type: a Python @int@ (a torch
-- @int64@ tensor, batched), a Julia @Int@. The points take each dim through
-- runtime arithmetic: the mixture's lower-dim-wins test, the ANY guard, and
-- the sum of a product's two dims.

resultDimIsIntTests :: TestTree
resultDimIsIntTests = testGroup "result dim is an Int (presult-dim-as-int)"
  [ testProperty "Interpreter" $ once $ conjoin
      [ case compiledDim src of
          Left err -> counterexample err False
          Right (prog, env) -> conjoin
            [ case runProbC prog env [] q of
                Right (VProbDim _ d) -> counterexample (src ++ " at " ++ show q) (d === dim)
                other -> counterexample (src ++ " at " ++ show q ++ ": no (prob, Int dim) result: " ++ show other) False
            | (q, dim) <- pts ]
      | (src, pts) <- dimCases ]
  , testProperty "Python" $ once $ ioProperty $ runDims "python" (Just "python3") "py" pythonScript
  , testProperty "BatchedPython" $ once $ ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> noTorchProperty "result dim is an Int: BatchedPython"
        Just py -> runDims "batched" (Just py) "py" batchedScript
    -- The batched runtime's reassembly of per-bucket and dense results
    -- ('bucketed', 'dense_query', 'gather_dense') used to cast a folded python
    -- int dim to a float tensor, so a sample-list query answered dim 0.0
    -- (prop_Fuzz_BackendsAgree, --quickcheck-replay=312753).
  , testProperty "BatchedPython, bucketed and dense reassembly" $ once $ ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> noTorchProperty "result dim is an Int: BatchedPython reassembly"
        Just py -> do
          cwd <- getCurrentDirectory
          case compiledDim "main = if Uniform < 0.3 then 1 else 0" >>= generateFunctionsBatched True . snd of
            Left err -> return (counterexample err False)
            Right srcLines -> do
              let calls = [ "bucketed(main.forward, [1, 0, 1])", "bucketed(main.forward, [1, 'ANY'])"
                          , "main.forward_at([1, 0], dense=True)", "main.forward_at([1, 5], dense=True)"
                          , "main.forward_at([1, 0], dense=False)" ]
                  script = unlines $
                    [ "import sys, torch", "sys.path.insert(0, " ++ show cwd ++ ")"
                    , "_ns = {}", "exec(" ++ show (unlines srcLines) ++ ", _ns)"
                    , "from pythonLibBatched import bucketed", "_ns['bucketed'] = bucketed" ] ++
                    [ "_r = eval(" ++ show c ++ ", _ns)\nprint(" ++ show c ++ " + '\\t' + str(_r[1][0].dtype) + '\\t' + str(_r[1][1].dtype))" | c <- calls ]
              (code, out, err) <- withSystemTempFile "result_dim_reassembly.py" $ \tmpPath tmpHandle -> do
                hPutStr tmpHandle script
                hClose tmpHandle
                readProcessWithExitCode py [tmpPath] ""
              return $ case code of
                ExitSuccess -> counterexample "(call, dim dtype, flag dtype)"
                                 (lines out === [ c ++ "\ttorch.int64\ttorch.bool" | c <- calls ])
                ExitFailure _ -> counterexample ("reassembly script failed:\n" ++ out ++ err) False
  , testProperty "Julia" $ once $ ioProperty $ runDims "julia" Nothing "jl" juliaScript
  , testProperty "Normalization takes the exact branch on a discrete program, and only there" $ once $ ioProperty $ do
      let branchOf name = do
            prog <- corpusPplPath name >>= parseProgram
            case compile defaultCompilerConfig prog of
              Left e -> return (Left (name ++ ": " ++ show e))
              Right env -> fmap (normalizationBranch . snd) <$> normalizationResults prog env
      discrete <- branchOf "autoNeuralProbMnistAdd"
      continuous <- branchOf "autoNeuralProbGaussian"
      return $ counterexample "a discrete program's normalization check" (discrete === Right ExactSumToOne)
          .&&. counterexample "a continuous program's normalization check" (continuous === Right DensitiesNotDegenerate)
  ]
  where
    dimCases =
      [ ("main = if Uniform < 0.5 then Normal else 1.0", [(VFloat 0.3, 1), (VFloat 1.0, 0)])
      , ("main = (Normal, Normal)", [(VTuple (VFloat 0.1) (VFloat 0.2), 2), (VTuple (VFloat 0.4) (VFloat 0.5), 2)]) ]
    compiledDim src = do
      prog <- either (Left . ("parse: " ++) . show) Right (tryParseProgram "" src)
      env <- either (Left . ("compile: " ++)) Right (compile defaultCompilerConfig prog)
      return (prog, env)
    -- Every script prints one line per point: the dim's runtime type, a tab, its value.
    runDims name mpy ext mkScript = do
      cwd <- getCurrentDirectory
      case mapM (\(src, pts) -> fmap (\(_, env) -> (env, pts)) (compiledDim src)) dimCases of
        Left err -> return (counterexample err False)
        Right compiled -> case mkScript cwd compiled of
          Left err -> return (counterexample (name ++ " codegen: " ++ err) False)
          Right script -> do
            (code, out, err) <- withSystemTempFile ("result_dim." ++ ext) $ \tmpPath tmpHandle -> do
              hPutStr tmpHandle script
              hClose tmpHandle
              case mpy of
                Just py -> readProcessWithExitCode py [tmpPath] ""
                Nothing -> readProcessWithExitCode "julia" (juliaTestFlags ++ [tmpPath]) ""
            let want = [ intType name ++ "\t" ++ show d | (_, pts) <- compiled, (_, d) <- pts ]
            return $ case code of
              ExitSuccess -> counterexample (name ++ ": (type, dim) per point") (lines out === want)
              ExitFailure _ -> counterexample (name ++ " script failed:\n" ++ out ++ err) False
    intType name = case name of
      "julia" -> "Int64"
      "batched" -> "torch.int64"
      _ -> "int"
    pythonScript cwd compiled = Right $ unlines $
      [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++
      concat [ [ "_ns = {}"
               , "exec(" ++ show (stubTorch (unlines (SPLL.CodeGenPyTorch.generateFunctions True env))) ++ ", _ns)" ] ++
               [ "_d = eval(" ++ show ("main.forward(" ++ pyVal q ++ ")") ++ ", _ns)[1][0]\nprint(type(_d).__name__ + '\\t' + repr(_d))" | (q, _) <- pts ]
             | (env, pts) <- compiled ]
    -- One batch per program, every point in it. A dim folded to a constant
    -- comes back as a plain int and is broadcast here, as the batched
    -- harness's '_leaf' does.
    batchedScript cwd compiled = do
      blocks <- mapM (\(env, pts) -> do
                        srcLines <- generateFunctionsBatched True env
                        lit <- maybe (Left "no batch literal") Right (batchLiteral (map fst pts))
                        return [ "_ns = {}"
                               , "exec(" ++ show (unlines srcLines) ++ ", _ns)"
                               , "_d = eval(" ++ show ("main.forward(" ++ lit ++ ")") ++ ", _ns)[1][0]"
                               , "_d = _d if torch.is_tensor(_d) else torch.tensor([_d] * " ++ show (length pts) ++ ")"
                               , "_d = _d.expand(" ++ show (length pts) ++ ") if _d.dim() == 0 else _d"
                               , "for _x in _d.tolist():"
                               , "    print(str(_d.dtype) + '\\t' + repr(_x))" ])
                     compiled
      return (unlines ([ "import sys, torch", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++ concat blocks))
    juliaScript cwd compiled = Right $ unlines $
      [ "include(" ++ show (cwd ++ "/juliaLib.jl") ++ ")", "using .JuliaSPPLLib" ] ++
      concat [ [ "module Prog" ++ show i, "using ..JuliaSPPLLib" ] ++ SPLL.CodeGenJulia.generateFunctions env ++ [ "end" ] ++
               [ "_d = Base.invokelatest(Prog" ++ show i ++ ".main_prob, " ++ juliaVal q ++ ")[2][1]; println(string(typeof(_d)), \"\\t\", repr(_d))" | (q, _) <- pts ]
             | (i, (env, pts)) <- zip [0 :: Int ..] compiled ]
    stubTorch = unpack . replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") . pack

-- ===========================================================================
-- Enumeration bucketing (task batched-bucketing-splits-on-nullary-constructors)
-- ===========================================================================
--
-- An ADT whose constructors are all nullary is an enumeration: its tag is a
-- value, not a structure, so the bucketing wrapper keys the whole ADT as one
-- signature and packs a bucket's tags into a [B] tensor. The acceptance
-- criterion (design heterogeneous-batch-inference, 2026-09-18 review note):
-- CLEVR-shaped scenes -- every attribute an enumeration, positions Gaussian --
-- bucket by object count alone, not by attribute-value combination.
--
-- This drives @clevrSceneEnumAttrs@ directly rather than through the corpus
-- batched differential, which does not route ADT-valued samples at all. Every
-- bucketed answer is checked twice: against the same kernel called on each
-- sample alone (so collapsing cannot change a number) and against the scene's
-- closed-form density (so the per-sample path is not wrong in the same way).

batchedEnumBucketingTests :: TestTree
batchedEnumBucketingTests = testGroup "batched enum bucketing"
  [ testProperty "CLEVR-shaped scenes bucket by object count, with unchanged values" $
      once $ ioProperty $ do
        mpy <- findTorchPython
        case mpy of
          Nothing -> noTorchProperty "batched enum bucketing"
          Just py -> do
            prog <- corpusPplPath "clevrSceneEnumAttrs" >>= parseProgram
            case compile defaultCompilerConfig{batched = True} prog >>= generateFunctionsBatched True of
              Left err -> return (counterexample ("clevrSceneEnumAttrs is not batched-eligible: " ++ err) False)
              Right srcLines -> do
                cwd <- getCurrentDirectory
                let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n"
                             ++ unlines srcLines ++ enumBucketingDriver
                (code, out, err) <- withSystemTempFile "enum_bucketing.py" $ \tmpPath tmpHandle -> do
                  hPutStr tmpHandle script
                  hClose tmpHandle
                  readProcessWithExitCode py [tmpPath] ""
                return $ case code of
                  ExitSuccess   -> counterexample (out ++ err) True
                  ExitFailure _ -> counterexample ("enum bucketing check failed:\n" ++ out ++ err) False
  ]

-- | A recursive deterministic helper's forward evaluator, run on a
-- per-element argument (task batched-prob-path-calls-recursive-helper-gen).
-- The corpus differential passes a program's parameters batch-shared, so
-- @factorial@'s rows never mix its guard @x < 1.5@ across a batch, and
-- modality inference refuses the same helper on a drawn value, which is
-- what would put a per-element value in its argument. This passes @x@ as a
-- @[B]@ tensor of different depths instead: the evaluator's guard mixes, so
-- the batch is split until each half agrees, and every element must still
-- get its own factorial. A @slow@ program, so no tier checks it otherwise.
batchedPerElementEvaluatorTests :: TestTree
batchedPerElementEvaluatorTests = testGroup "batched forward evaluator on a per-element argument"
  [ testProperty "factorial's prob path evaluates factorial per element" $
      once $ ioProperty $ do
        mpy <- findTorchPython
        case mpy of
          Nothing -> noTorchProperty "batched forward evaluator"
          Just py -> do
            prog <- corpusPplPath "factorial" >>= parseProgram
            case compile defaultCompilerConfig{batched = True} prog >>= generateFunctionsBatched True of
              Left err -> return (counterexample ("factorial is not batched-eligible: " ++ err) False)
              Right srcLines -> do
                cwd <- getCurrentDirectory
                let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n"
                             ++ unlines srcLines ++ driver
                (code, out, err) <- withSystemTempFile "per_element_evaluator.py" $ \tmpPath tmpHandle -> do
                  hPutStr tmpHandle script
                  hClose tmpHandle
                  readProcessWithExitCode py [tmpPath] ""
                return $ case code of
                  ExitSuccess   -> counterexample (out ++ err) True
                  ExitFailure _ -> counterexample ("per-element evaluator check failed:\n" ++ out ++ err) False
  ]
  where
    driver = unlines
      [ "def fact(n):"
      , "    return 1.0 if n < 1.5 else fact(n - 1.0) * n"
      , "xs = [5.0, 1.0, 3.0, 4.0, 0.5, 6.0, 2.0, 5.0]"
      , "hits = [fact(x) for x in xs]"
      , "misses = [fact(x) + 1.0 for x in xs]"
      , "x = torch.tensor(xs, dtype=torch.float64)"
      , "fails = []"
      , "for name, samples, want in [('hit', hits, 1.0), ('miss', misses, 0.0)]:"
      , "    p = main.forward(torch.tensor(samples, dtype=torch.float64), x)[0]"
      , "    for i, v in enumerate(p.tolist()):"
      , "        if abs(v - want) > 1e-9:"
      , "            fails.append('%s at x = %r: p = %r, expected %r' % (name, xs[i], v, want))"
      , "c = main.integrate(torch.tensor([h - 0.5 for h in hits] + [h + 0.5 for h in hits], dtype=torch.float64),"
      , "                   torch.cat([x, x]))[0]"
      , "for i, v in enumerate(c.tolist()):"
      , "    want = 0.0 if i < len(xs) else 1.0"
      , "    if abs(v - want) > 1e-9:"
      , "        fails.append('cdf row %d: %r, expected %r' % (i, v, want))"
      , "if fails:"
      , "    print('\\n'.join(fails))"
      , "    sys.exit(1)"
      , "print('per-element evaluator OK')"
      ]

-- | Appended to the emitted module (so the constructor classes are in scope).
-- The probabilities mirror @clevrSceneEnumAttrs.ppl@.
enumBucketingDriver :: String
enumBucketingDriver = unlines
  [ "import random, math"
  , "from pythonLibBatched import _pack"
  , "random.seed(7)"
  , "PS = {Cube: .4, Sphere: .3, Cylinder: .3}"
  , "PZ = {Small: .3, Large: .7}"
  , "CN = [Gray, Red, Blue, Green, Brown, Purple, Cyan, Yellow]"
  , "PC = {c: (0.5 ** (k + 1) if k < 7 else 0.5 ** 7) for k, c in enumerate(CN)}"
  , "PM = {Rubber: .6, Metal: .4}"
  , "def mk_obj():"
  , "    return T(random.choice(list(PS))(), T(random.choice(list(PZ))(), T(random.choice(CN)(),"
  , "             T(random.choice(list(PM))(), random.gauss(0.0, 1.0)))))"
  , "def ref(scene):"
  , "    e = 0.25"
  , "    for o in scene:"
  , "        x = o.t2.t2.t2.t2"
  , "        e *= 0.75 * PS[type(o.t1)] * PZ[type(o.t2.t1)] * PC[type(o.t2.t2.t1)] * PM[type(o.t2.t2.t2.t1)] \\"
  , "             * math.exp(-x * x / 2) / math.sqrt(2 * math.pi)"
  , "    return e"
  , "def leaf(x):"
  , "    return float(x.reshape(-1)[0]) if torch.is_tensor(x) else float(x)"
  , "fails = []"
  , "# Same object count, every attribute varying: one bucket."
  , "same = [toList([mk_obj() for _ in range(3)]) for _ in range(64)]"
  , "if bucket_count(same) != 1:"
  , "    fails.append('64 three-object scenes gave %d buckets, expected 1' % bucket_count(same))"
  , "# Object counts 0..10: bounded by the number of distinct counts."
  , "scenes = [toList([mk_obj() for _ in range(random.randint(0, 10))]) for _ in range(300)]"
  , "want = len(set(len(sc) for sc in scenes))"
  , "if bucket_count(scenes) != want:"
  , "    fails.append('%d scenes gave %d buckets, expected %d (one per object count)' % (len(scenes), bucket_count(scenes), want))"
  , "r = bucketed(main.forward, scenes)"
  , "for i, sc in enumerate(scenes):"
  , "    got = float(r[0][i])"
  , "    alone = leaf(main.forward(_pack([sc]))[0])"
  , "    e = ref(sc)"
  , "    if abs(got - alone) > 1e-9 * max(1.0, abs(alone)):"
  , "        fails.append('scene %d: bucketed %r != per-sample %r' % (i, got, alone))"
  , "    if abs(got - e) > 1e-5 * e:"
  , "        fails.append('scene %d: bucketed %r != closed form %r' % (i, got, e))"
  , "    if float(r[1][0][i]) != float(len(sc)):"
  , "        fails.append('scene %d: dim %r != %d' % (i, float(r[1][0][i]), len(sc)))"
  , "if fails:"
  , "    print('\\n'.join(fails[:20]))"
  , "    sys.exit(1)"
  , "print('enum bucketing OK: %d scenes in %d buckets' % (len(scenes), want))"
  ]

-- | One table row: the program must compile, and only then be refused by the
-- batched backend with a diagnostic containing @needle@.
refusalRow :: String -> String -> Property
refusalRow prog needle = ioProperty $ do
  p <- corpusPplPath prog >>= parseProgram
  return $ case compile defaultCompilerConfig{batched = True} p of
    Left err -> counterexample (prog ++ " failed to compile at all, so this row proves "
                                ++ "nothing about the batched refusal: " ++ err) False
    Right env -> case generateFunctionsBatched True env of
      Right _  -> counterexample ("batched mode accepted " ++ prog
                                  ++ "; expected a refusal mentioning: " ++ needle) False
      Left msg -> counterexample ("batched refusal for " ++ prog ++ " does not mention "
                                  ++ show needle ++ "; actual diagnostic: " ++ msg)
                    (needle `isInfixOf` msg)
             .&&. advisoryRow prog (Just msg) p

-- | The scalar-mode advisory ('SPLL.Prelude.batchedRefusal', CLI @-v@, task
-- @batched-scalar-mode-eligibility-warning@) must answer with exactly the
-- refusal batched mode would have given — that is its whole contract: a user
-- who has not flipped @--batched@ is told what flipping it would say. Called
-- from a /scalar/ config, since that is the situation it exists for.
advisoryRow :: String -> Maybe String -> Program -> Property
advisoryRow prog expected p =
  counterexample ("scalar-mode advisory for " ++ prog ++ " disagrees with the batched "
                  ++ "backend.\n  advisory: " ++ describe (batchedRefusal defaultCompilerConfig p)
                  ++ "\n  backend:  " ++ describe expected)
    (batchedRefusal defaultCompilerConfig p == expected)
  where
    describe = maybe "eligible" ("refused: " ++)

-- | A batchable group: all query points sharing the same query kind (prob vs
-- cumulative), rendered into one batched call. 'bgParamExprs' is the Python
-- expression for each positional argument after the sample: a broadcast scalar
-- for a shared non-neural parameter, or a @[B, n]@ tensor for a batched neural
-- symbol (whose per-point value differs across the batch — that variation is
-- the whole point of neural batching).
data BatchGroup = BatchGroup
  { bgIsCumul    :: Bool
  , bgParamExprs :: [String]
  -- | The raw positional arguments of each point, in sample order — what the
  -- Python-side 'bgParamExprs' were built from. Kept so the topK differential
  -- can re-run the same points through the interpreter for ground truth.
  , bgParamRows  :: [[IRValue]]
  , bgSamples    :: [IRValue]
  , bgExpProb    :: [Double]
  , bgExpDim     :: [Int]
  -- | How the samples go to the kernel ('batchSamples').
  , bgBatch      :: SampleBatch
  } deriving (Show)

-- | Split a program's prob/cumulative test cases into batchable groups, or
-- 'Nothing' if any sample is not structure-of-arrays batchable (a non
-- float/int/bool/tuple leaf). For a neural program ('isNeural'), all points of
-- a query kind form one group and each per-point symbol argument is batched
-- into a @[B, n]@ tensor; for a non-neural program, points are grouped by
-- identical parameter list and the shared parameters broadcast as scalars.
batchGroups :: EnumCtors -> Bool -> [TestCase] -> Maybe [BatchGroup]
batchGroups enumOf isNeural tcs = mapM build grouped
  where
    -- Marginal (ANY) query points are included as of design
    -- heterogeneous-batch-inference Component 3/M4: ANY-ness is a structural
    -- marker like a list length or Either tag ('containsStructureV'/'shapeSig'
    -- below), so such a point routes through the bucketing wrapper into its own
    -- bucket rather than being dropped. 'VAnyExcept' (a narrower
    -- marginal-exclusion sentinel, not just an ANY-flavoured structural marker)
    -- is the one still-unsupported case and is dropped, the same treatment
    -- 'containsAnyExceptV' below gives it -- one such point no longer keeps
    -- every *other* point of that program out of the differential either.
    keyed = [ q | t <- tcs, Just q@(_, _, sm, _, _) <- [asQuery t], not (containsAnyExceptV sm) ]
    grouped
      | isNeural  = groupBy ((==) `on` (\(c, _, _, _, _) -> c)) keyed
      | otherwise = groupBy ((==) `on` (\(c, ps, _, _, _) -> (c, show ps))) keyed
    build g@((c, _, _, _, _):_) =
      let samples = [s | (_, _, s, _, _) <- g]
          paramRows = [ps | (_, ps, _, _, _) <- g]
      in do sb <- batchSamples enumOf samples
            paramExprs <- if isNeural
              then batchSymParamCols paramRows
              else Just (map pyVal (head paramRows))
            Just BatchGroup { bgIsCumul = c, bgParamExprs = paramExprs
                            , bgParamRows = paramRows, bgSamples = samples
                            , bgExpProb = [ep | (_, _, _, ep, _) <- g]
                            , bgExpDim  = [ed | (_, _, _, _, ed) <- g]
                            , bgBatch   = sb }
    build [] = Nothing
    -- 'Impossible' rows (no stated dim) fall through to the final wildcard and
    -- are simply not batched, the same treatment 'containsAnyExceptV' above
    -- gives a 'VAnyExcept'-carrying query point.
    asQuery (ProbTestCase _ s ps (Possible (VFloat ep) ed _))  = Just (False, ps, s, ep, ed)
    asQuery (CumulTestCase _ s ps (Possible (VFloat ep) ed _)) = Just (True,  ps, s, ep, ed)
    asQuery _ = Nothing

-- | Batch the positional symbol arguments of a neural program across points.
-- Each row is one point's argument list; every argument is a mode-2 verbatim
-- symbol envelope @(2, [logit0, ...])@ (what the neural .tst files pass), or a
-- rank-1 tensor input (a shaped network's, after 'shapeNeuralParams'). We
-- transpose to columns (one per argument position) and stack each column's
-- logit vectors into a @[B, n]@ tensor literal — fed to the identity mock the
-- driver installs for every declared network. 'Nothing' if the rows are ragged
-- or any argument is not a mode-2 envelope.
batchSymParamCols :: [[IRValue]] -> Maybe [String]
batchSymParamCols rows
  | null rows                          = Just []
  | any ((/= length (head rows)) . length) rows = Nothing
  | otherwise = mapM batchSymColumn (transpose rows)

--
-- The column is float64, the interpreter's precision. In float32 a path mass
-- that equals a topK cutoff in exact arithmetic rounds onto the cutoff
-- (@0.2 + 0.8 * 0.5@ is @0.6f@, and @0.6f > 0.6@ is false once the cutoff is
-- cast to float32), while in Double it lands just above it; the batched topK
-- differential then pruned a path the interpreter kept (task
-- batched-topk-per-element-failures-on-redeclared-programs, class E).
batchSymColumn :: [IRValue] -> Maybe String
batchSymColumn vs = do
  logitRows <- mapM logitsOf vs
  return ("torch.tensor([" ++ intercalate ", " (map renderRow logitRows) ++ "], dtype=torch.float64)")
  where
    logitsOf (VTuple (VInt 2) (VList ls)) = Just (toList ls)
    -- a shaped tensor input ('shapeNeuralParams'): one row of the [B, numel]
    -- column, fed to that network's batched projection mock ('batchedMockExpr')
    logitsOf (VTensor [_] xs)             = Just xs
    logitsOf _                            = Nothing
    renderRow ls = "[" ++ intercalate ", " (map num ls) ++ "]"
    num (VFloat f) = show f
    num (VInt i)   = show (fromIntegral i :: Double)
    num _          = "0.0"

isTup :: IRValue -> Bool
isTup (VTuple _ _) = True
isTup _ = False

isBoolV :: IRValue -> Bool
isBoolV (VBool _) = True
isBoolV _ = False

isNum :: IRValue -> Bool
isNum (VFloat _) = True
isNum (VInt _) = True
isNum _ = False

-- | How a group's query points are handed to the batched kernel.
data SampleBatch
  -- | One structure-of-arrays tensor: the whole batch has one fixed shape, so
  -- the kernel takes it directly (the original tensor fragment).
  = SoA String
  -- | A plain Python list of per-point samples, to be routed through the host
  -- bucketing wrapper (design heterogeneous-batch-inference, Component 1): the
  -- points differ in structure (list lengths), so @bucketed@ partitions them by
  -- structural signature, SoA-packs each bucket, runs the kernel once per
  -- bucket and scatters the results back into input order. The 'Int' is the
  -- number of distinct signatures the wrapper must find -- the M1 acceptance
  -- criterion ("bucket count = distinct shapes"), asserted in the driver.
  | Bucketed String Int
  deriving (Show)

-- | The Python form of a group's samples, or 'Nothing' if they are not
-- batchable at all (a @VAnyExcept@ sample, or a leaf that is neither numeric,
-- bool, nor a structure of those).
batchSamples :: EnumCtors -> [IRValue] -> Maybe SampleBatch
batchSamples enumOf vs
  | any containsAnyExceptV vs  = Nothing
  | any containsStructureV vs =
      Just (Bucketed ("[" ++ intercalate ", " (map pyVal vs) ++ "]")
                     (length (nub (map (shapeSig enumOf) vs))))
  | otherwise            = SoA <$> batchLiteral vs

-- | Does this sample carry structure a batch can differ in — a list length, an
-- Either tag, or (design heterogeneous-batch-inference, Component 3/M4) a bare
-- ANY wildcard, which is a structural marker of exactly the same kind. A list
-- (any list, including @AnyList@) or an Either is always structure regardless
-- of its leaves, so a nested wildcard inside one needs no separate case here.
-- Such a group goes through the bucketing wrapper.
containsStructureV :: IRValue -> Bool
containsStructureV (VList _)    = True
containsStructureV (VEither _)  = True
containsStructureV (VTuple a b) = containsStructureV a || containsStructureV b
containsStructureV VAny         = True
-- Unit carries no per-element data: structure, spelled @None@ by 'pyVal' and
-- keyed @'U'@ by @pythonLibBatched.signature@ (task batched-refuses-unit-constant).
containsStructureV VUnit        = True
-- An ADT value has no structure-of-arrays literal ('batchLiteral'), but the
-- bucketing wrapper takes it as-is: @signature@ keys an enumeration as one
-- bucket and any other ADT by constructor tag and field shape. Routing it
-- there is what lets an ADT-valued program (e.g. a `Color` result) join the
-- differential at all -- before, its whole group was refused as unbatchable.
containsStructureV (VADT _ _)   = True
containsStructureV _            = False

-- | 'VAnyExcept' (a wildcard excluding specific values) is the one ANY-like
-- sentinel this milestone (M4) does not give a batched representation to (see
-- 'SPLL.CodeGenPyTorchBatched.batchedVal') — its exclusion set matters to
-- enumeration semantics elsewhere, so it is not just a structural marker like
-- plain ANY, and a query point carrying it is dropped from the differential.
containsAnyExceptV :: IRValue -> Bool
containsAnyExceptV (VAnyExcept _) = True
containsAnyExceptV (VList l)      = any containsAnyExceptV (toList l)
containsAnyExceptV (VEither e)    = either containsAnyExceptV containsAnyExceptV e
containsAnyExceptV (VTuple a b)   = containsAnyExceptV a || containsAnyExceptV b
containsAnyExceptV _              = False

-- | Which constructors the emitted batched program collapsed into an
-- enumeration, mapped to their ADT's name: the ADTs whose classes carry an
-- @_enum@ attribute ('SPLL.CodeGenPyTorchBatched.generateADTClassesBatched').
-- Read off the emitted source rather than recomputed from the declarations,
-- because the backend un-collapses an all-nullary ADT whose test a refusal
-- blames, so "all-nullary" alone does not decide it.
type EnumCtors = String -> Maybe String

-- | 'EnumCtors' of a program's declarations and its emitted batched source.
collapsedEnumCtors :: [ADTDecl] -> String -> EnumCtors
collapsedEnumCtors decls src cn = lookup cn table
  where
    collapsed = [ n | l <- lines src, Just q <- [stripPrefix "_enum = " (dropWhile (== ' ') l)]
                    , [(n, "")] <- [reads q :: [(String, String)]] ]
    table = [ (c, dataName d) | d <- decls, dataName d `elem` collapsed, (c, _) <- constructors d ]

-- | No collapsed enumeration: for a caller that ignores the bucket count.
noEnumCtors :: EnumCtors
noEnumCtors = const Nothing

-- | The Haskell twin of @pythonLibBatched.signature@: the sample's structural
-- skeleton with every scalar leaf erased, ANY-ness (M4) checked first exactly
-- as @signature@ checks @isAny@ first (a bare 'VAny' or an @AnyList@ nested
-- under a concrete constructor is its own bucket, not conflated with the
-- concrete case at that position). Used only to predict the bucket count.
shapeSig :: EnumCtors -> IRValue -> String
shapeSig _ VAny                 = "ANY"
shapeSig _ VUnit                = "U"
shapeSig _ (VList AnyList)      = "ANY"
shapeSig e (VList l)            = "L(" ++ intercalate "," (map (shapeSig e) (toList l)) ++ ")"
shapeSig e (VTuple a b)         = "T(" ++ shapeSig e a ++ "," ++ shapeSig e b ++ ")"
shapeSig e (VEither (Left v))   = "L?(" ++ shapeSig e v ++ ")"
shapeSig e (VEither (Right v))  = "R?(" ++ shapeSig e v ++ ")"
-- A collapsed enumeration is one bucket for the whole ADT (task
-- batched-bucketing-splits-on-nullary-constructors). Any other ADT value is
-- keyed by its constructor tag and its fields' shapes, as @signature@ keys it:
-- two constructors are two structures (task
-- batched-topk-per-element-failures-on-redeclared-programs).
shapeSig e (VADT cn fs)         = case e cn of
  Just adt -> "E(" ++ adt ++ ")"
  Nothing  -> "A(" ++ cn ++ concatMap ((',' :) . shapeSig e) fs ++ ")"
shapeSig _ _                    = "x"

-- | Build a structure-of-arrays batch tensor literal from a homogeneous list of
-- sample values: numeric leaves stack into a float tensor, bools into a bool
-- tensor, and tuples recurse per component (so the batch dimension lives at the
-- leaves). 'Nothing' if a leaf is neither.
batchLiteral :: [IRValue] -> Maybe String
batchLiteral vs
  | all isTup vs, not (null vs) =
      do l <- batchLiteral [a | VTuple a _ <- vs]
         r <- batchLiteral [b | VTuple _ b <- vs]
         return ("T(" ++ l ++ ", " ++ r ++ ")")
  | all isBoolV vs =
      Just ("torch.tensor([" ++ intercalate ", " (map (\v -> case v of VBool b -> if b then "True" else "False"; _ -> "False") vs) ++ "], dtype=torch.bool)")
  | all isNum vs =
      Just ("torch.tensor([" ++ intercalate ", " (map numLit vs) ++ "])")
  | otherwise = Nothing
  where
    numLit (VFloat f) = pyDouble f
    numLit (VInt i)   = pyDouble (fromIntegral i)
    numLit _          = "0.0"

-- | Locate a Python interpreter that can import torch: @NEST_TORCH_PYTHON@, then
-- a conventional venv path under @HOME@, then @python3@. Returns the first whose
-- @import torch@ succeeds.
findTorchPython :: IO (Maybe FilePath)
findTorchPython = do
  envPy <- lookupEnv "NEST_TORCH_PYTHON"
  home  <- lookupEnv "HOME"
  let candidates = maybe [] (:[]) envPy
                ++ maybe [] (\h -> [h ++ "/.local/share/nest/torchvenv/bin/python"]) home
                ++ ["python3"]
  firstWithTorch candidates
  where
    firstWithTorch [] = return Nothing
    firstWithTorch (c:cs) = do
      ok <- hasTorch c
      if ok then return (Just c) else firstWithTorch cs
    hasTorch c = do
      res <- try (readProcessWithExitCode c ["-c", "import torch"] "") :: IO (Either SomeException (ExitCode, String, String))
      return $ case res of
        Right (ExitSuccess, _, _) -> True
        _ -> False

-- | What a torch-dependent check does when 'findTorchPython' found nothing:
-- @Nothing@ means skip (only when @NEST_SKIP_TORCH=1@ asks for it, noted on
-- stderr), @Just msg@ is the failure to report. A missing torch used to be a
-- silent pass, and a garbage-collected venv then hid a real BatchedPython
-- failure behind "green" for days; skipping torch is now an explicit choice.
noTorch :: String -> IO (Maybe String)
noTorch what = do
  skip  <- lookupEnv "NEST_SKIP_TORCH"
  envPy <- lookupEnv "NEST_TORCH_PYTHON"
  if skip == Just "1"
    then do
      hPutStrLn stderr (what ++ ": skipped -- NEST_SKIP_TORCH=1.")
      return Nothing
    else return $ Just $ what ++ ": no torch-enabled python found. "
      ++ maybe "NEST_TORCH_PYTHON is unset; set it to a python that can import torch"
               (\p -> "NEST_TORCH_PYTHON=" ++ p ++ " cannot import torch (a nix GC may have removed its base python)")
               envPy
      ++ ", or set NEST_SKIP_TORCH=1 to skip torch-dependent checks deliberately."

-- | 'noTorch' as a property.
noTorchProperty :: String -> IO Property
noTorchProperty what = maybe (property True) (`counterexample` False) <$> noTorch what

-- | Run every eligible program's batched code in one shared torch process and
-- assert every batched query point matches its expected value.
runBatchedPython :: FilePath -> [(String, String, [BatchGroup], [NetMock])] -> Property
runBatchedPython _ [] = counterexample "BatchedPython: no eligible corpus programs found" False
runBatchedPython py eligible = ioProperty $ do
  hPutStrLn stderr ("BatchedPython: " ++ show (length eligible) ++ " eligible corpus programs, "
                    ++ show (sum [sum (map (length . bgSamples) gs) | (_, _, gs, _) <- eligible])
                    ++ " query points, via " ++ py)
  -- Run the script from a temp file rather than `python -c`: deep neural logit
  -- vectors make the embedded literals exceed the OS argument-length limit. A
  -- temp file puts its own directory (not cwd) on sys.path, so prepend the
  -- project root explicitly so `pythonLibBatched` resolves.
  cwd <- getCurrentDirectory
  let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ batchedDriver False eligible
  (code, out, err) <- withSystemTempFile "batched_diff.py" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle script
    hClose tmpHandle
    readProcessWithExitCode py [tmpPath] ""
  return $ case code of
    ExitSuccess -> counterexample (out ++ err) True
    ExitFailure _ -> counterexample ("Batched PyTorch differential failed:\n" ++ out ++ err) False

-- | The single Python script: define each eligible program in its own namespace
-- (torch imported once), run every batched group, and exit non-zero listing any
-- element whose prob (or dim, where prob is non-zero) disagrees with the corpus
-- expectation beyond 'probTolerance'.
batchedDriver :: Bool -> [(String, String, [BatchGroup], [NetMock])] -> String
batchedDriver accArg eligible = unlines $
  [ "import torch, sys, traceback"
  -- T for structure-of-arrays tuple sample batches; the list constructors and
  -- the bucketing wrapper for heterogeneous (list-shaped) samples.
  , "from pythonLibBatched import T, ConsInferenceList, EmptyInferenceList, AnyInferenceList, Left, Right, bucketed, bucket_count"
  , "TOL = " ++ show probTolerance
  , "failures = []"
  , "def _bucket_count(name, samples, expected):"
  , "    got = bucket_count(samples)"
  , "    if got != expected:"
  , "        failures.append(name + ': bucketing produced ' + str(got) + ' buckets, expected ' + str(expected))"
  , "def _leaf(x, i):"
  , "    return float(x[i]) if (torch.is_tensor(x) and x.dim() > 0) else float(x)"
  , "def _cmp(name, method, r, exp_p, exp_d):"
  , "    p = r[0]; d = r[1][0]"
  , "    for i in range(len(exp_p)):"
  , "        pv = _leaf(p, i)"
  , "        if abs(pv - exp_p[i]) > TOL:"
  , "            failures.append(name + '.' + method + ' pt ' + str(i) + ': prob ' + str(pv) + ' != ' + str(exp_p[i]))"
  , "        if pv != 0.0:"
  , "            dv = _leaf(d, i)"
  , "            if abs(dv - exp_d[i]) > TOL:"
  , "                failures.append(name + '.' + method + ' pt ' + str(i) + ': dim ' + str(dv) + ' != ' + str(exp_d[i]))"
  ] ++
  concatMap programBlock eligible ++
  [ "if failures:"
  , "    print('BATCHED DIFFERENTIAL FAILURES (' + str(len(failures)) + '):')"
  , "    for f in failures: print('  ' + f)"
  , "    sys.exit(1)"
  , "print('BatchedPython OK: " ++ show (length eligible) ++ " programs')"
  ]
  where
    programBlock (name, src, groups, netNames) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      -- Install an identity mock for every declared network: the .tst symbols
      -- are mode-2 verbatim-logit envelopes, batched into a [B, n] logit
      -- tensor, so net(sym) = sym returns those logits directly.
      ] ++
      [ "    _ns[" ++ show (netMockName nm) ++ "] = " ++ batchedMockExpr nm | nm <- netNames ] ++
      [ "    _main = _ns['main']" ] ++
      concatMap (groupCall name) groups ++
      [ "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    groupCall name (BatchGroup isCumul paramExprs _ _ expP expD sb) =
      let method = if isCumul then "integrate" else "forward"
          -- A topK-compiled prob function takes an accumulated-probability
          -- parameter right after the sample, then the runtime cutoff (see
          -- 'SPLL.Prelude.topKCutoff'); an integrate function takes only the
          -- cutoff. Seed the accumulator with 1.0 at the query root and pass
          -- the compiled-in default cutoff, exactly as the interpreter driver does.
          accStr
            | not accArg = ""
            | isCumul    = ", _ns['TOP_K_CUTOFF']"
            | otherwise  = ", 1.0, _ns['TOP_K_CUTOFF']"
          paramStr = concatMap (", " ++) paramExprs
          (bucketCheck, call) = case sb of
            SoA xs ->
              ([], "_main." ++ method ++ "(" ++ xs ++ accStr ++ paramStr ++ ")")
            -- Heterogeneous samples go through the host bucketing wrapper, and
            -- the bucket count is asserted: the M1 acceptance criterion is that
            -- the wrapper makes exactly one kernel call per distinct shape, not
            -- merely that the numbers come out right.
            --
            -- The literal is evaluated inside the program's own namespace: a
            -- sample may name the program's ADT constructors (@Cube()@), which
            -- exist only there.
            Bucketed xs n ->
              ( [ "    _samples = eval(" ++ show xs ++ ", _ns)"
                , "    _bucket_count(" ++ show name ++ ", _samples, " ++ show n ++ ")" ]
              , "bucketed(_main." ++ method ++ ", _samples" ++ accStr ++ paramStr ++ ")" )
      in bucketCheck
         ++ [ "    _cmp(" ++ show name ++ ", " ++ show method ++ ", " ++ call
              ++ ", " ++ pyFloatList expP ++ ", " ++ pyFloatList expD ++ ")" ]
    pyFloatList xs = "[" ++ intercalate ", " (map show xs) ++ "]"

-- ===========================================================================
-- M3: dense enumeration mode (design heterogeneous-batch-inference)
-- ===========================================================================

-- | The inference methods the emitted @Main@ class exposes a dense entry point
-- for. Read off the emitted source rather than recomputed from the IR: the
-- capability under test is precisely "the generated class has these methods",
-- and re-deriving the eligibility rule here would let the test agree with a
-- broken compiler.
--
-- Scoped to the @Main@ class block, because a helper group can perfectly well
-- have a finite domain while @main@ does not (@coin@'s own @Coin@ class does;
-- @Main@ there does too, but @gaussList@ is the shape where they differ).
denseEntryPoints :: String -> [String]
denseEntryPoints src =
  [ m | m <- ["forward", "integrate"], ("def " ++ m ++ "_dense(") `isInfixOf` block ]
  where
    block = unlines $ takeWhile indented $ drop 1
          $ dropWhile (/= "class Main(Module):") (lines src)
    indented l = null l || " " `isPrefixOf` l

-- | The point of the @dense@ routing token: a program that declares it must
-- actually receive dense entry points.
declaredDenseProp :: Int -> [String] -> Property
declaredDenseProp 0 _ = counterexample
  "no .tst file declares `dense` in its backends header; dense enumeration has no coverage" False
declaredDenseProp _ refused = counterexample
  ("programs declaring `dense` in their .tst backends header no longer get dense entry points\n\
   \  (a finite query domain, and a prob/integ signature of just the sample):\n"
   ++ unlines [ "  " ++ n | n <- refused ])
  (null refused)

-- | A visible note (never a failure) for batched programs that /could/ enumerate
-- densely but whose @.tst@ file does not say so. Same asymmetry as
-- 'gainNoteProp': losing the capability is the regression, gaining it is not.
denseGainNoteProp :: [String] -> Property
denseGainNoteProp gained = ioProperty $ do
  if null gained
    then return ()
    else hPutStrLn stderr ("BatchedPython: " ++ show (length gained) ++ " batched program(s) have a finite\n\
      \  query domain but do not declare `dense` in their .tst backends header:\n"
      ++ unlines [ "    " ++ n | n <- gained ])
  return True

-- | Both sides of the dense decision boundary, named explicitly, so that a
-- change which quietly widened or narrowed it fails here rather than only
-- shifting a count. The gain/loss notes above measure the boundary's *position*;
-- these rows pin the *reasons* it sits there.
--
-- Torch-free: it reads the emitted source, like the eligibility assertions.
denseBoundaryProp :: [(String, String, [BatchGroup], [NetMock])] -> Property
denseBoundaryProp eligible = counterexample (unlines wrong) (null wrong)
  where
    rows =
      -- A continuous query domain has no enumeration: dense must decline.
      [ ("normal", False, "a continuous query domain")
      , ("uniform", False, "a continuous query domain")
      -- Finite domain, but the prob function also takes a per-point neural
      -- symbol, so the dense result would be [B, V] and amortise over nothing.
      , ("autoNeuralProbMnistAdd", False, "a per-point neural symbol argument")
      -- The positive controls, one scalar and one composite, so a gate that
      -- refused everything could not pass this property.
      , ("coin", True, "a finite Int domain from the DiscreteValues tag")
      , ("letProbIntervalPair", True, "a finite (Bool, Bool) domain from the return type")
      ]
    wrong =
      [ "  " ++ n ++ ": expected " ++ (if want then "" else "no ") ++ "dense entry points ("
        ++ why ++ "), got " ++ show (denseEntryPoints src)
      | (n, want, why) <- rows
      , (m, src, _, _) <- eligible
      , m == n
      , not (null (denseEntryPoints src)) /= want ]

-- | Run every @dense@-declaring program's dense entry points in one torch
-- process. For each query group this checks three things:
--
--   * the dense vector really is the domain -- its length is @len(DOMAIN)@, so
--     the @[V]@ axis is pinned rather than merely being "some batch";
--   * @<method>_at(points, dense=True)@ matches the corpus expectation, i.e. the
--     gather into the dense vector agrees with per-point ground truth;
--   * @<method>_at(points, dense=False)@ does too, so the runtime dispatch is
--     value-neutral and forcing either axis is safe.
--
-- The dense=True direction is forced rather than left to the size heuristic:
-- most corpus programs have more domain values than query points, so the
-- automatic choice would take the direct path and never exercise M3 at all.
--
-- The @accArg@ flag runs the same check against topK-recompiled entries, whose
-- prob function takes the accumulated probability after the sample. Dense mode
-- needs no topK machinery of its own for that to work: under M5's per-element
-- rule the cutoff comparison is already an elementwise mask over whatever batch
-- is passed, and the domain is just another batch -- so pruning is per *domain
-- value* and the vector is identical to querying those values one at a time.
-- That is the whole answer to the design's open question about topK in dense
-- mode, and this property is what pins it.
runBatchedDense :: Bool -> FilePath -> [(String, String, [BatchGroup], [NetMock])] -> Property
runBatchedDense accArg _ [] = counterexample
  ("BatchedPython dense: no dense-declaring corpus programs found"
   ++ (if accArg then " at a topK threshold" else "")) False
runBatchedDense accArg py entries = ioProperty $ do
  hPutStrLn stderr ("BatchedPython dense" ++ (if accArg then " topK" else "") ++ ": "
                    ++ show (length entries) ++ " program(s), "
                    ++ show (sum [ length (denseEntryPoints src) | (_, src, _, _) <- entries ])
                    ++ " dense entry point(s), via " ++ py)
  cwd <- getCurrentDirectory
  let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ denseDriver accArg entries
  (code, out, err) <- withSystemTempFile "batched_dense.py" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle script
    hClose tmpHandle
    readProcessWithExitCode py [tmpPath] ""
  return $ case code of
    ExitSuccess -> counterexample (out ++ err) True
    ExitFailure _ -> counterexample ("Batched PyTorch dense differential failed:\n" ++ out ++ err) False

denseDriver :: Bool -> [(String, String, [BatchGroup], [NetMock])] -> String
denseDriver accArg entries = unlines $
  [ "import torch, sys, traceback"
  , "from pythonLibBatched import T, ConsInferenceList, EmptyInferenceList, AnyInferenceList, Left, Right"
  , "TOL = " ++ show probTolerance
  , "failures = []"
  , "def _leaf(x, i):"
  , "    return float(x[i]) if (torch.is_tensor(x) and x.dim() > 0) else float(x)"
  , "def _cmp(name, method, r, exp_p, exp_d):"
  , "    p = r[0]; d = r[1][0]"
  , "    for i in range(len(exp_p)):"
  , "        pv = _leaf(p, i)"
  , "        if abs(pv - exp_p[i]) > TOL:"
  , "            failures.append(name + '.' + method + ' pt ' + str(i) + ': prob ' + str(pv) + ' != ' + str(exp_p[i]))"
  , "        if pv != 0.0:"
  , "            dv = _leaf(d, i)"
  , "            if abs(dv - exp_d[i]) > TOL:"
  , "                failures.append(name + '.' + method + ' pt ' + str(i) + ': dim ' + str(dv) + ' != ' + str(exp_d[i]))"
  -- A topK-compiled prob function takes the accumulated probability and the
  -- runtime cutoff right after the sample (an integrate function only the
  -- cutoff); seed the former with 1.0 at the query root, as every other driver
  -- does, and pass the compiled-in default TOP_K_CUTOFF for the latter. Both
  -- are scalars, so they broadcast over the domain batch as well as over the
  -- query batch -- which is exactly why dense mode needs no topK plumbing.
  , "TOPK = " ++ (if accArg then "True" else "False")
  , "CUT = None"
  , "def _dense(name, method, main, samples, exp_p, exp_d, packed=None):"
  , "    ACC = (((1.0, CUT) if method == 'forward' else (CUT,)) if TOPK else ())"
  , "    dom = type(main).DOMAIN"
  , "    vec = getattr(main, method + '_dense')(*ACC)"
  , "    n = vec[0].shape[0] if (torch.is_tensor(vec[0]) and vec[0].dim() > 0) else 1"
  , "    if n != len(dom):"
  , "        failures.append(name + '.' + method + '_dense: vector length ' + str(n) + ' != domain size ' + str(len(dom)))"
  , "    at = getattr(main, method + '_at')"
  , "    _cmp(name, method + '_at[dense]', at(samples, *ACC, dense=True), exp_p, exp_d)"
  , "    _cmp(name, method + '_at[direct]', at(samples, *ACC, dense=False), exp_p, exp_d)"
  -- The scalar fast path: an already-packed [B] tensor skips the per-sample
  -- Python marshalling and looks the domain up with one torch comparison. It is
  -- a separate branch of dense_query, so it needs its own row -- and it is the
  -- only branch whose automatic choice can come out dense, which is why the
  -- unforced call is checked here and not above.
  , "    if packed is not None:"
  , "        _cmp(name, method + '_at[packed,dense]', at(packed, *ACC, dense=True), exp_p, exp_d)"
  , "        _cmp(name, method + '_at[packed,auto]', at(packed, *ACC), exp_p, exp_d)"
  ] ++
  concatMap programBlock entries ++
  [ "if failures:"
  , "    print('DENSE DIFFERENTIAL FAILURES (' + str(len(failures)) + '):')"
  , "    for f in failures: print('  ' + f)"
  , "    sys.exit(1)"
  , "print('BatchedPython dense OK: " ++ show (length entries) ++ " programs')"
  ]
  where
    programBlock (name, src, groups, netNames) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      ] ++
      [ "    _ns[" ++ show (netMockName nm) ++ "] = " ++ batchedMockExpr nm | nm <- netNames ] ++
      [ "    _main = _ns['main']"
      , "    CUT = _ns.get('TOP_K_CUTOFF')" ] ++
      concatMap (groupCall name src) groups ++
      [ "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    -- A group is checked only for the method that actually has a dense entry
    -- point: `integrate` can be absent (or itself outside the fragment) while
    -- `forward` is dense, and vice versa.
    groupCall name src g =
      let method = if bgIsCumul g then "integrate" else "forward"
          samples = "[" ++ intercalate ", " (map pyVal (bgSamples g)) ++ "]"
          -- Only a scalar (non-tuple, non-structural) batch has a packed form
          -- the fast path accepts; anything else exercises the marshalled path
          -- alone, which is correct -- dense_query routes it there too.
          packed = case batchLiteral (bgSamples g) of
            Just lit | not ("T(" `isPrefixOf` lit) -> ", " ++ lit
            _ -> ""
      in [ "    _dense(" ++ show name ++ ", " ++ show method ++ ", _main, " ++ samples
           ++ ", " ++ pyFloatList (bgExpProb g) ++ ", " ++ show (bgExpDim g) ++ packed ++ ")"
         | method `elem` denseEntryPoints src ]
    pyFloatList xs = "[" ++ intercalate ", " (map show xs) ++ "]"

-- ===========================================================================
-- M5: topK under batched mode (design pytorch-tensorizer)
-- ===========================================================================

-- | The threshold the topK differential compiles with. Chosen so that pruning
-- actually bites on part of the corpus (the property asserts that below), while
-- leaving enough programs unpruned that the "identical to scalar" direction is
-- exercised too.
topKDiffThresholds :: [Double]
topKDiffThresholds = [0.3, 0.6]

-- | Batched topK is /per element/: the pruning predicate
-- (@acc_prob * p_cond < TOP_K_CUTOFF@) is a @[B]@ mask feeding a @torch.where@,
-- so every batch element takes the same decision it would take alone in scalar
-- mode. This test pins that, and would fail loudly if anyone ever switched to a
-- per-batch rule (prune only when the whole batch agrees / on the batch max):
-- the fixtures below deliberately contain batches whose elements disagree about
-- which branches survive the cutoff, and under a per-batch rule the disagreeing
-- elements would take the other decision.
--
-- Ground truth is the /interpreter/ run of the same program compiled with the
-- same threshold in scalar mode — not the @.tst@ values, which are topK-off and
-- would be wrong wherever pruning bites.
--
-- Restricted to prob queries: the integrate path takes no @acc_prob@ parameter
-- (only the cutoff), and its pruning is seeded from its own root. Input is the @batched@-declaring corpus
-- entries, the same declaration 'batchedPythonTests' filters on — a program
-- whose fragment eligibility is asserted there is silently dropped here if it
-- fails to compile at a cutoff, which is why the non-vacuity assertion below
-- exists.
-- Returns the driver entries plus the number of programs on which the threshold
-- actually bites (some point's pruned value differs from its topK-off value) —
-- the property asserts that is non-zero, so the differential can never quietly
-- degenerate into "topK changed nothing anywhere". The third component names
-- the declared programs with a prob query that produced no pair at all, so a
-- silent drop is visible on stderr ('runBatchedTopK').
topKEntries :: [(String, Program, [TestCase])] -> ([(String, String, [BatchGroup], [NetMock])], [String], [String])
topKEntries entries = (map fst built, nub [n | ((n, _, _, _), True) <- built], dropped)
  where
    dropped = [ n | (n, _, tcs) <- entries, any isProbTestCase tcs
                  , not (any (\((m, _, _, _), _) -> takeWhile (/= '@') m == n) built) ]
    -- env0 (the plain default compile, used only to retarget expectations) does
    -- not depend on the threshold, so it is bound once per program -- outside
    -- the per-threshold loop -- rather than once per (program, threshold) pair.
    built =
      [ ((n ++ "@k=" ++ show thresh, src, groups', netNames), bites)
      | (n, p, tcs) <- entries
      , let qtcs = filter isProbTestCase tcs
      , not (null qtcs)
      , let netNames = networkMocks p
      , Right env0 <- [compile defaultCompilerConfig p]
      -- One topK compile per mode, re-thresholded per threshold: the cutoff
      -- is a runtime parameter (task runtime-parametric-topk-threshold), so
      -- only the emitted default TOP_K_CUTOFF differs between thresholds.
      , firstThresh : _ <- [topKDiffThresholds]
      , let confK = defaultCompilerConfig{topKThreshold = Just firstThresh}
      , Right envK0    <- [compile confK{batched = True}  p]
      , Right envKint0 <- [compile confK{batched = False} p]
      , thresh <- topKDiffThresholds
      , let envK    = withTopKCutoff thresh envK0
      , let envKint = withTopKCutoff thresh envKint0
      , Right srcLines <- [generateFunctionsBatched True envK]
      , Just groups  <- [batchGroups (collapsedEnumCtors (adts p) (intercalate "\n" srcLines)) (not (null netNames)) qtcs]
      , Just groups' <- [mapM (retarget p envKint) groups]
      , Just groups0 <- [mapM (retarget p env0) groups]
      , let src = intercalate "\n" srcLines
      , let bites = topKBites groups' groups0 ]
    -- Replace the .tst expectations by what the scalar/interpreter pipeline
    -- computes at the same threshold. A point the interpreter cannot evaluate
    -- drops the whole program rather than being silently skipped.
    retarget p env g = do
      pts <- zipWithM (interpPoint p env) (bgParamRows g) (bgSamples g)
      return g{bgExpProb = map fst pts, bgExpDim = map snd pts}
    interpPoint p env params sample = case runProbC p env params sample of
      Right (VProbDim pr d) -> Just (pr, d)
      _                     -> Nothing

-- | Whether a program's topK-pruned values actually differ from its topK-off
-- values — i.e. whether the threshold bites at all on this program.
topKBites :: [BatchGroup] -> [BatchGroup] -> Bool
topKBites withK withoutK =
  or [ abs (a - b) > probTolerance
     | (gk, g0) <- zip withK withoutK, (a, b) <- zip (bgExpProb gk) (bgExpProb g0) ]

runBatchedTopK :: FilePath -> ([(String, String, [BatchGroup], [NetMock])], [String], [String]) -> Property
runBatchedTopK py (topkEligible, biting, dropped)
  | null topkEligible = counterexample "BatchedPython topK: no eligible programs" False
  | null biting = counterexample
      ("BatchedPython topK: thresholds " ++ show topKDiffThresholds
       ++ " prune nothing anywhere in the corpus -- the differential is vacuous") False
  | otherwise = ioProperty $ do
      hPutStrLn stderr ("BatchedPython topK: " ++ show (length topkEligible)
                        ++ " program/threshold pairs over " ++ show topKDiffThresholds
                        ++ " (pruning bites on " ++ intercalate ", " biting ++ "), via " ++ py
                        ++ (if null dropped then "" else
                              "\n  dropped (no topK compile, batchable groups or interpreter answer at a cutoff): "
                              ++ intercalate ", " dropped))
      cwd <- getCurrentDirectory
      let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n"
                   ++ batchedDriver True topkEligible
      (code, out, err) <- withSystemTempFile "batched_topk.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle script
        hClose tmpHandle
        readProcessWithExitCode py [tmpPath] ""
      return $ case code of
        ExitSuccess   -> counterexample (out ++ err) True
        ExitFailure _ -> counterexample ("Batched PyTorch topK differential failed:\n" ++ out ++ err) False

-- ===========================================================================
-- M3: gradient hygiene (design pytorch-tensorizer)
-- ===========================================================================

-- | Acceptance test for M3's double-'where' masking: for every eligible program
-- whose batched code contains a gradient-unsafe op wrapped by 'safe_log'/
-- 'safe_div', feed a batch that straddles its guard boundary (the corpus points
-- already include off-support samples like @p(-1.0)@) with @requires_grad@ on the
-- sample, run backward, and assert the sample gradient is NaN-free. Without the
-- masking, autograd flows @0 * inf = NaN@ through the untaken (log-of-negative /
-- divide-by-zero) arm; the differential's value check alone would not catch it,
-- since the forward values are already correct.
--
-- Restricted to non-neural programs with a plain-float sample batch (a
-- differentiable leaf); the log-domain programs (@logNormal@ and friends) are the
-- ones that actually exhibit the bug.
runBatchedGradients :: FilePath -> [(String, String, [BatchGroup], [NetMock])] -> Property
runBatchedGradients py eligible
  | null probes = ioProperty $ do
      hPutStrLn stderr "BatchedPython gradients: no safe_log/safe_div programs found (skipped)."
      return True
  | otherwise = ioProperty $ do
      hPutStrLn stderr ("BatchedPython gradients: " ++ show (length probes)
                        ++ " unsafe-op programs, via " ++ py)
      cwd <- getCurrentDirectory
      let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ gradientDriver probes
      (code, out, err) <- withSystemTempFile "batched_grad.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle script
        hClose tmpHandle
        readProcessWithExitCode py [tmpPath] ""
      return $ case code of
        ExitSuccess   -> counterexample (out ++ err) True
        ExitFailure _ -> counterexample ("Batched PyTorch gradient check failed:\n" ++ out ++ err) False
  where
    probes = [ (name, src, xs, bgParamExprs g)
             | (name, src, groups, netNames) <- eligible
             , null netNames
             , "safe_log(" `isInfixOf` src || "safe_div(" `isInfixOf` src
             , g <- take 1 [gr | gr <- groups, not (bgIsCumul gr)]
             , Just xs <- [floatBatchLit (bgSamples g)] ]

-- | A batch tensor literal for a homogeneous list of /float/ samples, or
-- 'Nothing' if any sample is not a plain float (so it is a differentiable leaf,
-- not a bool/int/tuple).
floatBatchLit :: [IRValue] -> Maybe String
floatBatchLit vs
  | not (null vs), all isFloatV vs =
      Just ("torch.tensor([" ++ intercalate ", " [show f | VFloat f <- vs] ++ "])")
  | otherwise = Nothing
  where isFloatV (VFloat _) = True
        isFloatV _          = False

-- | The single Python script for the gradient check: run each program's
-- @main.forward@ on a @requires_grad@ float batch, backward through the prob
-- field, and record any NaN gradient.
gradientDriver :: [(String, String, String, [String])] -> String
gradientDriver probes = unlines $
  [ "import torch, sys, traceback"
  , "from pythonLibBatched import T"
  , "failures = []"
  ] ++ concatMap block probes ++
  [ "if failures:"
  , "    print('BATCHED GRADIENT FAILURES (' + str(len(failures)) + '):')"
  , "    for f in failures: print('  ' + f)"
  , "    sys.exit(1)"
  , "print('BatchedPython gradients OK: " ++ show (length probes) ++ " programs')"
  ]
  where
    block (name, src, xs, params) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      , "    _main = _ns['main']"
      , "    _x = (" ++ xs ++ ").requires_grad_(True)"
      , "    _r = _main.forward(_x" ++ concatMap (", " ++) params ++ ")"
      , "    _p = _r[0]"
      -- A fully out-of-support batch would make _p constant (no grad path); the
      -- corpus points always include an in-support sample, so guard defensively.
      , "    if getattr(_p, 'requires_grad', False):"
      , "        _p.sum().backward()"
      , "        if _x.grad is None:"
      , "            failures.append(" ++ show name ++ " + ': sample grad is None')"
      , "        elif torch.isnan(_x.grad).any() or torch.isinf(_x.grad).any():"
      , "            failures.append(" ++ show name ++ " + ': sample grad has NaN/Inf: ' + str(_x.grad.tolist()))"
      , "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]

-- ===========================================================================
-- M4: batched generate (design pytorch-tensorizer)
-- ===========================================================================

-- | Acceptance test for M4 (batched generate), extended to neural (task
-- neural-generate-parity) to cover a read-logits network's own sampling
-- (categorical/Gaussian) and cross-network composition (e.g. MNIST addition).
--
-- There is no per-draw ground truth for a stochastic 'generate' (unlike
-- forward/integrate, which have an exact expected value at each query point),
-- so the differential instead mirrors Spec.hs's existing @testSamplingProb@
-- idiom: draw a large batch, then estimate an empirical density in an
-- epsilon-window around each of the program's *existing* prob query points
-- (the same @.tst@-declared ground truth the value differential already
-- checks) and compare to the declared density within 'samplingTolerance'.
-- This reuses ground truth already in the corpus (no second sampling
-- distribution to generate or compare against) and is one vectorized torch
-- pass per point rather than one Python call per sample.
--
-- Non-neural programs draw one shared @main.generate(_batchN)@ batch and
-- check it against every point (the distribution does not depend on the
-- point). Neural programs' distribution *does* depend on the point (each
-- point supplies its own read-logits input symbol, per the corpus's mode-2
-- verbatim-logit convention), so each point gets its own
-- @main.generate(sym, _batchN)@ call: the point's row is sliced out of the
-- group's already-batched symbol tensor ('bgParamExprs', the same per-point
-- @[B, n]@ column 'batchSymParamCols' builds for forward/integrate) and
-- broadcast to a fresh @[N, n]@ batch via 'expand'.
--
-- Restricted to query points whose sample is a bare float/int/bool (not a
-- tuple): a tuple-valued window density would need per-leaf volume handling
-- the corpus's existing (sample, dim) pairs don't disentangle. A program
-- whose generate needs a different argument count than expected (e.g. a
-- ThetaTree test override, as in @gaussListTheta@/@lambdaThetaInverse@) is
-- skipped dynamically in the driver (arity-checked via
-- @inspect.signature@), since Haskell-side arity bookkeeping would only
-- duplicate what the emitted signature already says.
runBatchedGenerate :: FilePath -> [(String, String, [BatchGroup], [NetMock])] -> Property
runBatchedGenerate _ [] = counterexample "BatchedPython generate: no eligible corpus programs found" False
runBatchedGenerate py eligible
  | null nonNeuralProbes && null neuralProbes = ioProperty $ do
      hPutStrLn stderr "BatchedPython generate: no eligible programs with a compiled generate found (skipped)."
      return True
  | otherwise = ioProperty $ do
      hPutStrLn stderr ("BatchedPython generate: " ++ show (length nonNeuralProbes) ++ " non-neural + "
                        ++ show (length neuralProbes) ++ " neural programs, via " ++ py)
      cwd <- getCurrentDirectory
      let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n"
                 ++ generateDriver nonNeuralProbes neuralProbes
      (code, out, err) <- withSystemTempFile "batched_generate.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle script
        hClose tmpHandle
        readProcessWithExitCode py [tmpPath] ""
      return $ case code of
        ExitSuccess   -> counterexample (out ++ err) True
        ExitFailure _ -> counterexample ("Batched PyTorch generate differential failed:\n" ++ out ++ err) False
  where
    nonNeuralProbes = [ (name, src, points)
             | (name, src, groups, netNames) <- eligible
             , null netNames
             , let points = [ (pyVal s, ep, ed)
                            | g <- groups, not (bgIsCumul g)
                            , (s, ep, ed) <- zip3 (bgSamples g) (bgExpProb g) (bgExpDim g)
                            , isScalarSample s, densityLivesOnScalar s ed ]
             , not (null points) ]
    neuralProbes = [ (name, src, netNames, bgParamExprs g, points)
             | (name, src, groups, netNames) <- eligible
             , not (null netNames)
             , (g:_) <- [[gr | gr <- groups, not (bgIsCumul gr)]]
             , let points = [ (pyVal s, ep, ed, i)
                            | (i, s, ep, ed) <- zip4 [0 :: Int ..] (bgSamples g) (bgExpProb g) (bgExpDim g)
                            , isScalarSample s, densityLivesOnScalar s ed ]
             , not (null points) ]

-- | The scalar twin of @TestCorpus.densityLivesOnSamples@: a window over drawn
-- samples can only estimate a density with as many dimensions as the sample
-- has continuous coordinates (one for a float, none for an int or bool). A
-- larger dim is the density of a null-probability event of a continuous latent
-- (@x == 0.0@ observed True; task
-- sampling-matches-pdf-continuous-equality-density, by design), which sampling
-- cannot reach, so the generate differential does not probe it.
densityLivesOnScalar :: IRValue -> Int -> Bool
densityLivesOnScalar (VFloat _) ed = ed <= 1
densityLivesOnScalar _ ed = ed <= 0

-- | Is this sample a bare scalar leaf (not a tuple)? 'isNum'/'isBoolV' already
-- cover exactly float/int/bool between them (see 'batchLiteral').
isScalarSample :: IRValue -> Bool
isScalarSample v = isNum v || isBoolV v

-- | The single Python script for the generate check: for each non-neural
-- program, draw one shared large batch and test it against every query
-- point's epsilon-window density estimate; for each neural program, draw a
-- fresh per-point batch (the point's own read-logits symbol, repeated) and test
-- that point alone. Single-shot rather than retried -- the batch size is
-- fixed large enough, and the seed is pinned, to keep this non-flaky.
generateDriver :: [(String, String, [(String, Double, Int)])]
               -> [(String, String, [NetMock], [String], [(String, Double, Int, Int)])]
               -> String
generateDriver nonNeuralProbes neuralProbes = unlines $
  [ "import torch, sys, traceback, inspect"
  , "from pythonLibBatched import T"
  , "torch.manual_seed(1234)"
  , "N = 50000"
  , "TOL = " ++ show samplingTolerance
  , "failures = []"
  , "checked = 0"
  , "skipped = 0"
  ] ++ concatMap block nonNeuralProbes ++ concatMap neuralBlock neuralProbes ++
  [ "if checked == 0:"
  , "    failures.append('no program actually had its generate density checked (all skipped)')"
  , "if failures:"
  , "    print('BATCHED GENERATE FAILURES (' + str(len(failures)) + '):')"
  , "    for f in failures: print('  ' + f)"
  , "    sys.exit(1)"
  , "print('BatchedPython generate OK: ' + str(checked) + ' checks, ' + str(skipped) + ' skipped (arity mismatch))')"
  ]
  where
    block (name, src, points) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      , "    _main = _ns['main']"
      , "    _sig = inspect.signature(_main.generate)"
      , "    if len(_sig.parameters) != 1:"
      , "        skipped += 1"
      , "    else:"
      , "        _batch = _main.generate(N)"
      , "        _bt = _batch if torch.is_tensor(_batch) else torch.as_tensor(float(_batch))"
      , "        _btd = _bt.double()"
      , "        checked += 1"
      ] ++
      concatMap (pointCheck name "_btd") points ++
      -- A generate that is a declared stub (a structurally heterogeneous draw,
      -- design heterogeneous-batch-inference Component 4) is a skip, not a
      -- failure -- the same treatment as the arity mismatch above.
      [ "except NotImplementedError:"
      , "    skipped += 1"
      , "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    -- Each point supplies its own read-logits symbol (a row of the group's [B, n]
    -- symbol tensor, per argument position), so it needs its own generate call
    -- and its own arity check (the signature is the same for every point of a
    -- program, but checking it once per point keeps this block symmetric with
    -- 'block' and costs nothing at this scale).
    neuralBlock (name, src, netNames, paramExprs, points) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      ] ++
      [ "    _ns[" ++ show (netMockName nm) ++ "] = " ++ batchedMockExpr nm | nm <- netNames ] ++
      [ "    _main = _ns['main']"
      , "    _sig = inspect.signature(_main.generate)"
      , "    if len(_sig.parameters) != " ++ show (length paramExprs + 1) ++ ":"
      , "        skipped += 1"
      , "    else:"
      ] ++
      concatMap (neuralPointCheck name paramExprs) points ++
      -- A generate that is a declared stub (a structurally heterogeneous draw,
      -- design heterogeneous-batch-inference Component 4) is a skip, not a
      -- failure -- the same treatment as the arity mismatch above.
      [ "except NotImplementedError:"
      , "    skipped += 1"
      , "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    neuralPointCheck name paramExprs (xExpr, expProb, expDim, rowIx) =
      let argVar j = "_sym" ++ show rowIx ++ "_" ++ show j
          argSetup = [ "        " ++ argVar j ++ " = (" ++ e ++ ")[" ++ show rowIx ++ ":" ++ show (rowIx + 1) ++ "].expand(N, -1)"
                     | (j, e) <- zip [0 :: Int ..] paramExprs ]
          callArgs = intercalate ", " (map argVar [0 .. length paramExprs - 1] ++ ["N"])
          batchVar = "_batch" ++ show rowIx
          batchVarD = batchVar ++ "d"
      in argSetup ++
         [ "        " ++ batchVar ++ " = _main.generate(" ++ callArgs ++ ")"
         , "        " ++ batchVarD ++ " = (" ++ batchVar ++ " if torch.is_tensor(" ++ batchVar
             ++ ") else torch.as_tensor(float(" ++ batchVar ++ "))).double()"
         , "        checked += 1"
         ] ++
         pointCheck name batchVarD (xExpr, expProb, expDim)
    pointCheck name batchVarD (xExpr, expProb, expDim) =
      -- A tighter window (Spec.hs's testSamplingProb uses 1e-9, comparing
      -- interpreter Doubles) is unusable here: torch.rand/randn default to
      -- float32, so a discrete atom threaded through a torch.where alongside a
      -- float32 draw is itself rounded to float32 precision (~1e-7 relative),
      -- which an exact-match window at 1e-9 would simply miss. 1e-4 is still
      -- tight enough to exclude a neighbouring continuous arm's contribution
      -- (whose density over a 1e-4-wide window is on the order of 1e-4 * its
      -- density, negligible next to samplingTolerance) while comfortably
      -- covering float32 rounding.
      let eps = if expDim == 0 then 1e-4 else 0.05 :: Double
      in [ "        _x = float(" ++ xExpr ++ ")"
         , "        _inside = (torch.abs(" ++ batchVarD ++ " - _x) <= " ++ show (eps / 2.0) ++ ").double().mean().item()"
         , "        _est = _inside / (" ++ show eps ++ " ** " ++ show expDim ++ ")"
         , "        if abs(_est - " ++ show expProb ++ ") > TOL:"
         , "            failures.append(" ++ show name ++ " + ': generate density at ' + str(_x) + ' estimated ' + str(_est) + ' != ' + str(" ++ show expProb ++ "))"
         ]

-- | Programs whose .tst file carries a `slow` header (see TestCaseParser) are
-- expensive enough (deep recursive plan enumeration, run through both the
-- optimized and unoptimized interpreter passes) to noticeably slow day-to-day
-- `stack test`, and unlikely to catch regressions outside the code they pin.
-- Excluded from end2endTests; covered instead by slowEnd2EndTests, which
-- Spec.hs includes only when NEST_SLOW_TESTS is set (see Spec.hs's Slow
-- group).
-- ===========================================================================
-- Branch-counted backend coverage (fuzz-qc-compiler-bugs item 3)
-- ===========================================================================

-- | Corpus programs whose probability body enumerates two enumerable operands
-- -- the shape that reaches 'SPLL.Semiring.enumSumP', and therefore the only
-- one that needs a @(probability, branchCount)@ pair reduced out of a single
-- pass over the enumeration. Asserted, not filtered: if a compiler change
-- stops routing these through the shared-loop node, the group says so rather
-- than silently testing nothing.
branchCountPairedPrograms :: [String]
branchCountPairedPrograms =
  ["plusPolyInt", "minusPolyInt", "twoCoins", "discreteFloats", "letTwoEnumerable"]

-- | Backend coverage for the branch-counted paired enum sum.
--
-- Branch counting is an opt-in diagnostic flag, so no corpus row runs under it
-- -- which means the emitted-code path for the IR shape a countBranches compile
-- builds and a default compile never does (one enumeration map read by two
-- reductions, the probability sum and the branch-count sum) is otherwise
-- executed by no backend at all. This group compiles the programs above with
-- @countBranches = True@, runs the emitted Python and Julia, and checks the
-- whole @(prob, dim, branchCount)@ triple against the interpreter's answer for
-- the same query points. It is a differential -- no branch count is written
-- down here, so the group needs no maintenance when a count legitimately
-- changes.
branchCountBackendTests :: IO TestTree
branchCountBackendTests = do
  loaded <- mapM loadBranchCountCase branchCountPairedPrograms
  return $ testGroup "BranchCountBackends"
    [ testGroup "shares one enumeration pass between both reductions"
        [ testProperty n (once (counterexample
            (n ++ " no longer compiles to a shared enumeration pass under countBranches; \
                  \pick a program that does, or this group tests nothing")
            (any sharesOneMapAcrossTwoReduces (irEnvBodies env))))
        | (n, _, env, _) <- loaded ]
    -- The paired node's log-space reduction (log-sum-exp on the probability
    -- component, a plain sum on the branch count) is a second code path in
    -- every backend that has one. Checked through the interpreter only, which
    -- is where the corpus checks log space generally.
    , testGroup "log space agrees with linear"
        [ testProperty n (once (branchCountLogSpace n prog rows)) | (n, prog, _, rows) <- loaded ]
    -- One julia process for all of them: startup dominates the work here.
    , testProperty "Julia" (once (branchCountJulia loaded))
    , testGroup "Python"
        [ testProperty n (once (branchCountPython n env rows)) | (n, _, env, rows) <- loaded ]
    ]
-- | The property the retired @IREnumSumPaired@ existed to provide, checked
-- structurally on the tensor form that replaced it (design ir-tensor-values,
-- task retire-irenumsum): some let-bound tensor map is read by two or more
-- separate reductions.
--
-- This is the load-bearing half of that node, and the acceptance criterion
-- retire-irenumsum was most likely to fail. A branch-counting compile needs
-- both a probability sum and a branch-count sum over one enumeration, and two
-- single-scalar loops could not share a loop body -- so before the tensor
-- form each re-embedded the whole per-iteration computation, doubling the
-- IR at every level of a recursively-enumerable structure (fuzz-qc-compiler-bugs
-- item 3). Naming the mapped axis is what makes the sharing expressible, so
-- asserting the shared read is a stronger check than asserting a constructor:
-- it fails if a future rewrite reintroduces the duplication under any spelling.
sharesOneMapAcrossTwoReduces :: IRExpr -> Bool
sharesOneMapAcrossTwoReduces = irAnyNode shared
  where
    shared (IRLetIn n (IRBuiltin BMap _) body) = reducesOf n body >= 2
    shared _ = False
    -- Reductions in `body` whose operand mentions the bound axis `n`.
    reducesOf n body = length
      [ () | e <- irNodes body
           , IRBuiltin (BReduce _ _) [t] <- [e]
           , irAnyNode (== IRVar n) t ]

-- | Every node of an expression, itself included.
irNodes :: IRExpr -> [IRExpr]
irNodes e = e : concatMap irNodes (getIRSubExprs e)

-- | A program, its branch-counted compile, and one row per pinned query point
-- carrying the interpreter's @(prob, dim, branchCount)@ for it.
type BranchCountCase = (String, Program, IREnv, [(TestCase, Double, Int, Double)])

loadBranchCountCase :: String -> IO BranchCountCase
loadBranchCountCase name = do
  prog <- corpusPplPath name >>= parseProgram
  (_, _, _, tcs0) <- corpusTstPath name >>= parseTestCases
  let tcs = map (shapeNeuralTestCase prog) tcs0
  let env = either (error . ((name ++ ": ") ++) . show) id
              (compile defaultCompilerConfig{countBranches = True} prog)
      queries = filter (\t -> isProbTestCase t || isCumulTestCase t) tcs
      row t = case runOf t of
        Right (VProbDimBC p d bc) -> (t, p, d, bc)
        other -> error (name ++ ": branch-counted run gave " ++ show other)
        where runOf (ProbTestCase _ s ps _)  = runProbC prog env ps s
              runOf (CumulTestCase _ s ps _) = runIntegC prog env ps s
              runOf _ = error "not a query case"
  return (name, prog, env, map row queries)

-- | Every node in every compiled function body of an environment.
irEnvBodies :: IREnv -> [IRExpr]
irEnvBodies (IREnv groups _ _) = concatMap bodies groups
  where bodies g = [e | Just (e, _) <- [genFun g, probFun g, integFun g, writeLogitsFun g, normalFun g]]

irAnyNode :: (IRExpr -> Bool) -> IRExpr -> Bool
irAnyNode f e = f e || any (irAnyNode f) (getIRSubExprs e)

-- With countBranches on the emitted result is @(prob, (dim, (bc, imposs)))@,
-- one field deeper than the default @(prob, (dim, imposs))@ the other backend
-- harnesses in this module read.
branchCountPython :: String -> IREnv -> [(TestCase, Double, Int, Double)] -> Property
branchCountPython name env rows = ioProperty $ do
  let src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True env)
      checks = concatMap (\(tc, p, d, bc) ->
        let (sample, params, fn) = pyCall tc
        in "tmp = " ++ fn ++ "(" ++ intercalate ", " (map pyVal (sample : params)) ++ ")\n\
           \_chk(\"" ++ name ++ "/" ++ tcName tc ++ "\", tmp[0], tmp[1][0], tmp[1][1][0], "
           ++ show p ++ ", " ++ show d ++ ", " ++ show bc ++ ")\n") rows
      code = unpack (replace (pack "from torch.nn import Module")
                             (pack "\nclass Module:\n  pass\n") (pack src))
             ++ "\ndef _chk(what, p, d, bc, ep, ed, ebc):\n\
                \  if abs(p - ep) > " ++ show probTolerance ++ ":\n\
                \    raise ValueError(what + ': prob ' + str(p) + ' != ' + str(ep))\n\
                \  if type(d) is not int or (p != 0 and d != ed):\n\
                \    raise ValueError(what + ': dim ' + str(d) + ' != ' + str(ed))\n\
                \  if abs(bc - ebc) > " ++ show probTolerance ++ ":\n\
                \    raise ValueError(what + ': branch count ' + str(bc) + ' != ' + str(ebc))\n"
             ++ checks
  (_, _, _, h) <- createProcess (proc "python3" ["-c", code])
  c <- waitForProcess h
  return $ case c of
    ExitSuccess   -> property True
    ExitFailure _ -> counterexample (name ++ ": branch-counted Python differed from the interpreter") False
  where pyCall (ProbTestCase _ s ps _)  = (s, ps, "main.forward")
        pyCall (CumulTestCase _ s ps _) = (s, ps, "main.integrate")
        pyCall _ = error "not a query case"

branchCountJulia :: [BranchCountCase] -> Property
branchCountJulia loaded = ioProperty $ do
  projectDir <- getCurrentDirectory
  let prelude = "include(\"" ++ projectDir ++ "/juliaLib.jl\")\n\
                \using .JuliaSPPLLib\n\
                \function chk(what, p, d, bc, ep, ed, ebc)\n\
                \  if abs(p - ep) > " ++ show probTolerance ++ "\n\
                \    error(what * \": prob \" * string(p) * \" != \" * string(ep))\n\
                \  end\n\
                \  if typeof(d) != Int || (p != 0 && d != ed)\n\
                \    error(what * \": dim \" * string(d) * \" != \" * string(ed))\n\
                \  end\n\
                \  if abs(bc - ebc) > " ++ show probTolerance ++ "\n\
                \    error(what * \": branch count \" * string(bc) * \" != \" * string(ebc))\n\
                \  end\n\
                \end\n"
      body = concatMap (\(idx, (name, _, env, rows)) ->
        let m = "BCProg" ++ show (idx :: Int)
        in "module " ++ m ++ "\nusing ..JuliaSPPLLib\n"
           ++ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions env) ++ "\nend\n"
           ++ concatMap (\(tc, p, d, bc) ->
                let (sample, params, fn) = jlCall tc
                in "tmp = " ++ m ++ "." ++ fn ++ "("
                   ++ intercalate ", " (map (juliaVal . qualifyConstructors m) (sample : params)) ++ ")\n\
                   \chk(\"" ++ name ++ "/" ++ tcName tc ++ "\", tmp[1], tmp[2][1], tmp[2][2][1], "
                   ++ show p ++ ", " ++ show d ++ ", " ++ show bc ++ ")\n") rows)
        (zip [0..] loaded)
  code <- withSystemTempFile "julia_bc.jl" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle (prelude ++ body)
    hClose tmpHandle
    (_, _, _, h) <- createProcess (proc "julia" (juliaTestFlags ++ [tmpPath]))
    waitForProcess h
  return $ case code of
    ExitSuccess   -> property True
    ExitFailure _ -> counterexample "branch-counted Julia differed from the interpreter" False
  where jlCall (ProbTestCase _ s ps _)  = (s, ps, "main_prob")
        jlCall (CumulTestCase _ s ps _) = (s, ps, "main_integ")
        jlCall _ = error "not a query case"

-- | exp() of the log-space branch-counted probability must reproduce the linear
-- one, and the branch count -- which is never a log-space value -- must be
-- identical.
branchCountLogSpace :: String -> Program -> [(TestCase, Double, Int, Double)] -> Property
branchCountLogSpace name prog rows =
  case compile defaultCompilerConfig{countBranches = True, logSpace = True} prog of
    Left err -> counterexample (name ++ ": log-space compile failed: " ++ show err) False
    Right env -> conjoin (map (check env) rows)
  where
    check env (tc, p, _, bc) = case runOf env tc of
      Right (VProbDimBC lp _ lbc) -> conjoin
        [ counterexample (name ++ "/" ++ tcName tc ++ ": exp(" ++ show lp ++ ") /= " ++ show p)
            (abs (exp lp - p) < probTolerance)
        , counterexample (name ++ "/" ++ tcName tc ++ ": branch count " ++ show lbc ++ " /= " ++ show bc)
            (lbc == bc) ]
      other -> counterexample (name ++ ": log-space run gave " ++ show other) False
    runOf env (ProbTestCase _ s ps _)  = runProbC prog env ps s
    runOf env (CumulTestCase _ s ps _) = runIntegC prog env ps s
    runOf _ _ = error "not a query case"

tcName :: TestCase -> String
tcName (ProbTestCase n _ _ _)  = n
tcName (CumulTestCase n _ _ _) = n
tcName _ = "?"

-- * Impact analysis keys
--
-- Each corpus sweep below executes a program only when the hash of what it
-- consumes differs from the one recorded at its last pass ('ImpactManifest';
-- docs-repo task emitted-code-test-impact-analysis). A key must cover
-- everything the check reads: a value the check consumes that is missing from
-- its key is a pass that survives a change it should not have.

-- | Bump a check's version when its logic changes in a way earlier passes
-- must not survive. 'harnessFingerprint' (the source of this module) is the
-- backstop for a forgotten bump.
interpreterCheckVersion, normalizationCheckVersion, pythonCheckVersion, juliaCheckVersion :: String
interpreterCheckVersion   = "interpreter-v1"
normalizationCheckVersion = "normalization-v1"
pythonCheckVersion        = "python-v1"
juliaCheckVersion         = "julia-v1"

selectPassCheckVersion, planEngineCheckVersion, budgetZeroCheckVersion, planLogSpaceCheckVersion, neuralLogSpaceCheckVersion :: String
selectPassCheckVersion    = "select-pass-v1"
planEngineCheckVersion    = "plan-engine-v1"
budgetZeroCheckVersion    = "budget-zero-v1"
planLogSpaceCheckVersion  = "plan-log-space-v1"
neuralLogSpaceCheckVersion = "neural-log-space-v1"

pythonWriteLogitsCheckVersion, juliaWriteLogitsCheckVersion, batchedCheckVersion :: String
pythonWriteLogitsCheckVersion = "python-writelogits-v1"
juliaWriteLogitsCheckVersion  = "julia-writelogits-v1"
batchedCheckVersion           = "batched-v1"

-- | The parts of the parsed program the @run*C@ entry points read besides the
-- compiled 'IREnv' (networks, the writeLogits registry, ADT declarations).
programRuntimeFields :: Program -> String
programRuntimeFields p = show (neurals p, writeLogitsDecls p, adts p)

-- | What 'testInterpreter' derives from a row through the compiler's own
-- functions rather than reading it off the row: writeLogits arguments and
-- slot indices (typed via the program), argmax's shaped mock parameters.
interpreterRowInputs :: Program -> TestCase -> String
interpreterRowInputs p tc = case tc of
  WriteLogitsLengthTestCase _ _ ex _    -> show (writeLogitsArgsFor p ex)
  WriteLogitsSlotTestCase _ t ex idxOf _ -> show (writeLogitsArgsFor p ex, planIndexOf (endpointPlan p t) idxOf)
  ArgmaxPTestCase _ params _            -> show (argmaxParams p params)
  _                                     -> ""

-- | Key of an interpreter-run 'testInterpreter' sweep over one program.
interpreterKey :: Manifest -> Program -> Either CompilerError IREnv -> [TestCase] -> IO (Maybe String)
interpreterKey _ _ (Left _) _ = return Nothing
interpreterKey m p (Right env) tcs = do
  h <- harnessFingerprint m
  i <- interpreterFingerprint m
  return $ Just $ hashKey
    [ interpreterCheckVersion, h, i, show env, programRuntimeFields p, show tcs
    , concatMap (interpreterRowInputs p) tcs, show (probTolerance, writeLogitsSlotTolerance) ]

-- | Key of an interpreter differential over several compiles of one program
-- (SelectPassNoOp, the plan-engine and budget-0 differentials): every compile
-- as shown, a refusal included (it is the compiler's answer, and the
-- differentials skip or compare it), plus the program's runtime fields, the
-- rows, the tolerance and the interpreter. A compile that crashes while shown
-- has no key, so the check executes.
differentialKey :: Manifest -> String -> Program -> [Either CompilerError IREnv] -> [TestCase] -> IO (Maybe String)
differentialKey m version p envs tcs = do
  h <- harnessFingerprint m
  i <- interpreterFingerprint m
  return $ Just $ hashKey
    ([version, h, i, programRuntimeFields p, show tcs, show probTolerance] ++ map show envs)

-- | Key of 'testPythonWriteLogits': the exact script it runs, plus the
-- Python runtime.
pythonWriteLogitsKey :: Manifest -> [NetMock] -> Either CompilerError IREnv -> [WriteLogitsRow] -> IO (Maybe String)
pythonWriteLogitsKey _ _ (Left _) _ = return Nothing
pythonWriteLogitsKey m nets (Right env) rows = do
  projectDir <- getCurrentDirectory
  h <- harnessFingerprint m
  py <- pythonFingerprint m
  return $ Just $ hashKey [pythonWriteLogitsCheckVersion, h, py, pythonWriteLogitsScript projectDir nets env rows]

-- | Key of one program's part of 'testJuliaWriteLogitsAll': its module and
-- row checks as 'juliaWriteLogitsBody' renders them alone (the module number
-- depends on the batch), plus the Julia runtime.
juliaWriteLogitsKey :: Manifest -> Either CompilerError IREnv -> [WriteLogitsRow] -> [NetMock] -> IO (Maybe String)
juliaWriteLogitsKey _ (Left _) _ _ = return Nothing
juliaWriteLogitsKey m (Right env) rows nets = do
  h <- harnessFingerprint m
  jl <- juliaFingerprint m
  return $ Just $ hashKey [juliaWriteLogitsCheckVersion, h, jl, juliaWriteLogitsBody [(env, rows, nets)]]

-- | Key of one program's part of a batched-backend differential (@check@
-- names which): everything the driver renders for it (name, batched source,
-- query groups, network mocks) and the torch runtime ('torchFingerprint').
batchedKey :: Manifest -> String -> String -> (String, String, [BatchGroup], [NetMock]) -> IO (Maybe String)
batchedKey m torch check (n, src, gs, nets) = do
  h <- harnessFingerprint m
  return $ Just $ hashKey [batchedCheckVersion, check, h, torch, n, src, show gs, show nets]

-- | Key of 'discreteProbsNormalized' on one program.
normalizationKey :: Manifest -> Program -> Either CompilerError IREnv -> IO (Maybe String)
normalizationKey _ _ (Left _) = return Nothing
normalizationKey m p (Right env) = do
  h <- harnessFingerprint m
  i <- interpreterFingerprint m
  return $ Just $ hashKey
    [ normalizationCheckVersion, h, i, show env, programRuntimeFields p
    , show (normalizationDraws p), show normalizationTolerance ]

-- | Key of 'testPython': the exact script it runs (emitted module, mocks,
-- row checks with the tolerance spliced in), plus the Python runtime.
pythonKey :: Manifest -> [NetMock] -> Either CompilerError IREnv -> [TestCase] -> IO (Maybe String)
pythonKey _ _ (Left _) _ = return Nothing
pythonKey m nets (Right env) tcs = do
  projectDir <- getCurrentDirectory
  h <- harnessFingerprint m
  py <- pythonFingerprint m
  return $ Just $ hashKey [pythonCheckVersion, h, py, pythonTestScript projectDir nets env tcs]

-- | Key of one program's part of a 'testJuliaAll' shard: its module and row
-- checks as 'juliaBatchTestCode' renders them, under a fixed module name (the
-- shard's numbering depends on which other programs share it), plus the
-- Julia runtime and flags.
juliaKey :: Manifest -> Either CompilerError IREnv -> [TestCase] -> [NetMock] -> IO (Maybe String)
juliaKey _ (Left _) _ _ = return Nothing
juliaKey m (Right env) tcs nets = do
  h <- harnessFingerprint m
  jl <- juliaFingerprint m
  let src = intercalate "\n" (SPLL.CodeGenJulia.generateFunctions env)
  return $ Just $ hashKey [juliaCheckVersion, h, jl, show juliaTestFlags, juliaBatchTestCode "" [(src, tcs, nets)]]

-- | The corpus sweeps record their passes in @manifest@ ('ImpactManifest').
end2endTests :: Corpus -> Manifest -> IO TestTree
end2endTests corpus manifest =
  buildEnd2EndTree corpus manifest "End2End" "End2End" Default SkipSlow True

-- | The slow-only twin of end2endTests: same Interpreter/Unoptimized checks,
-- restricted to `slow`-headered programs. Julia/Python/Normalization are
-- skipped since these programs are Interpreter-only by design (see their
-- .tst headers).
slowEnd2EndTests :: Corpus -> Manifest -> IO TestTree
slowEnd2EndTests corpus manifest =
  buildEnd2EndTree corpus manifest "Slow.End2End (slow)" "End2End (slow)" Slow OnlySlow False

-- | Corpus programs the interpreter cannot serve at the default -O, each with
-- why (task impact-analysis-m2-drop-runtime-from-key). The interpreter is the
-- corpus's implicit and only oracle, so an ordinary corpus @.tst@ names no
-- backends; a program listed here is the exception, and its file's
-- @backends:@ line names the text backends its rows run on instead
-- ('headerBackendsTests' holds the two together). The -O0 group's own
-- exemptions ('unoptimizedRecompileExempt') are a separate matter: they
-- concern the optimizer differential, not whether the interpreter can answer.
--
-- Empty as measured 2026-10-09 and at the migration (2026-10-13): the
-- interpreter answers every row of every corpus program at -O2. An entry here
-- must be a program the interpreter genuinely cannot answer, with its ticket.
interpreterServesExempt :: [(String, String)]
interpreterServesExempt = []

-- | The ordinary corpus names no backends (impact analysis M2): a @.tst@ file
-- carries a @backends:@ line exactly when its program is in
-- 'interpreterServesExempt', and that line leaves the interpreter out.
-- (@batched@, @dense@ and @slow@ are standalone header lines.)
headerBackendsTests :: [CorpusEntry] -> TestTree
headerBackendsTests es = testProperty "a .tst names backends only for a program the interpreter cannot serve" $ once $ ioProperty $ do
  withLine <- fmap concat $ forM es $ \e -> do
    src <- readFile (ceTst e)
    return [ ceName e | any ("backends:" `isPrefixOf`) (lines src) ]
  let exempt = map fst interpreterServesExempt
      unlisted = filter (`notElem` exempt) withLine
      lineless = [ n | n <- exempt, n `elem` map ceName es, n `notElem` withLine ]
      routed = [ ceName e | e <- es, ceName e `elem` exempt, Interpreter `elem` ceBackends e ]
  return $ conjoin
    [ counterexample ("a `backends:` line on a program the interpreter serves (drop the line; the interpreter is implicit): " ++ show unlisted) (null unlisted)
    , counterexample ("interpreterServesExempt programs without a `backends:` line: " ++ show lineless) (null lineless)
    , counterexample ("interpreterServesExempt programs whose `backends:` line names the interpreter: " ++ show routed) (null routed) ]

-- | Programs whose -O0 recompilation is disproportionately expensive relative
-- to the regression class the "Interpreter Unoptimized" group exists to catch
-- (the optimizer changing an answer). 'recursiveAdtMultiCtor' pairs an
-- unbounded self-recursive ADT with several deep ANY-marginal queries; without
-- CSE (there is none at -O0) the interpreter re-walks the shared recursive
-- structure once per partial-match world, costing ~9s alone -- as much as the
-- other ~245 programs in the group combined. Its -O2 (default) Interpreter,
-- Julia and Python coverage is untouched; only the O0 differential is skipped
-- for it, and only here -- the same program still anchors the fast group's
-- recursive-ADT/ANY-marginal coverage.
--
-- 'wideProductSceneCount' is a ten-slot product scene read by one network
-- (task batched-compile-ooms-on-wide-product-scene). At -O2 its tail rows
-- answer in well under a second; at -O0 one query grows about 5x per slot
-- (0.08s at 2 slots, 6.5s at 5), so ten slots would take hours. The entry
-- exists for its batched compile and its -O2 answers on the scalar
-- backends; the -O0 cost is a separate interpreter defect, not the optimizer
-- changing an answer (task unoptimized-interpreter-exponential-in-scene-slots).
unoptimizedRecompileExempt :: [String]
unoptimizedRecompileExempt = ["recursiveAdtMultiCtor", "wideProductSceneCount"]

-- | Programs the -O0 *codegen* groups could not run, for a defect that was
-- not the optimizer changing an answer but the optimizer being required to
-- produce a well-formed call at all.
--
-- 'toIRInference' used to compile @Apply@ by let-binding each step of a
-- curried application spine (@let c0 = f(sample) in let c1 = c0(5.0) in ...@),
-- while the scalar backends emit a user function uncurried and flatten a
-- *contiguous* spine into one @f(sample, 5.0)@ call site. At the default -O
-- the let-inliner rejoined the spine before codegen saw it; at -O0 nothing
-- did, so each half was emitted as its own call and Julia answered
-- @MethodError: no method matching distr_prob(::Float64)@ -- an arity error,
-- not a wrong number. It was the same "the optimizer is load-bearing" family
-- as investigation 'any-placeholder-reconstruction-fragility', tracked
-- separately by task 'curried-call-spine-needs-optimizer-to-typecheck'.
--
-- Fixed at the root (that task's direction 2): a dedicated 'toIRInference'
-- equation now recognizes a curried spine whose head is a known top-level
-- function and every argument is Deterministic, and builds the whole
-- application -- the query sample plus every source-level argument -- as one
-- contiguous 'IRApply' chain, let-bound exactly once, instead of one
-- 'IRApply'/'let' pair per source-level argument. The spine is then
-- contiguous at every -O level, not just after the let-inliner runs, so the
-- backends' existing flattening (@f(sample, 5.0)@) sees it whether or not the
-- optimizer ran. This list is empty and kept only as the hook the acceptance
-- criterion (an empty list, the group green with these three restored) names.
unoptimizedCodegenExempt :: [String]
unoptimizedCodegenExempt = []

-- | The corpus subset the -O0 *codegen* groups run, on both text backends.
--
-- Deliberately a smoke test rather than the whole corpus. The full sweep was
-- run once while investigation 'any-placeholder-reconstruction-fragility' was
-- open and is worth recording: every -O0 program bar the three in
-- 'unoptimizedCodegenExempt' agrees with its .tst. But it costs ~147s of Julia
-- JIT (the -O0 sources are big and there are ~250 of them), against 89s for
-- the entire rest of the suite, and it re-confirms one already-known class.
--
-- These are the programs whose inference reconstructs a container around an
-- any-hole -- list, tuple, Either and ADT-field shapes -- which is where the
-- placeholders live, so this is the coverage the fix actually needs. Widening
-- it is fine; it is a runtime budget, not a correctness boundary.
--
-- Both backends run the same list, but for different failure modes. Julia is
-- where an ill-typed placeholder is fatal: 'prepend' takes an InferenceList,
-- so the scalar hole was a MethodError. Python is dynamically typed and
-- quietly coerced the same value, so what it adds is the codegen-side class --
-- a placeholder no 'pyVal' case can render aborts the compile outright.
unoptimizedCodegenSmoke :: [String]
unoptimizedCodegenSmoke =
  [ "head", "tail", "fst", "sndCall"
  , "listConsDeconstruction", "listLiteralDeconstruction"
  , "either_prob_inner", "eitherIntegral", "letBoundEitherDestructure"
  , "maybeFromLeftNested"
  , "adt", "adtMixedFieldTypes", "adtMixedArityCtors", "adtFloatChainDeep" ]

-- | Builds the standard End2End sweeps over the corpus programs the
-- 'SlowHeader' policy admits, under the group @treeName@ (whose path in the
-- tree is @path@). includeBackends controls whether the Normalization/Julia/
-- Python sweeps are built (skipped for the slow subset, whose programs are
-- Interpreter-only by design).
--
-- Each program is compiled once at -O2 and, where needed, once at -O0; the
-- compiles are shared by every sweep below ('optEnvs', 'unoptEnvs').
buildEnd2EndTree :: Corpus -> Manifest -> String -> String -> Tier -> SlowHeader -> Bool -> IO TestTree
buildEnd2EndTree corpus manifest path treeName tier slowH includeBackends = do
  -- The M2 census of every program the text-backend sweeps may select (see
  -- 'textRouted'): six compiles beyond the shared -O2 and -O0 ones, about a
  -- second each over the default corpus, so spread over the capabilities.
  censuses <- if not includeBackends then return Map.empty else
    Map.fromList <$> parMapIO programUncertified [ e | e <- entries, not (ceSlow e) ]
  interp <- corpusSweep corpus SweepSpec
    { sweepName = path ++ ".Interpreter", sweepTier = tier, sweepSlow = slowH
    , sweepSelect = interpreterRouted
    , sweepNote = "every .tst row against the interpreter, at -O2" } $ \e ->
      let n = ceName e; p = ceProgram e; c = opt e; tcs = rows e
      in testProperty n (once $ cachedProperty manifest (check "Interpreter") n (interpreterKey manifest p c tcs)
                                  (conjoin (map (testInterpreter p c) tcs)))
  -- Re-run every interpreter case at -O0 to confirm the optimizer changes no answer.
  interpUnopt <- corpusSweep corpus SweepSpec
    { sweepName = path ++ ".Interpreter Unoptimized", sweepTier = tier, sweepSlow = slowH
    , sweepSelect = \e -> interpreterRouted e && recompiledUnopt e
    , sweepNote = "every .tst row against the interpreter at -O0: the optimizer changes no answer" } $ \e ->
      let n = ceName e; p = ceProgram e; c = unopt e; tcs = rows e
      in testProperty n (once $ cachedProperty manifest (check "Interpreter Unoptimized") n (interpreterKey manifest p c tcs)
                                  (conjoin (map (testInterpreter p c) tcs)))
  backends <- if not includeBackends then return [] else sequence
    [ corpusSweep corpus SweepSpec
        { sweepName = path ++ ".Normalization", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = \e -> interpreterRouted e && neural e && not (ceNoNormalization e)
        , sweepNote = "a neural program's discrete probabilities sum to one at seeded inputs" } $ \e ->
          let n = ceName e; p = ceProgram e; c = opt e
          in testProperty n (once $ cachedProperty manifest (check "Normalization") n (normalizationKey manifest p c)
                                      (discreteProbsNormalized p c))
    -- The Julia programs share a batch file (and a julia process) per
    -- shard to amortize startup. One shard for the whole corpus was a
    -- single ~60 s test -- the suite's critical path, on one core --
    -- since the batch is dominated by JIT-compiling each module.
    -- Round-robin shards run as parallel tests instead.
    , corpusSweepAll corpus SweepSpec
        { sweepName = path ++ ".Julia", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = \e -> textRouted censuses Julia e && hasQueries e
        , sweepNote = "every p()/cdf() row against the emitted Julia, in round-robin shards, of a program the fuzzers do not certify" } $ \es ->
          return $ testGroup "Julia"
            [ testProperty ("shard " ++ show (i + 1) ++ "/" ++ show juliaShards)
                (once $ cachedBatch manifest (check "Julia")
                          [ (n, juliaKey manifest c tcs nets, (c, tcs, nets))
                          | (k, (n, c, tcs, nets)) <- zip [0 :: Int ..] (map routedQuery es)
                          , k `mod` juliaShards == i ]
                          testJuliaAll)
            | i <- [0 .. juliaShards - 1] ]
    -- "Julia free names are escaped" is not here: it is
    -- 'juliaFreeNamesTests', in Slow.
    , corpusSweep corpus SweepSpec
        { sweepName = path ++ ".Python", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = \e -> textRouted censuses Python e && hasQueries e
        , sweepNote = "every p()/cdf() row against the emitted Python, of a program the fuzzers do not certify" } $ \e ->
          let (n, c, tcs, nets) = routedQuery e
          in testProperty n (once $ cachedProperty manifest (check "Python") n (pythonKey manifest nets c tcs)
                                      (testPython nets c tcs))
    -- writeLogits rows used to run on the interpreter only, which is how
    -- every text-backend writeLogits but a flat discrete one shipped
    -- crashing (task writelogits-text-backends-broken).
    , corpusSweep corpus SweepSpec
        { sweepName = path ++ ".Python WriteLogits", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = \e -> textRouted censuses Python e && hasWriteLogits e
        , sweepNote = "every writeLogits row against the emitted Python, of a program the fuzzers do not certify" } $ \e ->
          let n = ceName e; nets = networkMocks (ceProgram e); c = opt e; wl = writeLogitsRows e
          in testProperty n (once $ cachedProperty manifest (check "Python WriteLogits") n (pythonWriteLogitsKey manifest nets c wl)
                                      (testPythonWriteLogits nets c wl))
    , corpusSweepAll corpus SweepSpec
        { sweepName = path ++ ".Julia WriteLogits", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = \e -> textRouted censuses Julia e && hasWriteLogits e
        , sweepNote = "every writeLogits row against the emitted Julia, in one batch, of a program the fuzzers do not certify" } $ \es ->
          return $ testProperty "Julia WriteLogits"
            (once $ cachedBatch manifest (check "Julia WriteLogits")
                      [ (ceName e, juliaWriteLogitsKey manifest c wl nets, (c, wl, nets))
                      | e <- es, let c = opt e, let wl = writeLogitsRows e, let nets = networkMocks (ceProgram e) ]
                      testJuliaWriteLogitsAll)
    -- The same corpus through the text backends at -O0. See 'unoptEnvs' for
    -- why this is not merely a duplicate of the optimized groups. None of
    -- 'unoptimizedCodegenSmoke' is neural, so this stays on the plain
    -- (non-mock-resolved) test cases.
    , corpusSweepAll corpus SweepSpec
        { sweepName = path ++ ".Julia Unoptimized", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = unoptSmoke
        , sweepNote = "the -O0 codegen smoke subset against the emitted Julia" } $ \es ->
          return $ testProperty "Julia Unoptimized"
            (once $ cachedBatch manifest (check "Julia Unoptimized")
                      [ (ceName e, juliaKey manifest (unopt e) (queries e) [], (unopt e, queries e, [])) | e <- es ]
                      testJuliaAll)
    , corpusSweep corpus SweepSpec
        { sweepName = path ++ ".Python Unoptimized", sweepTier = tier, sweepSlow = slowH
        , sweepSelect = unoptSmoke
        , sweepNote = "the -O0 codegen smoke subset against the emitted Python" } $ \e ->
          let n = ceName e
          in testProperty n (once $ cachedProperty manifest (check "Python Unoptimized") n (pythonKey manifest [] (unopt e) (queries e))
                                      (testPython [] (unopt e) (queries e)))
    ]
  let headers = [ headerBackendsTests entries | includeBackends ]
  return $ testGroup treeName ([interp, interpUnopt] ++ headers ++ backends)
  where
    -- The manifest slot prefix: the sweep's full group name.
    check grp = treeName ++ "." ++ grp
    entries = corpusEntries corpus
    -- Every corpus program compiled at -O2, shared by all the sweeps.
    optEnvs = Map.fromList [ (ceName e, compile defaultCompilerConfig (ceProgram e)) | e <- entries ]
    -- Every corpus program recompiled at -O0, shared by all the "Unoptimized"
    -- sweeps so the extra compile is paid once.
    --
    -- The optimizer is meant to be a rewrite, not a correctness pass, and the
    -- text backends are where that claim is testable: a value the optimizer
    -- would have folded away survives to codegen at -O0 and is evaluated for
    -- real. Investigation \'any-placeholder-reconstruction-fragility\' is the
    -- worked example -- \'head\'/\'tail\'/\'fst\'/\'snd\' inference reconstructs a
    -- container around a placeholder purely to tear it apart again, and while
    -- the fold at oLvl >= 1 cancelled the round trip, at -O0 the placeholder
    -- reached Julia and every such program died with a MethodError. The
    -- interpreter never saw it (it is dynamically typed and forgiving), so the
    -- pre-existing "Interpreter Unoptimized" group could not catch the class.
    unoptEnvs = Map.fromList [ (ceName e, compile defaultCompilerConfig{optimizerLevel = 0} (ceProgram e)) | e <- entries ]
    -- The compiles the text backends run (-O2 and -O0, shared with the
    -- sweeps); not one per config (IR fuzz generator M5). A compile that raises
    -- leaves the program uncertified: its text-backend checks then run, and
    -- report it.
    programUncertified e = do
      let census = uncertifiedConstructs (programCensus [opt e, unopt e])
      r <- try (evaluate (length (concat census) `seq` census))
      return (ceName e, either (\ex -> ["(census raised: " ++ takeWhile (/= '\n') (show (ex :: SomeException)) ++ ")"]) id r)
    shaped = Map.fromList [ (ceName e, shapedCases e) | e <- entries ]
    opt e = optEnvs Map.! ceName e
    unopt e = unoptEnvs Map.! ceName e
    rows e = shaped Map.! ceName e
    recompiledUnopt e = ceName e `notElem` unoptimizedRecompileExempt
    neural e = not (null (neurals (ceProgram e)))
    -- Impact analysis M2 (docs-repo task impact-analysis-m2-drop-runtime-from-key):
    -- the interpreter is the corpus's oracle, and a program's rows run on
    -- the scalar Python and Julia backends only when its census leaves what
    -- the agreement fuzzers certify ('CertifiedCensus'), or when its header
    -- names those backends because the interpreter cannot serve it
    -- ('interpreterServesExempt'). Either way the check is keyed with the
    -- runtime fingerprint, as under M1.
    textRouted cs b e = (not (interpreterRouted e) && b `elem` ceBackends e) || not (null (uncertified cs e))
    -- No census means not certified (only the slow programs have none, and
    -- the text-backend sweeps skip those before asking).
    uncertified cs e = Map.findWithDefault ["(no census)"] (ceName e) cs
    isQuery x = isProbTestCase x || isCumulTestCase x
    queries e = filter isQuery (rows e)
    hasQueries e = any isQuery (ceCases e)
    wlRows e = filter (\x -> isWriteLogitsLengthTestCase x || isWriteLogitsSlotTestCase x) (rows e)
    hasWriteLogits e = any (\x -> isWriteLogitsLengthTestCase x || isWriteLogitsSlotTestCase x) (ceCases e)
    writeLogitsRows e = map (writeLogitsRow (ceProgram e)) (wlRows e)
    -- A query program routes onto every backend it lists, neural or
    -- not. The @null (neurals p)@ filter that used to stand here
    -- existed only because neither text backend has a network to call
    -- at runtime, not because the routing was otherwise unsound (task
    -- route-neural-programs-to-julia-python-backends dropped it for
    -- Python, route-neural-programs-to-julia-backend for Julia). Once
    -- an identity mock is installed for each declared network
    -- ('testPython', 'juliaBatchTestCode') and the .tst row's own
    -- mock-NN parameters are pre-resolved to the raw vectors that mock
    -- would have produced ('resolveNeuralTestCase'), a neural program
    -- is just another program. The Julia flip was a routing-only
    -- change: the mock plumbing had been built for both backends at
    -- once, and adding @julia@ to the five .tst headers that still
    -- listed @interpreter, python, batched@ was the rest of it. Every
    -- newly-routed program agreed with the interpreter on the first
    -- run, mode-0 seeded envelopes included.
    --
    -- 'unoptSmoke' below still filters neural out, and deliberately:
    -- it is scoped to 'unoptimizedCodegenSmoke', none of which is
    -- neural.
    routedQuery e =
      let p = ceProgram e
      in (ceName e, opt e, if null (neurals p) then queries e else map (resolveNeuralTestCase p) (queries e), networkMocks p)
    -- Not gated on the census (M2): the class this smoke exists for, a
    -- placeholder of the wrong type reaching a backend at -O0, is a typing
    -- fact about the IR that a construct census cannot see. It stays on both
    -- text backends, keyed with their runtimes.
    unoptSmoke e = recompiledUnopt e && not (neural e)
                     && ceName e `elem` unoptimizedCodegenSmoke
                     && ceName e `notElem` unoptimizedCodegenExempt
                     && hasQueries e

-- ===========================================================================
-- Runtime topK cutoff (task runtime-parametric-topk-threshold)
-- ===========================================================================

-- | The topK cutoff is a runtime parameter of every compiled probability and
-- integrate function, so ONE topK compile answers every threshold. Pinned three
-- ways on fixtures where the threshold bites (pruning flips the answer between
-- 0 and 0.1): the interpreter on a re-thresholded compile ('withTopKCutoff')
-- reproduces a dedicated compile at that threshold exactly, in linear and log
-- space; and the emitted Python and Julia, compiled once, answer each cutoff
-- passed at call time as the dedicated compile does.
topKRuntimeCutoffTests :: TestTree
topKRuntimeCutoffTests = testGroup "topK runtime cutoff"
  [ testProperty "a re-thresholded compile matches a dedicated compile (interpreter)" $ once $
      conjoin [ rethresholdAgrees logS src t q
              | (_, src) <- fixtures, logS <- [False, True], t <- cutoffs, q <- queries ]
  , testProperty "the fixtures are not vacuous: thresholds 0 and 0.1 disagree" $ once $
      conjoin [ counterexample (name ++ ": " ++ show (at 0.0) ++ " == " ++ show (at 0.1)) (show (at 0.0) /= show (at 0.1))
              | (name, src) <- fixtures
              , let at t = dedicated False src t (False, VFloat 1.0) ]
  , testProperty "emitted Python takes the cutoff at call time" $ once $ ioProperty $ do
      mpy <- findTorchPython
      case mpy of
        Nothing -> noTorchProperty "topK runtime cutoff (Python)"
        Just py -> do
          cwd <- getCurrentDirectory
          conjoin <$> mapM (pythonFixture py cwd) fixtures
  , testProperty "emitted Julia takes the cutoff at call time" $ once $ ioProperty $ do
      projectDir <- getCurrentDirectory
      conjoin <$> mapM (juliaFixture projectDir) fixtures
  ]
  where
    -- A pruned mass arm at the root, and the same arm behind a call, so the
    -- cutoff has to be forwarded through 'inferenceCall' too.
    fixtures =
      [ ("root", "main = if Uniform < 0.05 then 1.0 else Uniform")
      , ("call", "f x = if Uniform < 0.05 then x else Uniform\nmain = f 1.0") ]
    cutoffs = [0.0, 0.03, 0.1, 0.5]
    -- (cumulative?, sample)
    queries = [ (c, VFloat x) | c <- [False, True], x <- [1.0, 0.5] ]
    parse src = either (error . show) id (tryParseProgram "" src)
    conf logS t = defaultCompilerConfig { topKThreshold = Just t, logSpace = logS }
    run p env (cumul, x) = either (error . show) id
      ((if cumul then runIntegC else runProbC) p env [] x)
    dedicated logS src t q =
      let p = parse src in run p (either (error . show) id (compile (conf logS t) p)) q
    -- compiled once at a threshold matching none of 'cutoffs'
    shared logS src = either (error . show) id (compile (conf logS 0.07) (parse src))
    rethresholdAgrees logS src t q =
      let got = run (parse src) (withTopKCutoff t (shared logS src)) q
          want = dedicated logS src t q
      in counterexample (src ++ " logSpace=" ++ show logS ++ " t=" ++ show t ++ " " ++ show q
                         ++ ": " ++ show got ++ " /= " ++ show want) (show got == show want)
    expected src = [ (t, q, pd (dedicated False src t q)) | t <- cutoffs, q <- queries ]
    pd v = case v of
      VProbDim p d -> (p, d)
      other        -> error ("unexpected result " ++ show other)
    compare1 name out src = case map (map read . words) (lines out) :: [[Double]] of
      rows | length rows == length (expected src) ->
        conjoin [ counterexample (name ++ " t=" ++ show t ++ " " ++ show q ++ ": got " ++ show [gp, gd]
                                  ++ ", want " ++ show (p, d))
                    (abs (gp - p) <= probTolerance && gd == fromIntegral d)
                | ((t, q, (p, d)), [gp, gd]) <- zip (expected src) rows ]
      _ -> counterexample (name ++ ": unexpected output\n" ++ out) False
    pythonFixture py cwd (name, src) = do
      let env = shared False src
          code = unlines (SPLL.CodeGenPyTorch.generateFunctions True env)
          call t (cumul, x) = if cumul
            then "main.integrate(" ++ pyVal x ++ ", " ++ pyVal (VFloat t) ++ ")"
            else "main.forward(" ++ pyVal x ++ ", ACC_PROB_INIT, " ++ pyVal (VFloat t) ++ ")"
          script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ code ++ "\n"
            ++ unlines [ "r = " ++ call t q ++ "\nprint(float(r[0]), float(r[1][0]))" | (t, q, _) <- expected src ]
      (ec, out, err) <- withSystemTempFile "topk_cutoff.py" $ \tmpPath h -> do
        hPutStr h script >> hClose h
        readProcessWithExitCode py [tmpPath] ""
      return $ case ec of
        ExitSuccess -> compare1 ("python " ++ name) out src
        ExitFailure _ -> counterexample ("python " ++ name ++ " failed:\n" ++ out ++ err) False
    juliaFixture projectDir (name, src) = do
      let env = shared False src
          code = intercalate "\n" (SPLL.CodeGenJulia.generateFunctions env)
          call t (cumul, x) = if cumul
            then "P.main_integ(" ++ juliaVal x ++ ", " ++ juliaVal (VFloat t) ++ ")"
            else "P.main_prob(" ++ juliaVal x ++ ", P.ACC_PROB_INIT, " ++ juliaVal (VFloat t) ++ ")"
          script = "include(\"" ++ projectDir ++ "/juliaLib.jl\")\nusing .JuliaSPPLLib\n"
            ++ "module P\nusing ..JuliaSPPLLib\n" ++ code ++ "\nend\n"
            ++ unlines [ "r = " ++ call t q ++ "\nprintln(Float64(r[1]), \" \", Float64(r[2][1]))" | (t, q, _) <- expected src ]
      (ec, out, err) <- withSystemTempFile "topk_cutoff.jl" $ \tmpPath h -> do
        hPutStr h script >> hClose h
        readProcessWithExitCode "julia" (juliaTestFlags ++ [tmpPath]) ""
      return $ case ec of
        ExitSuccess -> compare1 ("julia " ++ name) out src
        ExitFailure _ -> counterexample ("julia " ++ name ++ " failed:\n" ++ out ++ err) False
