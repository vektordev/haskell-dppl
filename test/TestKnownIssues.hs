{-# LANGUAGE PatternSynonyms #-}
-- | Drives @test/cases/known-issues/@ (design testcases-corpus-restructure):
-- a folder of @.ppl@/@.tst@ pairs pinned to a *specific*, known compiler bug,
-- each carrying an @expect-failure:@ header naming the shape it demonstrates
-- (see 'TestCaseParser.ExpectFailure'). Unlike the rest of the corpus (whose
-- programs are all expected to compile and run correctly), every program here
-- is expected to keep failing exactly as documented -- so the suite fails
-- loudly, not silently, the day the underlying bug gets fixed and a case here
-- needs to move out (to the ordinary corpus, or to "TestRejection" if the fix
-- turned it into a deliberate, graceful refusal).
--
-- This folder is deliberately excluded from 'TestCaseParser.listCorpusPplFiles'
-- (and so from every ordinary corpus sweep -- End2End, the batched groups,
-- the @Corpus@ metamorphic properties, ...), since those all assume a program
-- compiles; a known issue by definition does not.
--
-- Coexists with "TestRejection" rather than replacing it: a bespoke,
-- multi-assertion regression (e.g. one that also checks a *different* variant
-- is unaffected) stays a hand-written HUnit group there. This module is for
-- the common single-diagnostic shape only, filed by dropping in a program
-- instead of writing new Haskell.
module TestKnownIssues (knownIssuesTests, performancePinHarnessTests) where

import Control.Exception (AllocationLimitExceeded(..), SomeException, evaluate, finally, fromException, try)
import Data.IORef (modifyIORef, newIORef, readIORef)
import GHC.Clock (getMonotonicTime)
import System.Mem (disableAllocationLimit, enableAllocationLimit, getAllocationCounter, setAllocationCounter)
import System.Timeout (timeout)
import Text.Megaparsec (errorBundlePretty)
import Control.Monad (filterM)
import Data.List (foldl', intercalate, isInfixOf)
import Data.Maybe (isNothing)
import System.Directory (doesDirectoryExist, getCurrentDirectory, listDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), isExtensionOf, takeBaseName)
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertBool, assertEqual, assertFailure)

import SPLL.Lang.Types (CompilerError, Program, GenericValue(..))
import SPLL.IntermediateRepresentation
  ( IREnv(..), IRValue, CompilerConfig, defaultCompilerConfig, lookupIREnv
  , IRFunGroup(..), showRefusal
  , resultImpossible, pattern VProbDim
  )
import SPLL.Prelude (compile, runProbC, runIntegC)
import SPLL.Parser (tryParseProgram)
import SPLL.CodeGenPyTorch (generateFunctions)
import TestCaseParser
  ( Backend(..), ExpectFailure(..), TestCase(..), Expectation(..), corpusRoot
  , GrowthSpec(..), GrowthMetric(..), PointCap(..), CompileFlag(..), applyCompileFlags
  , defaultBackends, defaultPointCap
  , parseProgram, parseTestCasesFromString
  )
import ScalingCheck (Point(..), Verdict(..), climb, expandTemplate)
import TestTolerances (probTolerance)
import End2EndTesting (networkMocks, pythonTestScript, resolveNeuralTestCase, shapeNeuralTestCase)

knownIssuesDir :: FilePath
knownIssuesDir = corpusRoot </> "known-issues"

-- | Every known-issues base name, found by a flat listing (unlike the rest of
-- the corpus, this folder is not itself subdivided into topics).
knownIssueBaseNames :: IO [String]
knownIssueBaseNames = do
  exists <- doesDirectoryExist knownIssuesDir
  if not exists
    then return []
    else do
      entries <- listDirectory knownIssuesDir
      return [ takeBaseName e | e <- entries, ".ppl" `isExtensionOf` e ]

knownIssuesTests :: IO TestTree
knownIssuesTests = do
  names <- knownIssueBaseNames
  -- A `slow`-headered pin runs only under NEST_SLOW_TESTS, like the slow
  -- programs of the ordinary corpus. The header is read here, while the tree
  -- is built, so a skipped pin is absent rather than a passing no-op.
  runSlow <- maybe False (const True) <$> lookupEnv "NEST_SLOW_TESTS"
  kept <- filterM (\n -> (runSlow ||) . not <$> isSlow n) names
  return $ testGroup "KnownIssues" (map knownIssueTest kept)
  where
    isSlow n = do
      let tstPath = knownIssuesDir </> (n ++ ".tst")
      src <- readFile tstPath
      (_, slow, _, _) <- either error return (parseTestCasesFromString tstPath src)
      length src `seq` return slow

knownIssueTest :: String -> TestTree
knownIssueTest baseName = testCaseInfo baseName $ do
  let pplPath = knownIssuesDir </> (baseName ++ ".ppl")
      tstPath = knownIssuesDir </> (baseName ++ ".tst")
  tstSrc <- readFile tstPath
  (backends, _, mEf, tcs) <- either error return (parseTestCasesFromString tstPath tstSrc)
  case mEf of
    Nothing -> assertFailure (tstPath ++ " is a known-issues .tst but declares no \
                              \`expect-failure:` header -- every case here must name \
                              \which shape it pins")
    -- A growth pin's .ppl is a template, parsed once per knob value.
    Just (ExpectGrowthAbove spec) -> readFile pplPath >>= checkGrowthAbove baseName pplPath spec
    Just ef@ExpectCodeSizeAbove{} -> do
      prog <- parseProgram pplPath
      checkCodeSizeAbove baseName prog ef
    Just ef -> do
      prog <- parseProgram pplPath
      checkExpectFailure baseName prog backends ef tcs
      return ""

checkExpectFailure :: String -> Program -> [Backend] -> ExpectFailure -> [TestCase] -> IO ()
checkExpectFailure name _ _ ExpectGrowthAbove{} _ =
  assertFailure (name ++ ": internal: a growth pin is checked from its template, not a parsed program")
checkExpectFailure name _ _ ExpectCodeSizeAbove{} _ =
  assertFailure (name ++ ": internal: a code-size pin is checked by checkCodeSizeAbove")
checkExpectFailure name prog _ ExpectCrash _ =
  assertCrashes name (compile defaultCompilerConfig prog) Nothing
checkExpectFailure name prog _ (ExpectDiagnostic needle) _ =
  assertCrashes name (compile defaultCompilerConfig prog) (Just needle)
checkExpectFailure name prog _ (ExpectRefused needle) _ = do
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left ex -> assertFailure (name ++ ": expected a refused variant, but compile crashed: " ++ show ex)
    Right _ -> case compile defaultCompilerConfig prog of
      Left err -> assertFailure (name ++ ": expected a refused variant, but the compile was \
                                 \refused outright: " ++ err)
      Right env ->
        let reasons = [ groupName g ++ "." ++ lbl ++ ": " ++ showRefusal r
                      | g <- envGroups env, (lbl, r) <- refusedVariants g ]
        in assertBool (name ++ ": expected a variant refused with a reason containing \""
                       ++ needle ++ "\", but the recorded refusals are: "
                       ++ (if null reasons then "(none) -- the bug it pins may be fixed; if so, \
                                                \move or retire this known-issues case"
                           else intercalate "\n" reasons))
             (any (needle `isInfixOf`) reasons)
  where envGroups (IREnv gs _ _) = gs
checkExpectFailure name prog _ ExpectNoCode _ = do
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left ex -> assertFailure (name ++ ": expected compile to succeed with a silently absent \
                              \variant, but it crashed instead: " ++ show ex)
    Right _ -> case compile defaultCompilerConfig prog of
      Left err -> assertFailure (name ++ ": expected compile to succeed with a silently \
                                 \absent variant, but it was refused outright: " ++ err)
      Right env ->
        let m = lookupIREnv "main" env
        in assertBool (name ++ ": expected at least one of generate/probability/integrate \
                       \to be silently absent, but main compiled all three")
             (isNothing (genFun m) || isNothing (probFun m) || isNothing (integFun m))
-- The rows below the header pin the (known-wrong) value the compiled program
-- produces today, on every backend the @backends:@ header declares that this
-- harness can evaluate (see 'checkableBackends'). Each row must still match:
-- a fix changes the number and fails the pin, and so does the wrong value
-- drifting. A compile that crashes or is refused, a query that crashes or is
-- refused, and a non-prob/dim result all fail too -- the pin documents a
-- program that compiles and answers, just wrongly.
checkExpectFailure name prog backends ExpectWrongResult tcs = do
  checked <- requireCheckable "wrong-result" name backends
  let rows = queryRows tcs
  if null rows
    then assertFailure (name ++ ": an `expect-failure: wrong-result` pin has no p()/cdf() rows, \
                        \so nothing pins the wrong value")
    else do
      result <- forced (compile defaultCompilerConfig prog)
      case result of
        Left ex -> assertFailure (name ++ ": expected a wrong-result pin to compile, but the \
                                  \compile crashed: " ++ show ex)
        Right _ -> case compile defaultCompilerConfig prog of
          Left err -> assertFailure (name ++ ": expected a wrong-result pin to compile, but it \
                                     \was refused outright: " ++ err)
          Right env -> mapM_ (\b -> mapM_ (assertStillWrong b name prog env) rows) checked
-- The mechanism is unpinned: the rows below state the *idealized* value, and
-- the case passes as long as the compiled program does not yet produce it
-- on any backend the @backends:@ header declares (read exactly as the rest
-- of the corpus reads it: no header means the three scalar backends). The
-- header names where the bug is pinned, so a Python-only bug is spelled
-- @backends: python@ and is not reported "may be fixed" merely because the
-- interpreter already gets it right.
checkExpectFailure name prog backends ExpectBroken tcs = do
  checked <- requireCheckable "broken" name backends
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left _ -> return ()      -- crashed at compile time: still broken everywhere
    Right _ -> case compile defaultCompilerConfig prog of
      Left _ -> return ()    -- refused outright: still broken everywhere
      Right env -> mapM_ (\b -> mapM_ (assertStillBroken b name prog env) (queryRows tcs)) checked

-- | The backends a @broken@ or @wrong-result@ pin's rows can be run against
-- here: the interpreter in-process, and the Python backend through the same
-- emitted script End2End runs. Julia is not (it is not installed everywhere
-- the suite runs, and a missing binary would read as "still broken", i.e. a
-- silently green pin), nor are batched/dense. A pin declaring only those
-- fails loudly instead of passing vacuously.
checkableBackends :: [Backend]
checkableBackends = [Interpreter, Python]

-- | The declared backends this harness can evaluate, failing the pin when
-- there are none (it would otherwise pass without checking anything).
requireCheckable :: String -> String -> [Backend] -> IO [Backend]
requireCheckable shape name backends = do
  let checked = filter (`elem` checkableBackends) backends
  if null checked
    then assertFailure (name ++ ": an `expect-failure: " ++ shape ++ "` pin must declare at \
                        \least one backend the known-issues harness can evaluate (" ++
                        intercalate ", " (map show checkableBackends) ++
                        "); declared only " ++ intercalate ", " (map show backends) ++
                        ", so its rows would never be checked")
    else return checked

-- | The p()/cdf() rows: both checks only cover the two ordinary probability
-- query shapes, so anything else (argmax_p, writeLogits) is left unchecked.
queryRows :: [TestCase] -> [TestCase]
queryRows = filter isQuery
  where
    isQuery ProbTestCase{}  = True
    isQuery CumulTestCase{} = True
    isQuery _               = False

-- | One idealized row on one backend: assert the result does not yet match
-- the documented-correct value. A crash (at codegen, module load, or run
-- time), a refused query, or a non-prob/dim result are all still "broken";
-- only an exact (within-tolerance) match to the idealized row counts as "may
-- be fixed now".
assertStillBroken :: Backend -> String -> Program -> IREnv -> TestCase -> IO ()
assertStillBroken Interpreter name prog env (ProbTestCase caseName sample params expct) =
  checkStillBroken name caseName expct (runProbC prog env params sample)
assertStillBroken Interpreter name prog env (CumulTestCase caseName sample params expct) =
  checkStillBroken name caseName expct (runIntegC prog env params sample)
assertStillBroken Python name prog env tc = do
  matched <- pythonRowMatches prog env tc
  assertBool
    (name ++ "/" ++ rowName tc ++ " [python]: the Python backend now matches the documented \
             \idealized value -- this known issue may be fixed; if so, tighten or move this \
             \case out of known-issues")
    (not matched)
assertStillBroken _ _ _ _ _ = return ()

-- | One pinned (wrong) row on one backend: assert the result still matches
-- it. Anything else -- a different value, a crash, a refused query, a
-- non-prob/dim result -- means the bug moved or was fixed.
assertStillWrong :: Backend -> String -> Program -> IREnv -> TestCase -> IO ()
assertStillWrong Interpreter name prog env (ProbTestCase caseName sample params expct) =
  checkStillWrong name caseName expct (runProbC prog env params sample)
assertStillWrong Interpreter name prog env (CumulTestCase caseName sample params expct) =
  checkStillWrong name caseName expct (runIntegC prog env params sample)
assertStillWrong Python name prog env tc = do
  matched <- pythonRowMatches prog env tc
  assertBool
    (name ++ "/" ++ rowName tc ++ " [python]: no longer produces the pinned wrong value \
             \(or failed to load/run) -- the bug may be fixed or may have moved; triage \
             \this known-issues case (move it to the corpus if fixed, re-pin if the wrong \
             \value changed)")
    matched
assertStillWrong _ _ _ _ _ = return ()

checkStillWrong :: String -> String -> Expectation -> Either CompilerError IRValue -> IO ()
checkStillWrong name caseName expct er = do
  r <- try (evaluate (length (show er)) >> return er)
         :: IO (Either SomeException (Either CompilerError IRValue))
  let here = name ++ "/" ++ caseName ++ " [interpreter]: "
      triage = " -- the bug may be fixed or may have moved; triage this known-issues case \
               \(move it to the corpus if fixed, re-pin if the wrong value changed)"
  case r of
    Left ex -> assertFailure (here ++ "the query crashed instead of producing the pinned \
                                      \wrong value: " ++ show ex ++ triage)
    Right (Left err) -> assertFailure (here ++ "the query was refused instead of producing \
                                               \the pinned wrong value: " ++ err ++ triage)
    Right (Right res@(VProbDim outProb outDim)) ->
      assertBool (here ++ "got " ++ show res ++ ", not the pinned wrong value " ++ show expct ++ triage)
        (matchesExpectation expct outProb outDim res)
    Right (Right res) -> assertFailure (here ++ "got a non-prob/dim result " ++ show res ++ triage)

rowName :: TestCase -> String
rowName (ProbTestCase n _ _ _)  = n
rowName (CumulTestCase n _ _ _) = n
rowName _                       = "?"

-- | Run one row through the emitted Python module (End2End's own script, with
-- neural parameters resolved and identity network mocks, exactly as
-- 'End2EndTesting.testPython' does). True iff the script exits 0, i.e. the
-- module loaded and the row matched within tolerance. Output is captured, not
-- echoed: a still-broken pin failing to load is the expected outcome here.
-- A Haskell-side codegen crash counts as "does not match".
pythonRowMatches :: Program -> IREnv -> TestCase -> IO Bool
pythonRowMatches prog env tc = do
  projectDir <- getCurrentDirectory
  let script = pythonTestScript projectDir (networkMocks prog) env [resolveNeuralTestCase prog (shapeNeuralTestCase prog tc)]
  forcedScript <- try (evaluate (length script)) :: IO (Either SomeException Int)
  case forcedScript of
    Left _ -> return False
    Right _ -> withSystemTempFile "spll_known_issue.py" $ \tmpPath h -> do
      hPutStr h script
      hClose h
      (code, _, _) <- readProcessWithExitCode "python3" [tmpPath] ""
      return (code == ExitSuccess)

checkStillBroken :: String -> String -> Expectation -> Either CompilerError IRValue -> IO ()
checkStillBroken name caseName expct er = do
  r <- try (evaluate (length (show er)) >> return er)
         :: IO (Either SomeException (Either CompilerError IRValue))
  case r of
    Left _ -> return ()               -- runtime crash: still broken
    Right (Left _) -> return ()       -- query refused outright: still broken
    Right (Right res@(VProbDim outProb outDim)) ->
      assertBool
        (name ++ "/" ++ caseName ++ " [interpreter]: now matches the documented idealized value -- \
                 \this known issue may be fixed; if so, tighten or move this case out \
                 \of known-issues")
        (not (matchesExpectation expct outProb outDim res))
    Right (Right _) -> return ()      -- not a prob/dim result: still broken

matchesExpectation :: Expectation -> Double -> Double -> IRValue -> Bool
matchesExpectation (Possible (VFloat expectedProb) (VFloat expectedDim) mImp) outProb outDim res =
  abs (outProb - expectedProb) < probTolerance
    && outDim == expectedDim
    && matchesImposs mImp res
matchesExpectation (Possible {}) _ _ _ = False
matchesExpectation Impossible outProb _ res =
  abs outProb < probTolerance && matchesImposs (Just True) res

matchesImposs :: Maybe Bool -> IRValue -> Bool
matchesImposs Nothing _ = True
matchesImposs (Just expected) res = resultImpossible res == Just expected

-- | Force a compile result, catching either a genuine crash (an uncaught
-- exception thrown while forcing it) or an ordinary, non-crashing result
-- (a graceful 'Left', or a 'Right' that forces cleanly).
forced :: Show a => Either CompilerError a -> IO (Either SomeException Int)
forced = try . evaluate . length . show

-- | 'ExpectCrash'/'ExpectDiagnostic': the known issue must still crash at
-- compile time. A graceful @Left@ does not count -- that is an intended
-- refusal, not the bug this folder pins.
assertCrashes :: String -> Either CompilerError IREnv -> Maybe String -> IO ()
assertCrashes name compiled mNeedle = do
  result <- forced compiled
  case result of
    Left ex -> case mNeedle of
      Nothing -> return ()
      Just needle -> assertBool
        (name ++ ": crashed, but not with the pinned diagnostic \"" ++ needle
               ++ "\": " ++ show ex)
        (needle `isInfixOf` show ex)
    Right _ -> assertFailure
      (name ++ ": expected this known issue to still crash at compile time, but it did not \
              \-- the bug it pins may be fixed; if so, move or retire this known-issues case")

-- ---------------------------------------------------------------------------
-- Performance pins (task known-issues-performance-scaling-checks)
-- ---------------------------------------------------------------------------

-- | A code-size pin: the emitted Python must still be larger than the bound.
-- Returns the measured size, shown beside the passing test.
checkCodeSizeAbove :: String -> Program -> ExpectFailure -> IO String
checkCodeSizeAbove name prog (ExpectCodeSizeAbove bound flags cap) = do
  point <- measureCompile cap (applyCompileFlags flags defaultCompilerConfig) prog
  case point of
    PointFailed why -> assertFailure (name ++ ": a code-size pin must compile: " ++ why)
    PointCapped why ->
      assertFailure (name ++ ": the compile ran into the per-compile cap (" ++ why
                     ++ "), so its size could not be measured; a code-size pin \
                        \should be cheap -- shrink the program or raise `cap:`")
    PointDone m -> do
      assertBool (name ++ ": emitted Python is " ++ show (mCodeBytes m) ++ " bytes, no longer above \
                         \the pinned " ++ show bound ++ " -- this known issue may be fixed; if so, \
                         \move the program to the corpus (and add a regression guard), or tighten \
                         \the bound if it only shrank")
        (mCodeBytes m > bound)
      return ("still " ++ show (mCodeBytes m) ++ " bytes > " ++ show bound)
checkCodeSizeAbove name _ ef =
  assertFailure (name ++ ": internal: not a code-size pin: " ++ show ef)

-- | Everything one capped compile measured.
data Measurement = Measurement
  { mCodeBytes :: Integer   -- ^ UTF-8 bytes of the emitted Python module
  , mIRChars   :: Integer   -- ^ characters of the shown IR environment (0 unless asked for)
  , mAlloc     :: Integer   -- ^ bytes allocated by this thread during compile + codegen
  , mSeconds   :: Double    -- ^ wall time of compile + codegen
  }

data PointResult
  = PointDone Measurement
  | PointCapped String      -- ^ ran into the time or allocation cap
  | PointFailed String      -- ^ refused, crashed, or failed to parse

-- | Compile and emit Python under a hard cap: a 'timeout' on wall time and
-- GHC's per-thread allocation limit ('enableAllocationLimit') on the bytes
-- this thread allocates, so a runaway compile is killed and recorded rather
-- than hanging or exhausting the suite. The allocation counter is per Haskell
-- thread, so tests running in parallel do not pollute it; the compile is
-- forced on this thread, so its work is counted here. Bounding allocation
-- also bounds what the compile can retain.
measureCompile :: PointCap -> CompilerConfig -> Program -> IO PointResult
measureCompile = measureCompileWith False

measureCompileWith :: Bool -> PointCap -> CompilerConfig -> Program -> IO PointResult
measureCompileWith wantIR cap conf prog = do
  let micros = max 1 (round (capSeconds cap * 1e6))
  r <- try $ timeout micros $ flip finally disableAllocationLimit $ do
    setAllocationCounter (fromInteger (capAllocBytes cap))
    enableAllocationLimit
    t0 <- getMonotonicTime
    outcome <- case compile conf prog of
      Left err -> return (Left ("refused: " ++ err))
      Right env -> do
        code <- evaluate (utf8Length (intercalate "\n" (generateFunctions True env)))
        ir <- if wantIR then evaluate (toInteger (length (show env))) else return 0
        return (Right (code, ir))
    t1 <- getMonotonicTime
    left <- getAllocationCounter
    let allocated = capAllocBytes cap - toInteger left
    return (fmap (\(code, ir) -> Measurement code ir allocated (t1 - t0)) outcome)
  return $ case r of
    Left ex -> case fromException ex of
      Just AllocationLimitExceeded -> PointCapped (showBytes (capAllocBytes cap) ++ " allocated")
      Nothing -> PointFailed ("crashed: " ++ show ex)
    Right Nothing -> PointCapped (show (capSeconds cap) ++ " s")
    Right (Just (Left why)) -> PointFailed why
    Right (Just (Right m)) -> PointDone m
  where
    showBytes b = show (b `div` 1000000) ++ " MB"

-- | Bytes of the UTF-8 encoding (the emitted module is ASCII in practice, but
-- this is what the CLI writes).
utf8Length :: String -> Integer
utf8Length = foldl' (\acc c -> acc + width (fromEnum c)) 0
  where
    width n | n < 0x80 = 1
            | n < 0x800 = 2
            | n < 0x10000 = 3
            | otherwise = 4

-- | The slope margin added to a growth pin's degree: none worth speaking of
-- for the deterministic metrics, a whole degree for wall time.
metricMargin :: GrowthMetric -> Double
metricMargin MetricCodeSize = 0.25
metricMargin MetricIRSize = 0.25
metricMargin MetricAlloc = 0.5
metricMargin MetricWallTime = 1.0

-- | The metric as the @metric:@ header spells it.
metricName :: GrowthMetric -> String
metricName MetricCodeSize = "code-size"
metricName MetricIRSize = "ir-size"
metricName MetricAlloc = "alloc"
metricName MetricWallTime = "wall-time"

metricValue :: GrowthMetric -> Measurement -> Double
metricValue MetricCodeSize = fromInteger . mCodeBytes
metricValue MetricIRSize = fromInteger . mIRChars
metricValue MetricAlloc = fromInteger . mAlloc
-- A floor keeps a sub-millisecond compile from reading as a huge ratio.
metricValue MetricWallTime = max 0.01 . mSeconds

-- | A growth pin: expand the template at each knob value in turn and climb
-- (see "ScalingCheck"). Still exceeding the bound passes; staying within it
-- at every pair fails ("may be fixed"); a template, parse or compile failure
-- fails too, since the pin documents a family that compiles, just too
-- expensively.
checkGrowthAbove :: String -> FilePath -> GrowthSpec -> String -> IO String
checkGrowthAbove name pplPath spec src = do
  let conf = applyCompileFlags (growthFlags spec) defaultCompilerConfig
      metric = growthMetric spec
      bound = fromIntegral (growthDegree spec) + metricMargin metric
      boundName = if growthDegree spec == 1 then "linear" else "polynomial " ++ show (growthDegree spec)
      label n = growthKnob spec ++ "=" ++ show n
  failures <- newIORef []
  verdict <- climb bound (growthValues spec) $ \n ->
    case expandTemplate (growthKnob spec) n pplPath src of
      Left err -> recordFail failures (label n ++ ": template: " ++ err)
      Right expanded -> case tryParseProgram (pplPath ++ "@" ++ label n) expanded of
        Left err -> recordFail failures (label n ++ ": parse: " ++ errorBundlePretty err)
        Right prog -> do
          res <- measureCompileWith (metric == MetricIRSize) (growthCap spec) conf prog
          case res of
            PointDone m -> return (Measured (metricValue metric m))
            PointCapped why -> return (Capped why)
            PointFailed why -> recordFail failures (label n ++ ": " ++ why)
  failed <- readIORef failures
  case (failed, verdict) of
    (f : _, _) -> assertFailure (name ++ ": a growth pin's family must compile at every point it \
                                        \measures; " ++ f)
    (_, Exceeds evidence) -> return ("still above " ++ boundName ++ " in " ++ metricName metric ++ ": " ++ evidence)
    (_, Unmeasurable why) -> assertFailure (name ++ ": " ++ why)
    (_, WithinBound table) ->
      assertFailure (name ++ ": " ++ metricName metric ++ " now grows within " ++ boundName ++ " over "
                     ++ growthKnob spec ++ " (" ++ table ++ ") -- this known issue may be fixed; \
                     \if so, move it out of known-issues and add a regression guard")
  where
    -- A failed point stops the climb (as a cap would) and is reported above.
    recordFail ref msg = modifyIORef ref (++ [msg]) >> return (Capped "failed")

-- | The harness's own checks: the per-point cap really kills a runaway
-- compile (both limits), and the performance-pin header lines parse as
-- documented. The pure template/climb units are 'ScalingCheck.scalingCheckTests'.
performancePinHarnessTests :: TestTree
performancePinHarnessTests = testGroup "KnownIssuesHarness"
  [ testCase "the allocation cap kills a runaway compile" $ do
      prog <- wideRecord 12
      r <- measureCompile (PointCap 60 50000000) (applyCompileFlags [FlagOptimizer 0] defaultCompilerConfig) prog
      case r of
        PointCapped why -> assertBool why ("allocated" `isInfixOf` why)
        _ -> assertFailure "expected the 50 MB allocation cap to stop a 12-field -O0 compile"
  , testCase "the time cap kills a runaway compile" $ do
      prog <- wideRecord 12
      r <- measureCompile (PointCap 0.05 100000000000) (applyCompileFlags [FlagOptimizer 0] defaultCompilerConfig) prog
      case r of
        PointCapped why -> assertBool why (" s" `isInfixOf` why)
        _ -> assertFailure "expected the 0.05 s cap to stop a 12-field -O0 compile"
  , testCase "a cheap compile is measured" $ do
      prog <- wideRecord 2
      r <- measureCompile defaultPointCap defaultCompilerConfig prog
      case r of
        PointDone m -> assertBool "positive size and allocation" (mCodeBytes m > 0 && mAlloc m > 0)
        _ -> assertFailure "expected a 2-field compile to be measured"
  , testCase "growth header: knob, metric, long flags, cap" $
      assertEqual "parsed"
        (Right (defaultBackends, False, Just (ExpectGrowthAbove (GrowthSpec 2 "N" [2, 4, 8] MetricAlloc
                  [FlagOptimizer 0, FlagNoIntegrate, FlagMaterializationBudget 0] (PointCap 2.5 300000000))), 0))
        (summary (parseTestCasesFromString "h.tst"
          "-- comment\nexpect-failure: growth above polynomial 2\nflags: -O 0 --noIntegrate --materializationBudget 0\n\
          \knob: N = 2, 4, 8\ncap: 2.5 s, 300 MB\nmetric: alloc\n"))
  , testCase "growth header: linear and the defaults" $
      assertEqual "parsed"
        (Right (defaultBackends, False, Just (ExpectGrowthAbove (GrowthSpec 1 "depth" [1, 2] MetricCodeSize [] defaultPointCap)), 0))
        (summary (parseTestCasesFromString "h.tst" "expect-failure: growth above linear\nknob: depth = 1, 2\n"))
  , testCase "code-size header" $
      assertEqual "parsed"
        (Right (defaultBackends, False, Just (ExpectCodeSizeAbove 40000 [FlagPruneAnyChecks] defaultPointCap), 0))
        (summary (parseTestCasesFromString "h.tst" "expect-failure: code-size above 40 KB\nflags: --pruneAnyChecks\n"))
  , testCase "malformed performance pins are parse errors" $
      mapM_ (\(what, src) -> case parseTestCasesFromString "h.tst" src of
                Left _ -> return ()
                Right r -> assertFailure (what ++ ": expected a parse error, got " ++ show (summary (Right r))))
        [ ("no knob", "expect-failure: growth above linear\n")
        , ("decreasing knob", "expect-failure: growth above linear\nknob: N = 4, 2\n")
        , ("single knob value", "expect-failure: growth above linear\nknob: N = 4\n")
        , ("knob on code-size", "expect-failure: code-size above 1 KB\nknob: N = 1, 2\n")
        , ("unknown flag", "expect-failure: code-size above 1 KB\nflags: --noIntegrat\n")
        , ("two metric lines", "expect-failure: growth above linear\nknob: N = 1, 2\nmetric: alloc\nmetric: ir-size\n")
        , ("missing unit", "expect-failure: code-size above 40\n")
        ]
  ]
  where
    summary = fmap (\(bs, slow, ef, tcs) -> (bs, slow, ef, length tcs))
    wideRecord :: Int -> IO Program
    wideRecord n =
      let fields = intercalate ", " [ "f" ++ show i ++ "::Int" | i <- [1 .. n] ]
          args = unwords (map show [1 .. n])
          src = "data R = R " ++ fields ++ ", g::Int\n\nmain = R " ++ args ++ " (if Uniform < 0.5 then 1 else 2)\n"
      in either (fail . errorBundlePretty) return (tryParseProgram "wideRecord.ppl" src)
