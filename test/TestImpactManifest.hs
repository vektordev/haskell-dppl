-- | The impact-analysis manifest ('ImpactManifest') and the keys the corpus
-- sweeps compute for it (End2EndTesting). Docs-repo task
-- emitted-code-test-impact-analysis.
module TestImpactManifest (impactManifestTests) where

import Control.Monad (forM_)
import Control.Exception (SomeException, evaluate, throwIO, try)
import Data.IORef
import qualified Data.Map.Strict as Map
import System.Directory (getTemporaryDirectory, removeFile, doesFileExist)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.QuickCheck (Property, property, counterexample, quickCheckWithResult, stdArgs, chatty, isSuccess, ioProperty)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual, (@?=))

import SPLL.Prelude (compile)
import SPLL.IntermediateRepresentation (defaultCompilerConfig, CompilerConfig(..), IREnv)
import ImpactManifest
import CertifiedCensus (programCensus, uncertifiedConstructs, certifiedConstructs, samplingConstructs,
                        batchedProgramCensus, batchedUncertifiedConstructs, batchedCertifiedConstructs, lineSpillLabel,
                        selectDemotionLabel, pureCalleeLabel)
import End2EndTesting (interpreterKey, pythonKey, juliaKey, loadCorpusPair, networkMocks)
import TestCaseParser (corpusPplPath, isProbTestCase, isCumulTestCase)

impactManifestTests :: TestTree
impactManifestTests = testGroup "ImpactManifest"
  [ testCase "an edited program's keys change and nothing else's do" editedProgramKeys
  , testCase "a pass is skipped on the next run, a changed key executes" passThenSkip
  , testCase "a failing check is not recorded" failureNotRecorded
  , testCase "NEST_FULL_TESTS mode executes a recorded check" fullModeExecutes
  , testCase "a batch executes only its changed members" batchRunsMisses
  , testCase "an action is skipped on a hit, and recorded only when it returns" actionPassThenSkip
  , testCase "an unreadable manifest is an empty one" corruptManifest
  , testCase "the interpreter closure is the interpreter, not the compiler" closureIsNarrow
  , testCase "M2: a census leaving the certified constructs keeps the text backends" censusRouting
  , testCase "batched compliance: a batched census leaving the certified constructs keeps batched-vs-expected" batchedCensusRouting
  ]

-- | M2 (task impact-analysis-m2-drop-runtime-from-key): a corpus program runs
-- on the scalar Python and Julia backends exactly when 'uncertifiedConstructs'
-- of its census is non-empty. The census of a real corpus program sees its
-- constructs, generate bodies and their draws included (certified since the
-- IR fuzz generator's M4); a construct outside 'certifiedConstructs' is
-- reported, one inside is not.
censusRouting :: IO ()
censusRouting = do
  path <- corpusPplPath "addNormals"
  (p, _) <- loadCorpusPair (path, take (length path - 4) path ++ ".tst")
  let census = programCensus [compile defaultCompilerConfig p]
  assertBool ("the census sees the program's IR: " ++ show census) ("IRExpr:IRVar" `elem` census)
  assertBool ("the census sees the generate body's draws: " ++ show census)
    (any (`elem` samplingConstructs) census)
  assertEqual "a corpus program's census is certified" [] (uncertifiedConstructs census)
  assertEqual "a refused compile contributes nothing" census
    (programCensus [compile defaultCompilerConfig p, Left "refused" :: Either String IREnv])
  assertEqual "a construct the fuzzers never reach is uncertified" ["Accessor:AcNotDrawn"]
    (uncertifiedConstructs ("Accessor:AcNotDrawn" : census))
  assertEqual "the certified list certifies itself" [] (uncertifiedConstructs certifiedConstructs)

-- | Batched reference compliance (task batched-backend-reference-compliance):
-- a @batched@ corpus program's rows run on the batched backend exactly when
-- 'batchedUncertifiedConstructs' of its batched census is non-empty. The
-- census is of the batched compile (after the select pass); a theta-tree
-- read, which no batched arm compares, keeps the check.
batchedCensusRouting :: IO ()
batchedCensusRouting = do
  let load n = do
        path <- corpusPplPath n
        fst <$> loadCorpusPair (path, take (length path - 4) path ++ ".tst")
      census p = batchedProgramCensus (compile defaultCompilerConfig { batched = True } p)
  plain <- census <$> load "addNormals"
  assertBool ("the batched census sees the program's IR: " ++ show plain) ("IRExpr:IRDensity" `elem` plain)
  assertEqual "a plain batched program is certified" [] (batchedUncertifiedConstructs plain)
  theta <- census <$> load "theta"
  assertEqual "a theta-tree read is not certified" ["Accessor:AcTheta"] (batchedUncertifiedConstructs theta)
  -- A 250-value neural agreement: its mask variant's point read is spilled
  -- for CPython's bracket limit, which the fuzz arms never reach.
  wide <- census <$> load "batchedMaskVariantNeuralReadChain"
  assertEqual "a module with a spilled line is not certified" [lineSpillLabel] (batchedUncertifiedConstructs wide)
  assertBool "a module without one carries no spill label" (lineSpillLabel `notElem` plain)
  -- A draw-bound list element: its witness guard is a select over the shape
  -- probe `sample == []`, which the batched backend emits as a Python if.
  demoted <- census <$> load "drawBoundListElementGuardsEmptyTail"
  assertEqual "a demoted structural select is not certified" [selectDemotionLabel] (batchedUncertifiedConstructs demoted)
  assertBool "a module without one carries no demotion label" (selectDemotionLabel `notElem` plain)
  -- A prob path calling a recursive deterministic helper's evaluator, and
  -- one reading a helper's Gaussian parameters: the callee's method body is
  -- emitted code the fuzz arms (prob/integ bodies only) never ran.
  forM_ ["recursiveHelperOnlyWhereGuarded", "normalThroughFunctionParam"] $ \n -> do
    c <- census <$> load n
    assertBool (n ++ " calls a pure callee, so it is not certified: " ++ show c)
      (pureCalleeLabel `elem` batchedUncertifiedConstructs c)
  assertBool "a module without one carries no pure-callee label" (pureCalleeLabel `notElem` plain)
  assertEqual "a refused compile contributes nothing" [] (batchedProgramCensus (Left "refused" :: Either String IREnv))
  assertEqual "the batched certified list certifies itself" [] (batchedUncertifiedConstructs batchedCertifiedConstructs)

-- | Run a property once, quietly, and report whether it passed.
runProp :: Property -> IO Bool
runProp p = isSuccess <$> quickCheckWithResult stdArgs { chatty = False } p

-- | A property that counts its executions and has the given verdict.
counted :: IORef Int -> Bool -> Property
counted ref verdict = ioProperty $ do
  modifyIORef' ref (+ 1)
  return (counterexample "deliberate failure" (property verdict))

withManifest :: (FilePath -> IO a) -> IO a
withManifest k = withSystemTempDirectory "impact-manifest" (\d -> k (d </> "manifest"))

-- Acceptance (b) of the task: editing one corpus program (in a temp copy)
-- changes exactly that program's keys. Recomputing an unedited program's keys
-- from a fresh parse and compile reproduces them, which is the
-- non-deterministic-emission pitfall: if it failed, every run would be full.
editedProgramKeys :: IO ()
editedProgramKeys = withManifest $ \file -> do
  m <- openManifest file False
  editedPath <- corpusPplPath "discreteFloats"
  otherPath  <- corpusPplPath "addNormals"
  let tstOf path = take (length path - 4) path ++ ".tst"
  before   <- corpusKeys m (editedPath, tstOf editedPath)
  other    <- corpusKeys m (otherPath, tstOf otherPath)
  before'  <- corpusKeys m (editedPath, tstOf editedPath)
  other'   <- corpusKeys m (otherPath, tstOf otherPath)
  assertEqual "recompiling discreteFloats reproduces its keys" before before'
  assertEqual "recompiling addNormals reproduces its keys" other other'
  assertBool "every key is present" (all (/= Nothing) (before ++ other))
  src <- readFile editedPath
  _ <- evaluate (length src)
  tmp <- getTemporaryDirectory
  let copy = tmp </> "impactManifestEdited.ppl"
      edited = replaceOnce "0.5" "0.25" src
  assertBool "the edit applies" (edited /= src)
  writeFile copy edited
  after <- corpusKeys m (copy, tstOf editedPath)
  removeFile copy
  forM_ (zip3 ["interpreter", "python", "julia"] before after) $ \(lbl, b, a) ->
    assertBool ("the edited program's " ++ lbl ++ " key changes") (b /= a)
  where
    replaceOnce old new s = go s
      where go [] = []
            go str@(c:cs) | take (length old) str == old = new ++ drop (length old) str
                          | otherwise = c : go cs

corpusKeys :: Manifest -> (FilePath, FilePath) -> IO [Maybe String]
corpusKeys m pair = do
  (p, (_, _, _, tcs)) <- loadCorpusPair pair
  let c = compile defaultCompilerConfig p
      queries = filter (\x -> isProbTestCase x || isCumulTestCase x) tcs
  i  <- interpreterKey m p c tcs
  py <- pythonKey m (networkMocks p) c queries
  jl <- juliaKey m c queries (networkMocks p)
  return [i, py, jl]

passThenSkip :: IO ()
passThenSkip = withManifest $ \file -> do
  ran <- newIORef 0
  m1 <- openManifest file False
  ok1 <- runProp (cachedProperty m1 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  ok1 @?= True
  writeManifest m1
  m2 <- openManifest file False
  ok2 <- runProp (cachedProperty m2 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  ok2 @?= True
  readIORef ran >>= (@?= 1)
  manifestStats m2 >>= (@?= Map.fromList [("G", (0, 1))])
  -- the same slot under a different key (its program changed) executes
  _ <- runProp (cachedProperty m2 "G" "prog" (return (Just (hashKey ["b"]))) (counted ran True))
  readIORef ran >>= (@?= 2)
  -- the same key in another slot is a different check
  _ <- runProp (cachedProperty m2 "H" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  readIORef ran >>= (@?= 3)
  -- no key (the compile failed): always executes
  _ <- runProp (cachedProperty m2 "G" "prog" (return Nothing) (counted ran True))
  readIORef ran >>= (@?= 4)

failureNotRecorded :: IO ()
failureNotRecorded = withManifest $ \file -> do
  ran <- newIORef 0
  m1 <- openManifest file False
  ok <- runProp (cachedProperty m1 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran False))
  ok @?= False
  writeManifest m1
  m2 <- openManifest file False
  ok' <- runProp (cachedProperty m2 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran False))
  ok' @?= False
  readIORef ran >>= (@?= 2)

fullModeExecutes :: IO ()
fullModeExecutes = withManifest $ \file -> do
  ran <- newIORef 0
  m1 <- openManifest file False
  _ <- runProp (cachedProperty m1 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  writeManifest m1
  full <- openManifest file True
  _ <- runProp (cachedProperty full "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  readIORef ran >>= (@?= 2)
  writeManifest full
  -- the full run's pass is still a pass for the next normal run
  m3 <- openManifest file False
  _ <- runProp (cachedProperty m3 "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  readIORef ran >>= (@?= 2)

batchRunsMisses :: IO ()
batchRunsMisses = withManifest $ \file -> do
  seen <- newIORef []
  let batch m items = runProp (cachedBatch m "J" [ (n, return (Just (hashKey [n, v])), n) | (n, v) <- items ]
                                 (\xs -> ioProperty (modifyIORef' seen (xs :) >> return (property True))))
  m1 <- openManifest file False
  _ <- batch m1 [("a", "1"), ("b", "1"), ("c", "1")]
  writeManifest m1
  m2 <- openManifest file False
  _ <- batch m2 [("a", "1"), ("b", "2"), ("c", "1")]
  _ <- batch m2 [("a", "1"), ("c", "1")]
  readIORef seen >>= (@?= [["b"], ["a", "b", "c"]])

-- 'cachedAction', the HUnit-shaped twin of 'cachedProperty': an assertion
-- fails by throwing, and a throw is not recorded.
actionPassThenSkip :: IO ()
actionPassThenSkip = withManifest $ \file -> do
  ran <- newIORef (0 :: Int)
  let act ok = do
        modifyIORef' ran (+ 1)
        if ok then return "ran" else throwIO (userError "deliberate failure")
      key = return (Just (hashKey ["a"]))
      failing m = try (cachedAction m "A" "bad" key (act False)) :: IO (Either SomeException (Either String String))
  m1 <- openManifest file False
  r1 <- cachedAction m1 "A" "prog" key (act True)
  r1 @?= Right "ran"
  f1 <- failing m1
  assertBool "the failing action throws" (either (const True) (const False) f1)
  writeManifest m1
  m2 <- openManifest file False
  r2 <- cachedAction m2 "A" "prog" key (act True)
  assertBool "a recorded pass is skipped" (either (const True) (const False) r2)
  _ <- failing m2
  readIORef ran >>= (@?= 3)
  manifestStats m2 >>= (@?= Map.fromList [("A", (1, 1))])

corruptManifest :: IO ()
corruptManifest = withManifest $ \file -> do
  writeFile file "not a manifest\n"
  ran <- newIORef 0
  m <- openManifest file False
  _ <- runProp (cachedProperty m "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  readIORef ran >>= (@?= 1)
  writeManifest m
  exists <- doesFileExist file
  assertBool "the manifest is rewritten" exists
  m' <- openManifest file False
  _ <- runProp (cachedProperty m' "G" "prog" (return (Just (hashKey ["a"]))) (counted ran True))
  readIORef ran >>= (@?= 1)

-- M1's key: a change to the interpreter's sources invalidates interpreter
-- checks, a change to the compiler does not (its effect reaches the check
-- through the emitted IR, which is in the key already).
closureIsNarrow :: IO ()
closureIsNarrow = do
  files <- interpreterClosure
  assertBool "IRInterpreter is in its closure" ("src/IRInterpreter.hs" `elem` files)
  assertBool "Prelude (the run*C entry points) is in it" ("src/SPLL/Prelude.hs" `elem` files)
  assertBool "MockNN is in it" ("src/MockNN.hs" `elem` files)
  forM_ ["src/SPLL/IRCompiler.hs", "src/SPLL/IROptimizer.hs", "src/SPLL/Parser.hs", "src/SPLL/CodeGenPyTorch.hs"] $ \f ->
    assertBool (f ++ " is not in the interpreter closure") (f `notElem` files)
