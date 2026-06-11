{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Exit (exitWith, ExitCode(ExitFailure))
import System.Directory (listDirectory, getCurrentDirectory)
import System.FilePath (stripExtension, isExtensionOf)
import System.IO.Temp (withSystemTempFile)
import System.IO (hPutStr, hClose)
import System.Process
import System.Exit
import Control.Monad.Random
import System.Random (mkStdGen)
import Data.Maybe
import Data.List (intercalate, nub)
import Data.Text (replace, pack, unpack)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.Parser (tryParseProgram, pValue)
import qualified Text.Megaparsec.Char.Lexer as L
import SPLL.CodeGenJulia
import SPLL.CodeGenPyTorch
import TestCaseParser
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.AutoNeural (makePartitionPlan, planIndexOf)
import Data.Foldable (toList)
import Test.QuickCheck hiding (verbose)
import Debug.Trace
import Control.Exception (try, evaluate, throwIO, SomeException)
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Data.IORef (IORef, newIORef, modifyIORef, readIORef)
import IRInterpreter (generateRand, generateDet)

getAllTestFiles :: IO [(FilePath, FilePath)]
getAllTestFiles = do
  files <- listDirectory "testCases"
  let pplFiles = filter (".ppl" `isExtensionOf`) files
  let pplFullPath = map ("testCases/" ++) pplFiles
  let testCaseFiles = map ((++ ".tst") . (fromJust . stripExtension ".ppl")) pplFullPath
  return (zip pplFullPath testCaseFiles)

{-
parseProbTestCases :: FilePath -> IO [TestCase]
parseProbTestCases fp = do
  content <- readFile fp
  let lines = split '\n' content
  let valueStrs = map (split ';') lines
  let values =  map (map (parseValue fp)) valueStrs
  return $ map (\vals ->
    let (outDim, notDim) = (last vals, init vals)
        (outProb, notOut) = (last notDim, init notDim)
        sample:params = notOut in
          ProbTestCase sample params (outProb, outDim)
    ) values
  where split delim str = case break (==delim) str of
                      (a, delim:b) -> a : split delim b
                      (a, "")    -> [a]
-}

testInterpreter :: Program -> Either CompilerError IREnv -> TestCase -> Property
testInterpreter p compiledE (ProbTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try $ evaluate $ (compiledE >>= \c -> runProbC p c params sample) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VTuple (VFloat outProb) (VFloat outDim))) -> 
      counterexample ("Probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < 0.0001) .&&.
        counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (CumulTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try $ evaluate $ (compiledE >>= \c -> runIntegC p c params sample) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VTuple (VFloat outProb) (VFloat outDim)) )-> 
      counterexample ("Cmulative probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < 0.0001) .&&.
        counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (EncodingLengthTestCase name expectedLen) = ioProperty $ do
  -- Construct one mock sym per outer parameter of main (or none for closed-form programs).
  let paramCnt = progParameterCount p
      mockArgs = replicate paramCnt (VTuple (VInt 0) (VInt 42))
  result <- try $ evaluate $ (compiledE >>= \c -> runEncodeC p c mockArgs) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      counterexample ("Encode length differs for test case " ++ name ++ ". Expected: " ++ show expectedLen ++ " Got: " ++ show (length lst)) (length lst == expectedLen)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a list: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised a compiler error: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (EncodingSlotTestCase name spikeVal idxOf expected) = ioProperty $ do
  -- Build a spiking mock sym: mode=1 spikes the mock NN at spikeVal.
  let mockSym = VTuple (VInt 1) (VTuple spikeVal (VInt 0))
  let (_, TArrow _ target, nnTag) = head (neurals p)
      plan = makePartitionPlan (adts p) target nnTag
      slotIdx = planIndexOf plan idxOf
  result <- try $ evaluate $ (compiledE >>= \c -> runEncodeC p c [mockSym]) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      let items = toList lst
      in if slotIdx >= length items
         then counterexample ("Slot index " ++ show slotIdx ++ " out of bounds (list length " ++ show (length items) ++ ") in test case " ++ name) False
         else case items !! slotIdx of
           VFloat actual ->
             counterexample ("Encode slot " ++ show slotIdx ++ " for " ++ name ++ ": expected " ++ show expected ++ ", got " ++ show actual ++ " (tolerance 0.15)") (abs (actual - expected) < 0.15)
           other -> counterexample ("Slot is not VFloat: " ++ show other ++ " in " ++ name) False
    Right (Right x) -> counterexample ("Output is not a list: " ++ show x ++ " in " ++ name) False
    Right (Left err) -> counterexample ("Compiler error in " ++ name ++ ": " ++ show err) False
    Left err -> counterexample ("Exception in " ++ name ++ ": " ++ show err) False
testInterpreter p compiledE (ArgmaxPTestCase name params res) = ioProperty $ do
  let paramCnt = length params
  let mockedParams seeds = map (\(par, s) -> VTuple (VInt 1) (VTuple par (VInt s))) (zip params seeds)
  let mockedParamsList start = map mockedParams [[x .. x + (paramCnt-1)] | x <- [start, paramCnt..]]  -- [[((1, (p1, 0)), (1, (p2, 1)))], [(1, (p1, 2)), (1, (p2, 3))] ..]
  case compiledE of
    Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Right compiled -> do
      let resP' = runProbC p compiled (head (mockedParamsList 0)) res
      case resP' of
        Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
        Right resP -> do
          let cntSamples = 100
          samples <- evalRandIO (mapM (runGenC p compiled) (take cntSamples (mockedParamsList paramCnt)))
          -- The prob queries are independent and pure; force them in parallel.
          probResults <- parEval (map (\(par, s) -> runProbC p compiled par s) (zip (take cntSamples (mockedParamsList (paramCnt * cntSamples))) samples))
          case sequence probResults of
            Left err -> return $ counterexample err False
            Right samplesP -> return $ conjoin (map (\(s, p) -> counterexample ("Test Case " ++ name ++ ": Sample " ++ show s ++ " has highest probability: " ++ show p ++ " instead of sample " ++ show res ++ " with probability: " ++ show resP) (p `lessEqualsProbs` resP || s == res)) (zip samples samplesP))

-- Force a list of independent pure results concurrently (one thread each).
-- The values are unchanged - this only spreads the evaluation work across cores.
parEval :: [a] -> IO [a]
parEval xs = do
  vars <- mapM (\x -> do
    v <- newEmptyMVar
    _ <- forkIO (try (evaluate x) >>= putMVar v)
    return v) xs
  mapM (\v -> takeMVar v >>= either (\e -> throwIO (e :: SomeException)) return) vars

lessEqualsProbs :: IRValue -> IRValue -> Bool
lessEqualsProbs (VFloat a) (VFloat b) = a <= b
lessEqualsProbs (VTuple (VFloat aP) (VFloat aD)) (VTuple (VFloat bP) (VFloat bD)) | aD == bD = aP <= bP
lessEqualsProbs (VTuple _ (VFloat aD)) (VTuple _ (VFloat bD)) = aD > bD -- Lower dimensionality means higher probability

-- Samples are drawn with replacement from a small discrete support, so the same
-- value tends to come up many times in 1000 draws. generateDet's cost depends on
-- the size of that support (it enumerates it), not on sampleCnt, so evaluating it
-- once per *distinct* sampled value (weighted by how often it occurred) gives the
-- exact same sum but skips the redundant repeat evaluations.
discreteProbsNormalized :: Program -> Either CompilerError IREnv -> Property
discreteProbsNormalized p compiledE = case compiledE of
  Left err -> counterexample ("Compilation failed: " ++ err) False
  Right compiled -> ioProperty $ do
    let Just (genExpr, _)  = genFun  (lookupIREnv "main" compiled)
        Just (probExpr, _) = probFun (lookupIREnv "main" compiled)
        randomParams :: RandomGen g => Rand g [IRValue]
        randomParams = replicateM paramCnt (fmap (\x -> VTuple (VInt 0) (VInt x)) (getRandomR (1, 100000)))
        randomParamsForSamples = evalRand (replicateM sampleCnt randomParams) (mkStdGen 42)
        gens = map (\args -> generateRand (neurals p) compiled (map IRConst args) genExpr) randomParamsForSamples
        pSamples = evalRand (sequence gens) (mkStdGen 42)
        uniqueSamples = nub pSamples
        counts = map (\u -> length (filter (== u) pSamples)) uniqueSamples
    -- The per-sample prob queries are independent and pure; force them in parallel.
    probResults <- parEval (map (\sam -> generateDet (neurals p) compiled (map IRConst (sam:params)) probExpr) uniqueSamples)
    return $ case sequence probResults of
        Left err -> counterexample err False
        Right t
          | all ((== VInt 0) . dim) t ->
              -- Discrete (dim 0): with 1000 draws from a small support, every distinct
              -- value is observed, so the probabilities of the distinct observed values
              -- should sum to (approximately) exactly 1. Checking both bounds catches
              -- both missing mass (e.g. wrong probabilities) and double-counted /
              -- unnormalized probabilities (sum > 1), neither of which the old
              -- count-weighted sum (always >> 1 for small supports) could detect.
              let totalProb = sum (map prob t)
              in counterexample ("Probabilities of distinct sampled values sum to " ++ show totalProb ++ ", expected ~1") (abs (totalProb - 1) < 0.01)
          | otherwise ->
              -- Continuous: sampled values are (almost) all distinct, and a sum of
              -- densities has no "=1" meaning - just check the densities aren't degenerate.
              let sumProbSamples = sum (zipWith (\c r -> fromIntegral c * prob r) counts t)
              in counterexample "Probability of randomly sampled values does not sum to 1" (sumProbSamples >= sufficientlyNormal)
  where
    paramCnt = progParameterCount p
    seedList = [0 .. (paramCnt - 1)]
    params = map (VTuple (VInt 0) . VInt) seedList
    sampleCnt = 1000
    sufficientlyNormal = 0.99
    prob (VTuple (VFloat p) _) = p
    dim (VTuple _ d) = d

progParameterCount :: Program -> Int
progParameterCount Program{functions=f} = countLambdas main
  where
    Just main = lookup "main" f
    countLambdas (Lambda _ _ e) = 1 + countLambdas e
    countLambdas _ = 0

testJuliaAll :: [(Either CompilerError IREnv, [TestCase])] -> Property
testJuliaAll programCases = ioProperty $ do
  let results = [(c, tcs) | (c, tcs) <- programCases, not (null tcs)]
  case [err | (Left err, _) <- results] of
    (err:_) -> return $ counterexample err False
    [] -> do
      let srcs = [(intercalate "\n" (SPLL.CodeGenJulia.generateFunctions c), tcs) | (Right c, tcs) <- results]
      projectDir <- getCurrentDirectory
      code <- withSystemTempFile "julia_batch.jl" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle (juliaBatchTestCode projectDir srcs)
        hClose tmpHandle
        (_, _, _, handle) <- createProcess (proc "julia" [tmpPath])
        waitForProcess handle
      return $ case code of
        ExitSuccess -> True === True
        ExitFailure _ -> counterexample "Julia batch test failed. See Julia error message above." False

testPython :: Either CompilerError IREnv -> [TestCase] -> Property
testPython compiledE tc = ioProperty $ do
  case compiledE of
    Left err -> return $ counterexample err False
    Right compiled -> do
      let src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True compiled)
      (_, _, _, handle) <- createProcess (proc "python3" ["-c", pythonTestCode src tc])
      code <- waitForProcess handle
      case code of
        ExitSuccess -> return $ True === True
        ExitFailure _ -> return $ counterexample ("Python test " ++ testCaseName (head tc) ++ " failed. See Python error message") False

juliaBatchTestCode :: FilePath -> [(String, [TestCase])] -> String
juliaBatchTestCode projectDir allCases =
  "include(\"" ++ projectDir ++ "/juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n" ++
  concatMap (\(idx, (src, tcs)) ->
    let modName = "Prog" ++ show (idx :: Int)
    in "module " ++ modName ++ "\nusing ..JuliaSPPLLib\n" ++
       src ++ "\nend\n" ++
       juliaModuleTestCases modName tcs
  ) (zip [0..] allCases)

juliaModuleTestCases :: String -> [TestCase] -> String
juliaModuleTestCases modName tcs =
  modName ++ ".main_gen(" ++ intercalate ", " (map juliaVal exampleParams) ++ ")\n" ++
  concat (map (\tc ->
    let (name, sample, params, outProb, outDim) = unpackTestCase tc
        call = modName ++ "." ++ mainName tc ++ "(" ++ juliaVal sample ++ ", " ++ intercalate ", " (map juliaVal params) ++ ")"
    in "tmp = " ++ call ++ "\n\
       \if abs(tmp[1] - " ++ juliaVal outProb ++ ") > 0.0001\n\
       \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ ") * \"in test case " ++ name ++ "\")\n\
       \end\n\
       \if tmp[1] != 0 && tmp[2] != " ++ juliaVal outDim ++ "\n\
       \  error(\"Dimensionality wrong: \" * string(tmp[2]) * \"/=\" * string(" ++ juliaVal outDim ++ ") * \"in test case " ++ name ++ "\")\n\
       \end\n"
    ) tcs)
  where
    (_, _, exampleParams, _, _) = unpackTestCase (head tcs)
    unpackTestCase (ProbTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    unpackTestCase (CumulTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    mainName (ProbTestCase _ _ _ _) = "main_prob"
    mainName (CumulTestCase _ _ _ _) = "main_integ"

pythonTestCode :: String -> [TestCase] -> String
pythonTestCode src tcs = 
  unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") (pack src)) ++ "\n" ++   -- Importing pyTorch is really slow and not needed
  "main.generate(" ++ intercalate ", " (map pyVal exampleParams) ++ ")\n" ++
  concat (map (\tc -> let (name, sample, params, outProb, outDim) = unpackTestCase tc in 
    "tmp = " ++ mainName tc ++ "(" ++  pyVal sample ++ ", " ++ intercalate ", " (map pyVal params) ++ ")\n\
    \if abs(tmp[0] - " ++ pyVal outProb ++ ") > 0.0001:\n\
    \  raise ValueError(\"Probability wrong: \" + str(tmp[0]) + \"!=\" + str(" ++ pyVal outProb ++ ") + \"in test case " ++ name ++ "\")\n\
    \if tmp[0] != 0 and tmp[1] != " ++ pyVal outDim ++ ":\n\
    \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1]) + \"/=\" + str(" ++ pyVal outDim ++ ") + \"in test case " ++ name ++ "\")\n\
    \") tcs)
  where 
    (_, _, exampleParams, _, _) = unpackTestCase (head tcs)
    unpackTestCase (ProbTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    unpackTestCase (CumulTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    mainName (ProbTestCase _ _ _ _) = "main.forward"
    mainName (CumulTestCase _ _ _ _) = "main.integrate"

type TimingLog = IORef [(String, Int)]

newTimingLog :: IO TimingLog
newTimingLog = newIORef []

timedLog :: TimingLog -> String -> IO a -> IO a
timedLog tlog label action = do
  start <- getCurrentTime
  result <- action
  end <- getCurrentTime
  let ms = round (realToFrac (diffUTCTime end start) * 1000 :: Double) :: Int
  modifyIORef tlog ((label, ms) :)
  return result

printTimingSummary :: TimingLog -> IO ()
printTimingSummary tlog = do
  entries <- fmap reverse (readIORef tlog)
  let total = sum (map snd entries)
  putStrLn "\n=== Timing Summary ==="
  mapM_ (\(lbl, ms) ->
    let pct = if total == 0 then (0 :: Int)
              else round (fromIntegral ms * 100 / fromIntegral total :: Double)
    in putStrLn $ "  " ++ lbl ++ ": " ++ show ms ++ " ms (" ++ show pct ++ "%)"
    ) entries
  putStrLn $ "  Total: " ++ show total ++ " ms"

test_end2end :: TimingLog -> IO Bool
test_end2end tlog = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  -- Compile each program exactly once; every test group below shares the result.
  let compiledCases = [(p, compile defaultCompilerConfig p, tcs) | (p, tcs) <- cases]
  let queryTestCases = [(p, c, filter (\x -> isProbTestCase x || isCumulTestCase x) tcs) | (p, c, tcs) <- compiledCases]
  let nonNeuralsQueries = filter (\(p, _, _) -> null (neurals p)) queryTestCases
  let neuralP = [(p, c) | (p, c, _) <- compiledCases, not (null (neurals p))]

  putStrLn "=== Test End2End Interpreter ==="
  let interprTest = label "End2End Interpreter" $ conjoin [conjoin $ map (testInterpreter p c) tcs | (p, c, tcs) <- compiledCases]
  interprProp <- timedLog tlog "End2End Interpreter" $ quickCheckResult (withMaxSuccess 1 interprTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Interpreter Normalization ==="
  let interprNormalizeTest = label "End2End Interpreter Normalization" $ conjoin [discreteProbsNormalized p c | (p, c) <- neuralP]
  interprNormalProp <- timedLog tlog "End2End Interpreter Normalization" $ quickCheckResult (withMaxSuccess 1 interprNormalizeTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Julia ==="
  let juliaTest = label "End2End Julia" $ testJuliaAll [(c, tcs) | (_, c, tcs) <- nonNeuralsQueries]
  juliaProp <- timedLog tlog "End2End Julia" $ quickCheckResult (withMaxSuccess 1 juliaTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Python ==="
  let pythonTest = label "End2End Python" $ conjoin [testPython c tcs | (_, c, tcs) <- nonNeuralsQueries]
  pythonProp <- timedLog tlog "End2End Python" $ quickCheckResult (withMaxSuccess 1 pythonTest) >>= return . isSuccess

  return $ interprProp && interprNormalProp && juliaProp && pythonProp
