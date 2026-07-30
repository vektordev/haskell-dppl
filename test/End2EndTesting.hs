{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Directory (listDirectory, getCurrentDirectory, doesFileExist)
import System.FilePath (stripExtension, isExtensionOf, takeBaseName)
import System.IO.Temp (withSystemTempFile)
import System.IO (hPutStr, hClose, hPutStrLn, stderr)
import System.Environment (lookupEnv)
import System.Process
import System.Exit
import Data.List (groupBy)
import Data.Function (on)
import Control.Monad.Random
import System.Random (mkStdGen)
import Data.Maybe
import Data.List (intercalate, nub, isInfixOf, transpose, zip4)
import Data.Text (replace, pack, unpack)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.Parser (tryParseProgram, pValue)
import qualified Text.Megaparsec.Char.Lexer as L
import SPLL.CodeGenJulia
import SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import TestCaseParser
import TestTolerances (probTolerance, encodeSlotTolerance, normalizationTolerance, samplingTolerance)
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.AutoNeural (makePartitionPlan, planIndexOf, resolvePartitionAnnotation, PartitionPlan)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Analysis (annotateEnumsProg)
import Data.Foldable (toList)
import Test.QuickCheck hiding (verbose)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Debug.Trace
import Control.Exception (try, evaluate, throwIO, SomeException)
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import IRInterpreter (generateRand, generateDet)

getAllTestFiles :: IO [(FilePath, FilePath)]
getAllTestFiles = do
  files <- listDirectory "testCases"
  let pplFiles = filter (".ppl" `isExtensionOf`) files
  let pplFullPath = map ("testCases/" ++) pplFiles
  let testCaseFiles = map ((++ ".tst") . (fromJust . stripExtension ".ppl")) pplFullPath
  return (zip pplFullPath testCaseFiles)

-- | M1 differential test (design pytorch-tensorizer): the IR select pass is a
-- behavioural no-op under scalar lowering, since the interpreter and scalar
-- backends evaluate a SelectIf exactly like a LazyIf. So for every corpus
-- prob/cumulative query point, compiling with @batched = True@ (which runs the
-- select pass) must return the same result as the default pipeline. Reuses the
-- same corpus loader as 'end2endTests', restricted to the non-slow,
-- interpreter-routed cases.
selectPassDifferentialTests :: IO TestTree
selectPassDifferentialTests = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  let entries = [ (takeBaseName pplPath, p, tcs)
                | ((pplPath, _), (p, (bs, slow, tcs))) <- zip files cases
                , not slow, Interpreter `elem` bs ]
  return $ testGroup "SelectPassNoOp"
    [ testProperty n (once $ conjoin (map (selectNoOp p) tcs)) | (n, p, tcs) <- entries ]

-- | Assert one corpus query point is unchanged by the select pass. Non-query
-- cases (encode/argmax) are skipped: the pass only touches prob/integ bodies.
selectNoOp :: Program -> TestCase -> Property
selectNoOp p (ProbTestCase  name sample params _) = selectNoOpCmp p name (\c -> runProbC  p c params sample)
selectNoOp p (CumulTestCase name sample params _) = selectNoOpCmp p name (\c -> runIntegC p c params sample)
selectNoOp _ _ = property True

selectNoOpCmp :: Program -> String -> (IREnv -> Either CompilerError IRValue) -> Property
selectNoOpCmp p name run = ioProperty $ do
  scalar  <- forceResult (compile defaultCompilerConfig p >>= run)
  batched <- forceResult (compile defaultCompilerConfig{batched = True} p >>= run)
  return $ counterexample
    ("select pass is not a no-op for " ++ name ++ ": scalar=" ++ show scalar ++ ", batched=" ++ show batched)
    (resultsAgree scalar batched)

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

testInterpreter :: Program -> Either CompilerError IREnv -> TestCase -> Property
testInterpreter p compiledE (ProbTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runProbC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VProbDim outProb outDim)) -> 
      counterexample ("Probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < probTolerance) .&&.
        counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (CumulTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runIntegC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VProbDim outProb outDim)) -> 
      counterexample ("Cmulative probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < probTolerance) .&&.
        counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (EncodingLengthTestCase name target explicitArgs expectedLen) = ioProperty $ do
  let args = encodeArgsFor p explicitArgs
  result <- try $ evaluate $ (compiledE >>= \c -> runEncodeC p c target args) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      counterexample ("Encode length differs for test case " ++ name ++ " (target " ++ target ++ "). Expected: " ++ show expectedLen ++ " Got: " ++ show (length lst)) (length lst == expectedLen)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a list: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised a compiler error: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (EncodingSlotTestCase name target explicitArgs idxOf expected) = ioProperty $ do
  let args = encodeArgsFor p explicitArgs
      plan = endpointPlan p target
      slotIdx = planIndexOf plan idxOf
  result <- try $ evaluate $ (compiledE >>= \c -> runEncodeC p c target args) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of
    Right (Right (VList lst)) ->
      let items = toList lst
      in if slotIdx >= length items
         then counterexample ("Slot index " ++ show slotIdx ++ " out of bounds (list length " ++ show (length items) ++ ") in test case " ++ name) False
         else case items !! slotIdx of
           VFloat actual ->
             counterexample ("Encode slot " ++ show slotIdx ++ " for " ++ name ++ ": expected " ++ show expected ++ ", got " ++ show actual ++ " (tolerance " ++ show encodeSlotTolerance ++ ")") (abs (actual - expected) < encodeSlotTolerance)
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
  let mockedParams = [VTuple (VInt 1) (VTuple par (VInt seed)) | (par, seed) <- zip params [0..]]
  case compiledE of
    Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Right compiled -> case runProbC p compiled mockedParams res of
      Left err -> return $ counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
      Right (VProbDim resP resDim)
        | resDim /= 0 -> return $ counterexample ("Test case " ++ name ++ ": argmax_p does not support continuous (dim > 0) results") False
        | otherwise -> evalRandIO (argmaxLoop p compiled name mockedParams res resP [res] resP 0)
      Right x -> return $ counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False

-- Number of consecutive repeat draws (samples already in the bucket) after
-- which we give up: if normalization held, the accumulated mass of a fully
-- re-discovered support would already have completed the proof above, so
-- this many repeats without that happening means the probabilities of the
-- distinct values found so far don't sum to 1.
argmaxPatience :: Int
argmaxPatience = 10000

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

-- Samples are drawn with replacement from a small discrete support, so the same
-- value tends to come up many times in 1000 draws. generateDet's cost depends on
-- the size of that support (it enumerates it), not on sampleCnt, so evaluating it
-- once per *distinct* sampled value (weighted by how often it occurred) gives the
-- exact same sum but skips the redundant repeat evaluations.
discreteProbsNormalized :: Program -> Either CompilerError IREnv -> Property
discreteProbsNormalized p compiledE = case compiledE of
  Left err -> counterexample ("Compilation failed: " ++ err) False
  Right compiled -> case (genFun (lookupIREnv "main" compiled), probFun (lookupIREnv "main" compiled)) of
    -- A program with no probability function cannot have its normalization
    -- checked -- and for an inference compiler, a program we can only sample
    -- from is not a passing test, it is a missing feature. Fail loudly rather
    -- than crash on a partial match (the irrefutable Just-pattern this replaces)
    -- or silently pass. E.g. clevr3_predicate_spatial compares two continuous
    -- neural outputs, which currently yields Bottom and emits no main_prob.
    (Just (genExpr, _), Just (probExpr, _)) -> ioProperty $ do
      let randomParams :: RandomGen g => Rand g [IRValue]
          randomParams = replicateM paramCnt (fmap (\x -> VTuple (VInt 0) (VInt x)) (getRandomR (1, 100000)))
          randomParamsForSamples = evalRand (replicateM sampleCnt randomParams) (mkStdGen 42)
          gens = map (\args -> generateRand (neurals p) (encodeDecls p) compiled (map IRConst args) genExpr) randomParamsForSamples
          pSamples = evalRand (sequence gens) (mkStdGen 42)
          uniqueSamples = nub pSamples
          counts = map (\u -> length (filter (== u) pSamples)) uniqueSamples
      -- The per-sample prob queries are independent and pure; force them in parallel.
      probResults <- parEval (map (\sam -> generateDet (neurals p) (encodeDecls p) compiled (map IRConst (sam:params)) probExpr) uniqueSamples)
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
                in counterexample ("Probabilities of distinct sampled values sum to " ++ show totalProb ++ ", expected ~1") (abs (totalProb - 1) < normalizationTolerance)
            | otherwise ->
                -- Continuous: sampled values are (almost) all distinct, and a sum of
                -- densities has no "=1" meaning - just check the densities aren't degenerate.
                let sumProbSamples = sum (zipWith (\c r -> fromIntegral c * prob r) counts t)
                in counterexample "Probability of randomly sampled values does not sum to 1" (sumProbSamples >= sufficientlyNormal)
    _ -> counterexample "main has no probability function (inference unavailable); only generate compiled" False
  where
    paramCnt = progParameterCount p
    seedList = [0 .. (paramCnt - 1)]
    params = map (VTuple (VInt 0) . VInt) seedList
    sampleCnt = 1000
    sufficientlyNormal = 0.99
    prob :: IRValue -> Double
    prob (VProbDim p _) = p
    prob v = error ("not a probability result: " ++ show v)
    dim :: IRValue -> IRValue
    dim (VProbDim _ d) = VFloat d
    dim v = error ("not a probability result: " ++ show v)

progParameterCount :: Program -> Int
progParameterCount Program{functions=f} = countLambdas main
  where
    Just main = lookup "main" f
    countLambdas (Lambda _ _ e) = 1 + countLambdas e
    countLambdas _ = 0

-- | Build the argument list for an encode query from the directive's explicit args.
--
--   * No-NN programs (per-function encode over real values): args are passed verbatim
--     (e.g. `encode_at[isRed](0.3, indexOf(True))` calls isRed's encode with s = 0.3).
--   * Decoder programs: each explicit arg is the value to spike the mock NN at, wrapped in
--     the mock-sym envelope `(mode=1, (spikeVal, seed=0))` so the mock network peaks there.
--   * Decoder programs with no explicit args (legacy `encode_len=N`): one neutral mock sym
--     per outer parameter of main.
encodeArgsFor :: Program -> [IRValue] -> [IRValue]
encodeArgsFor p explicitArgs
  | not (null explicitArgs) = if null (neurals p) then explicitArgs else map spike explicitArgs
  | null (neurals p)        = []
  | otherwise               = replicate (progParameterCount p) (VTuple (VInt 0) (VInt 42))
  where spike v = VTuple (VInt 1) (VTuple v (VInt 0))

-- | The logit layout for an endpoint function's own output type, resolved exactly as the
-- compiler resolves it when emitting that function's encodeFun (registry entry, else
-- auto-derive). Used to map an `indexOf(value)` directive to a flat slot index.
endpointPlan :: Program -> String -> PartitionPlan
endpointPlan p target = makePartitionPlan (adts p) rt (resolvePartitionAnnotation (encodeDecls p) rt Nothing)
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
    stripLambdasE (Lambda _ _ b) = stripLambdasE b
    stripLambdasE e = e

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

-- The compiled result is (prob, (dim, impossible)) -- the trailing field is the
-- internal impossibility flag (design inference-result-side-channels), which is
-- not stripped from the emitted code, hence the nested dim access below.
juliaModuleTestCases :: String -> [TestCase] -> String
juliaModuleTestCases modName tcs =
  modName ++ ".main_gen(" ++ intercalate ", " (map juliaVal exampleParams) ++ ")\n" ++
  concat (map (\tc ->
    let (name, sample, params, outProb, outDim) = unpackTestCase tc
        call = modName ++ "." ++ mainName tc ++ "(" ++ juliaVal sample ++ ", " ++ intercalate ", " (map juliaVal params) ++ ")"
    in "tmp = " ++ call ++ "\n\
       \if abs(tmp[1] - " ++ juliaVal outProb ++ ") > " ++ show probTolerance ++ "\n\
       \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ ") * \"in test case " ++ name ++ "\")\n\
       \end\n\
       \if tmp[1] != 0 && tmp[2][1] != " ++ juliaVal outDim ++ "\n\
       \  error(\"Dimensionality wrong: \" * string(tmp[2][1]) * \"/=\" * string(" ++ juliaVal outDim ++ ") * \"in test case " ++ name ++ "\")\n\
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
    \if abs(tmp[0] - " ++ pyVal outProb ++ ") > " ++ show probTolerance ++ ":\n\
    \  raise ValueError(\"Probability wrong: \" + str(tmp[0]) + \"!=\" + str(" ++ pyVal outProb ++ ") + \"in test case " ++ name ++ "\")\n\
    \if tmp[0] != 0 and tmp[1][0] != " ++ pyVal outDim ++ ":\n\
    \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1][0]) + \"/=\" + str(" ++ pyVal outDim ++ ") + \"in test case " ++ name ++ "\")\n\
    \") tcs)
  where 
    (_, _, exampleParams, _, _) = unpackTestCase (head tcs)
    unpackTestCase (ProbTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    unpackTestCase (CumulTestCase name sample params (outProb, outDim)) = (name, sample, params, outProb, outDim)
    mainName (ProbTestCase _ _ _ _) = "main.forward"
    mainName (CumulTestCase _ _ _ _) = "main.integrate"

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
-- venv path, then @python3@; if none imports torch the whole group is skipped
-- with a visible note (so a torch-less CI stays green). Torch import is slow, so
-- every eligible program runs in one shared interpreter process.
batchedPythonTests :: IO TestTree
batchedPythonTests = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  -- Non-neural programs are routed to Python by their .tst header; neural
  -- programs are Interpreter-only there (their networks are undefined in the
  -- emitted code), but batched mode supplies a torch mock (identity, for the
  -- mode-2 verbatim-logit symbols the .tst files pass), so we admit them here
  -- regardless of the Python routing header (design pytorch-tensorizer M2b).
  let entries = [ (takeBaseName pplPath, p, tcs)
                | ((pplPath, _), (p, (bs, slow, tcs))) <- zip files cases
                , not slow, Python `elem` bs || not (null (neurals p)) ]
      eligible = [ (n, src, groups, netNames)
                 | (n, p, tcs) <- entries
                 , let qtcs = filter (\t -> isProbTestCase t || isCumulTestCase t) tcs
                 , not (null qtcs)
                 , let netNames = [nm | (nm, _, _) <- neurals p]
                 , Right env <- [compile defaultCompilerConfig{batched = True} p]
                 , Right srcLines <- [generateFunctionsBatched True env]
                 , Just groups <- [batchGroups (not (null netNames)) qtcs]
                 , let src = intercalate "\n" srcLines ]
  mpy <- findTorchPython
  return $ testGroup "BatchedPython" $ case mpy of
    Nothing ->
      [ testProperty "skipped-no-torch" $ once $ ioProperty $ do
          hPutStrLn stderr "BatchedPython: skipped -- no torch-enabled python found (set NEST_TORCH_PYTHON)."
          return True ]
    Just py ->
      [ testProperty "batched-vs-expected" (once (runBatchedPython py eligible))
      , testProperty "gradients-nan-free" (once (runBatchedGradients py eligible))
      , testProperty "generate-density-matches-expected" (once (runBatchedGenerate py eligible)) ]

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
-- sentinel, a residual @IRConformsTo@/@OpIsAny@, a composite-'MultiValue'
-- @IREnumSum@/@IRIsPossible@, and generate-only recursion — are covered by the
-- synthetic-IR rows in "TestInternals" (@batchedRefusalUnitTests@), because on
-- any real program another guard always fires first.
batchedRefusalTests :: TestTree
batchedRefusalTests = testGroup "BatchedRefusal"
  [ testProperty (prog ++ " -- " ++ needle) (once (refusalRow prog needle))
  | (prog, needle) <- batchedRefusalTable ]

-- | @(corpus program base name, diagnostic substring pinning the construct)@.
-- The substring names the offending IR node rather than quoting prose, so a
-- reworded diagnostic does not break a row, but a *different* refusal firing
-- first does. Every row was read off the actual diagnostic
-- (@stack run -- -i FILE --batched compile -l python@ — note @--batched@ is a
-- global flag and must precede the @compile@ subcommand).
batchedRefusalTable :: [(String, String)]
batchedRefusalTable =
  -- lists
  [ ("list",                      "list head (IRHead)")
  , ("headTail",                  "list construction (IRCons)")
  , ("listLiteralDeconstruction", "list tail (IRTail)")
  , ("map",                       "list map (IRMap)")
  -- Either: constructors, destructors, predicates
  , ("either_const",              "Either constructor (IRLeft)")
  , ("either_isleft",             "Either constructor (IRRight)")
  , ("nestedDeconstruction",      "Either destructor (IRFromLeft)")
  , ("eitherDeconstruction",      "Either destructor (IRFromRight)")
  , ("either",                    "Either predicate (IRIsLeft)")
  , ("either_fromLeft",           "Either predicate (IRIsRight)")
  -- a neural decoder's own Either-shaped output: the refused method is a
  -- decoder group's forward, not main's
  , ("eitherNeural",              "eitherNeural_auto's forward")
  -- ADT declarations: the bail at the top of 'generateFunctionsBatched'
  , ("adt",                       "ADT declarations are not in the tensor fragment")
  , ("adtNeuralCounting",         "ADT declarations are not in the tensor fragment")
  -- prob/integ recursion: a cycle found by 'checkCallGraph'
  , ("dice",                      "dice_prob reaches dice_prob recursively")
  , ("gaussList",                 "main_prob reaches main_prob recursively")
  -- a prob/integ path reaching a method batched mode does not emit
  , ("factorial",                 "calls factorial_gen, which is not a forward/integrate method")
  , ("flip",                      "calls flip_gen, which is not a forward/integrate method")
  -- the marginal ANY sentinel
  , ("sndCall",                   "marginal ANY sentinel (IRConst VAny)")
  -- an inner lambda that did not reduce, once in each of the three method
  -- bodies (twiceApplication's forward/integrate *do* reduce; only its
  -- generate body keeps the literal lambda -- the accepted cost of generate's
  -- hard refusal rule, see 'generateFunctionsBatched')
  , ("either_arith_inv",          "main's forward uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  , ("injApply",                  "main's integrate uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  , ("twiceApplication",          "main's generate uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  ]

-- | One table row: the program must compile, and only then be refused by the
-- batched backend with a diagnostic containing @needle@.
refusalRow :: String -> String -> Property
refusalRow prog needle = ioProperty $ do
  p <- parseProgram ("testCases/" ++ prog ++ ".ppl")
  return $ case compile defaultCompilerConfig{batched = True} p of
    Left err -> counterexample (prog ++ " failed to compile at all, so this row proves "
                                ++ "nothing about the batched refusal: " ++ err) False
    Right env -> case generateFunctionsBatched True env of
      Right _  -> counterexample ("batched mode accepted " ++ prog
                                  ++ "; expected a refusal mentioning: " ++ needle) False
      Left msg -> counterexample ("batched refusal for " ++ prog ++ " does not mention "
                                  ++ show needle ++ "; actual diagnostic: " ++ msg)
                    (needle `isInfixOf` msg)

-- | A batchable group: all query points sharing the same query kind (prob vs
-- cumulative), rendered into one batched call. 'bgParamExprs' is the Python
-- expression for each positional argument after the sample: a broadcast scalar
-- for a shared non-neural parameter, or a @[B, n]@ tensor for a batched neural
-- symbol (whose per-point value differs across the batch — that variation is
-- the whole point of neural batching).
data BatchGroup = BatchGroup
  { bgIsCumul    :: Bool
  , bgParamExprs :: [String]
  , bgSamples    :: [IRValue]
  , bgExpProb    :: [Double]
  , bgExpDim     :: [Double]
  }

-- | Split a program's prob/cumulative test cases into batchable groups, or
-- 'Nothing' if any sample is not structure-of-arrays batchable (a non
-- float/int/bool/tuple leaf). For a neural program ('isNeural'), all points of
-- a query kind form one group and each per-point symbol argument is batched
-- into a @[B, n]@ tensor; for a non-neural program, points are grouped by
-- identical parameter list and the shared parameters broadcast as scalars.
batchGroups :: Bool -> [TestCase] -> Maybe [BatchGroup]
batchGroups isNeural tcs = mapM build grouped
  where
    keyed = [ q | t <- tcs, Just q <- [asQuery t] ]
    grouped
      | isNeural  = groupBy ((==) `on` (\(c, _, _, _, _) -> c)) keyed
      | otherwise = groupBy ((==) `on` (\(c, ps, _, _, _) -> (c, show ps))) keyed
    build g@((c, _, _, _, _):_) =
      let samples = [s | (_, _, s, _, _) <- g]
          paramRows = [ps | (_, ps, _, _, _) <- g]
      in do _ <- batchLiteral samples
            paramExprs <- if isNeural
              then batchSymParamCols paramRows
              else Just (map pyVal (head paramRows))
            Just BatchGroup { bgIsCumul = c, bgParamExprs = paramExprs, bgSamples = samples
                            , bgExpProb = [ep | (_, _, _, ep, _) <- g]
                            , bgExpDim  = [ed | (_, _, _, _, ed) <- g] }
    build [] = Nothing
    asQuery (ProbTestCase _ s ps (VFloat ep, VFloat ed))  = Just (False, ps, s, ep, ed)
    asQuery (CumulTestCase _ s ps (VFloat ep, VFloat ed)) = Just (True,  ps, s, ep, ed)
    asQuery _ = Nothing

-- | Batch the positional symbol arguments of a neural program across points.
-- Each row is one point's argument list; every argument is a mode-2 verbatim
-- symbol envelope @(2, [logit0, ...])@ (what the neural .tst files pass). We
-- transpose to columns (one per argument position) and stack each column's
-- logit vectors into a @[B, n]@ tensor literal — fed to the identity mock the
-- driver installs for every declared network. 'Nothing' if the rows are ragged
-- or any argument is not a mode-2 envelope.
batchSymParamCols :: [[IRValue]] -> Maybe [String]
batchSymParamCols rows
  | null rows                          = Just []
  | any ((/= length (head rows)) . length) rows = Nothing
  | otherwise = mapM batchSymColumn (transpose rows)

batchSymColumn :: [IRValue] -> Maybe String
batchSymColumn vs = do
  logitRows <- mapM logitsOf vs
  return ("torch.tensor([" ++ intercalate ", " (map renderRow logitRows) ++ "])")
  where
    logitsOf (VTuple (VInt 2) (VList ls)) = Just (toList ls)
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
    numLit (VFloat f) = show f
    numLit (VInt i)   = show (fromIntegral i :: Double)
    numLit _          = "0.0"

-- | Locate a Python interpreter that can import torch: @NEST_TORCH_PYTHON@, then
-- a conventional venv path under @HOME@, then @python3@. Returns the first whose
-- @import torch@ succeeds.
findTorchPython :: IO (Maybe FilePath)
findTorchPython = do
  envPy <- lookupEnv "NEST_TORCH_PYTHON"
  home  <- lookupEnv "HOME"
  let candidates = maybe [] (:[]) envPy
                ++ maybe [] (\h -> [h ++ "/.cache/nest/torchvenv/bin/python"]) home
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

-- | Run every eligible program's batched code in one shared torch process and
-- assert every batched query point matches its expected value.
runBatchedPython :: FilePath -> [(String, String, [BatchGroup], [String])] -> Property
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
  let script = "import sys\nsys.path.insert(0, " ++ show cwd ++ ")\n" ++ batchedDriver eligible
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
batchedDriver :: [(String, String, [BatchGroup], [String])] -> String
batchedDriver eligible = unlines $
  [ "import torch, sys, traceback"
  , "from pythonLibBatched import T"  -- for structure-of-arrays tuple sample batches
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
      [ "    _ns[" ++ show nm ++ "] = (lambda s: s)" | nm <- netNames ] ++
      [ "    _main = _ns['main']" ] ++
      concatMap (groupCall name) groups ++
      [ "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    groupCall name (BatchGroup isCumul paramExprs samples expP expD) =
      let method = if isCumul then "integrate" else "forward"
          xs = case batchLiteral samples of Just s -> s; Nothing -> "None"
          paramStr = concatMap (", " ++) paramExprs
          call = "_main." ++ method ++ "(" ++ xs ++ paramStr ++ ")"
      in [ "    _cmp(" ++ show name ++ ", " ++ show method ++ ", " ++ call
           ++ ", " ++ pyFloatList expP ++ ", " ++ pyFloatList expD ++ ")" ]
    pyFloatList xs = "[" ++ intercalate ", " (map show xs) ++ "]"

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
runBatchedGradients :: FilePath -> [(String, String, [BatchGroup], [String])] -> Property
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
-- neural-generate-parity) to cover decoder-own sampling (categorical/Gaussian)
-- and cross-decoder composition (e.g. MNIST addition).
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
-- point supplies its own decoder input symbol, per the corpus's mode-2
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
runBatchedGenerate :: FilePath -> [(String, String, [BatchGroup], [String])] -> Property
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
                            , isScalarSample s ]
             , not (null points) ]
    neuralProbes = [ (name, src, netNames, bgParamExprs g, points)
             | (name, src, groups, netNames) <- eligible
             , not (null netNames)
             , (g:_) <- [[gr | gr <- groups, not (bgIsCumul gr)]]
             , let points = [ (pyVal s, ep, ed, i)
                            | (i, s, ep, ed) <- zip4 [0 :: Int ..] (bgSamples g) (bgExpProb g) (bgExpDim g)
                            , isScalarSample s ]
             , not (null points) ]

-- | Is this sample a bare scalar leaf (not a tuple)? 'isNum'/'isBoolV' already
-- cover exactly float/int/bool between them (see 'batchLiteral').
isScalarSample :: IRValue -> Bool
isScalarSample v = isNum v || isBoolV v

-- | The single Python script for the generate check: for each non-neural
-- program, draw one shared large batch and test it against every query
-- point's epsilon-window density estimate; for each neural program, draw a
-- fresh per-point batch (the point's own decoder symbol, repeated) and test
-- that point alone. Single-shot rather than retried -- the batch size is
-- fixed large enough, and the seed is pinned, to keep this non-flaky.
generateDriver :: [(String, String, [(String, Double, Double)])]
               -> [(String, String, [String], [String], [(String, Double, Double, Int)])]
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
      [ "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    -- Each point supplies its own decoder symbol (a row of the group's [B, n]
    -- symbol tensor, per argument position), so it needs its own generate call
    -- and its own arity check (the signature is the same for every point of a
    -- program, but checking it once per point keeps this block symmetric with
    -- 'block' and costs nothing at this scale).
    neuralBlock (name, src, netNames, paramExprs, points) =
      [ "try:"
      , "    _ns = {}"
      , "    exec(" ++ show src ++ ", _ns)"
      ] ++
      [ "    _ns[" ++ show nm ++ "] = (lambda s: s)" | nm <- netNames ] ++
      [ "    _main = _ns['main']"
      , "    _sig = inspect.signature(_main.generate)"
      , "    if len(_sig.parameters) != " ++ show (length paramExprs + 1) ++ ":"
      , "        skipped += 1"
      , "    else:"
      ] ++
      concatMap (neuralPointCheck name paramExprs) points ++
      [ "except Exception as _e:"
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
end2endTests :: IO TestTree
end2endTests = do
  compiled <- loadEnd2EndCases (\slow -> not slow)
  return $ buildEnd2EndTree "End2End" True compiled

-- | The slow-only twin of end2endTests: same Interpreter/Unoptimized checks,
-- restricted to `slow`-headered programs. Julia/Python/Normalization are
-- skipped since these programs are Interpreter-only by design (see their
-- .tst headers).
slowEnd2EndTests :: IO TestTree
slowEnd2EndTests = do
  compiled <- loadEnd2EndCases id
  return $ buildEnd2EndTree "End2End (slow)" False compiled

-- | Parses and compiles (default -O2, and -O0 to check the optimizer is
-- harmless) every testCases/*.ppl+.tst pair whose `slow` header (see
-- TestCaseParser) satisfies `keep`.
loadEnd2EndCases :: (Bool -> Bool)
                  -> IO [(String, Program, Either CompilerError IREnv, [Backend], [TestCase])]
loadEnd2EndCases keep = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  return [ (takeBaseName pplPath, p, compile defaultCompilerConfig p, bs, tcs)
         | ((pplPath, _), (p, (bs, slow, tcs))) <- zip files cases, keep slow ]

-- | Builds the standard End2End test groups from already-loaded/compiled
-- cases. includeBackends controls whether the Normalization/Julia/Python
-- groups are built (skipped for the slow subset, whose programs are
-- Interpreter-only by design).
buildEnd2EndTree :: String -> Bool
                  -> [(String, Program, Either CompilerError IREnv, [Backend], [TestCase])]
                  -> TestTree
buildEnd2EndTree groupName includeBackends compiledCases = testGroup groupName $
    [ testGroup "Interpreter"
        [ testProperty n (once $ conjoin (map (testInterpreter p c) tcs)) | (n, p, c, bs, tcs) <- compiledCases, Interpreter `elem` bs ]
    -- Re-run every interpreter case at -O0 to confirm the optimizer changes no answer.
    , testGroup "Interpreter Unoptimized"
        [ testProperty n (once $ conjoin (map (testInterpreter p c) tcs)) | (n, p, _, bs, tcs) <- compiledCases, Interpreter `elem` bs
        , let c = compile defaultCompilerConfig{optimizerLevel = 0} p ]
    ] ++
    ( if not includeBackends then [] else
      let queryTestCases = [(n, p, c, bs, filter (\x -> isProbTestCase x || isCumulTestCase x) tcs) | (n, p, c, bs, tcs) <- compiledCases]
          nonNeuralsQueries b = [(n, c, tcs) | (n, p, c, bs, tcs) <- queryTestCases, b `elem` bs, null (neurals p), not (null tcs)]
          neuralP = [(n, p, c) | (n, p, c, bs, _) <- compiledCases, Interpreter `elem` bs, not (null (neurals p))]
      in [ testGroup "Normalization"
             [ testProperty n (once $ discreteProbsNormalized p c) | (n, p, c) <- neuralP ]
         -- All Julia programs share one batch file (and one julia process) to amortize startup.
         , testProperty "Julia" (once $ testJuliaAll [(c, tcs) | (_, c, tcs) <- nonNeuralsQueries Julia])
         , testGroup "Python"
             [ testProperty n (once $ testPython c tcs) | (n, c, tcs) <- nonNeuralsQueries Python ]
         ]
    )
