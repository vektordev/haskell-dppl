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
import Data.List (intercalate, nub, isInfixOf, transpose)
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
import TestTolerances (probTolerance, encodeSlotTolerance, normalizationTolerance)
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
      , testProperty "refusal-diagnostic" (once (ioProperty (return refusalProp))) ]

-- | The batched backend must refuse a program outside the tensor fragment with
-- a diagnostic naming the offending construct. `coin` (whose main, `coin ++
-- coin`, builds a list) is a stable negative.
refusalProp :: Property
refusalProp = ioProperty $ do
  p <- parseProgram "testCases/coin.ppl"
  return $ case compile defaultCompilerConfig{batched = True} p of
    Left err -> counterexample ("coin failed to compile at all: " ++ err) False
    Right env -> case generateFunctionsBatched True env of
      Right _  -> counterexample "batched mode accepted list-valued coin; expected a fragment refusal" False
      Left msg -> counterexample ("refusal diagnostic did not mention the tensor fragment: " ++ msg)
                    ("tensor fragment" `isInfixOf` msg && "list" `isInfixOf` msg)

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
    isTup (VTuple _ _) = True
    isTup _ = False
    isBoolV (VBool _) = True
    isBoolV _ = False
    isNum (VFloat _) = True
    isNum (VInt _) = True
    isNum _ = False
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
