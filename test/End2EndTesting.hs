{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Directory (listDirectory, getCurrentDirectory)
import System.FilePath (stripExtension, isExtensionOf, takeBaseName)
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

testInterpreter :: Program -> Either CompilerError IREnv -> TestCase -> Property
testInterpreter p compiledE (ProbTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runProbC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VTuple (VFloat outProb) (VFloat outDim))) -> 
      counterexample ("Probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < probTolerance) .&&.
        counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
    Right (Right x) -> counterexample ("Output of test case " ++ name ++ " is not a probability tuple: " ++ show x) False
    Right (Left err) -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
    Left err -> counterexample ("Test case " ++ name ++ " raised an exception: " ++ show err) False
testInterpreter p compiledE (CumulTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = ioProperty $ do
  result <- try (let r = compiledE >>= \c -> runIntegC p c params sample in evaluate (length (show r)) >> return r) :: IO (Either SomeException (Either CompilerError (GenericValue IRExpr)))
  return $ case result of 
    Right (Right (VTuple (VFloat outProb) (VFloat outDim)) )-> 
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
      Right (VTuple (VFloat resP) (VFloat resDim))
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
          Right (VTuple (VFloat sampleP) (VFloat sampleDim))
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
    prob (VTuple (VFloat p) _) = p
    dim (VTuple _ d) = d

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
    \if abs(tmp[0] - " ++ pyVal outProb ++ ") > " ++ show probTolerance ++ ":\n\
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
