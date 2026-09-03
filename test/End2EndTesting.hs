{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Directory (listDirectory, getCurrentDirectory)
import System.FilePath (stripExtension, isExtensionOf, takeBaseName)
import System.IO.Temp (withSystemTempFile)
import System.IO (hPutStr, hClose, hPutStrLn, stderr)
import System.Environment (lookupEnv)
import System.Process (createProcess, proc, readProcessWithExitCode, waitForProcess)
import System.Exit
import Data.List (groupBy)
import Data.Function (on)
import Control.Monad.Random
import Data.Maybe
import Data.List (intercalate, nub, isInfixOf, isPrefixOf, transpose, zip4)
import Data.Text (replace, pack, unpack)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.CodeGenJulia
import SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import SPLL.Parser (tryParseProgram)
import TestCaseParser
import TestTolerances (probTolerance, writeLogitsSlotTolerance, normalizationTolerance, samplingTolerance)
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.AutoNeural (makePartitionPlan, planIndexOf, resolvePartitionAnnotation, PartitionPlan)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Analysis (annotateEnumsProg)
import Data.Foldable (toList)
import Test.QuickCheck hiding (sample, verbose)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Control.Exception (try, evaluate, throwIO, SomeException)
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import IRInterpreter (generateRand, generateDet)
import MockNN (evaluateMockNN)

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
--
-- Each program is compiled once per config here, not once per query point:
-- 'compile' depends only on the (program, config) pair, so re-running it for
-- every row of a multi-row .tst file was pure waste -- measured at ~1100
-- corpus query rows against ~200 eligible programs, that was ~5x more compiles
-- than the differential needs, and this group's own cost (~25s) came from
-- exactly that.
selectPassDifferentialTests :: IO TestTree
selectPassDifferentialTests = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  let entries = [ (takeBaseName pplPath, p, tcs)
                | ((pplPath, _), (p, (bs, slow, tcs))) <- zip files cases
                , not slow, Interpreter `elem` bs ]
  return $ testGroup "SelectPassNoOp"
    [ testProperty n (once $ conjoin (map (selectNoOp p scalarEnv batchedEnv) tcs))
    | (n, p, tcs) <- entries
    , let scalarEnv  = compile defaultCompilerConfig p
    , let batchedEnv = compile defaultCompilerConfig{batched = True} p ]

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
-- (see CLAUDE.md, design inference-result-side-channels).
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
-- special case (see CLAUDE.md's ".tst dim expectations" note, task
-- tst-dim-unasserted-at-zero-probability) -- and not checked at all for
-- 'Impossible', which asserts prob=0 and imposs=True instead of a dim.
checkExpectation :: String -> String -> Expectation -> Double -> Double -> IRValue -> Property
checkExpectation probLabel name (Possible (VFloat expectedProb) (VFloat expectedDim) mImp) outProb outDim res =
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
  let mockedParams = [VTuple (VInt 1) (VTuple par (VInt seed)) | (par, seed) <- zip params [0..]]
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
          gens = map (\args -> generateRand (neurals p) (writeLogitsDecls p) compiled (map IRConst args) genExpr) randomParamsForSamples
          pSamples = evalRand (sequence gens) (mkStdGen 42)
          uniqueSamples = nub pSamples
          counts = map (\u -> length (filter (== u) pSamples)) uniqueSamples
      -- The per-sample prob queries are independent and pure; force them in parallel.
      probResults <- parEval (map (\sam -> generateDet (neurals p) (writeLogitsDecls p) compiled (map IRConst (sam:params)) probExpr) uniqueSamples)
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
    prob (VProbDim pr _) = pr
    prob v = error ("not a probability result: " ++ show v)
    dim :: IRValue -> IRValue
    dim (VProbDim _ d) = VFloat d
    dim v = error ("not a probability result: " ++ show v)

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
  | not (null explicitArgs) = if null (neurals p) then explicitArgs else map spike explicitArgs
  | null (neurals p)        = []
  | otherwise               = replicate (progParameterCount p) (VTuple (VInt 0) (VInt 42))
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
-- its mock straight off a lambda parameter.
readNNOfVar :: Expr -> [(String, String)]
readNNOfVar (Expr _ e) = case e of
  ReadNN name (Expr _ (Var v)) -> (v, name) : rest
  _                             -> rest
  where rest = concatMap readNNOfVar (toList e)

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

-- | Per parameter position of 'main', the plan of the network it feeds
-- directly (as @net(paramVar)@), or 'Nothing' for a position that feeds no
-- network.
paramNetworkPlans :: Program -> [Maybe PartitionPlan]
paramNetworkPlans p = [ networkPlan p <$> lookup v varToNet | v <- mainParamNames p ]
  where varToNet = readNNOfVar (mainBinding (functions p))

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
resolveNeuralParams :: Program -> [IRValue] -> [IRValue]
resolveNeuralParams p params = zipWith resolve (paramNetworkPlans p) params
  where
    resolve (Just plan) v = evaluateMockNN plan v
    resolve Nothing     v = v

-- | 'resolveNeuralParams' applied to a query test case's own parameter list.
-- A no-op on a non-neural program (every parameter position resolves to
-- 'Nothing') and on any non-prob/cumulative case.
resolveNeuralTestCase :: Program -> TestCase -> TestCase
resolveNeuralTestCase p (ProbTestCase n s ps e)  = ProbTestCase  n s (resolveNeuralParams p ps) e
resolveNeuralTestCase p (CumulTestCase n s ps e) = CumulTestCase n s (resolveNeuralParams p ps) e
resolveNeuralTestCase _ tc                       = tc

-- | A program's declared network names, in declaration order -- what the
-- Julia/Python harnesses install identity mocks for.
networkNames :: Program -> [String]
networkNames p = [ nm | (nm, _, _) <- neurals p ]

-- | The network names attached to each program feed a per-module identity
-- mock (@net(sym) = sym@, task route-neural-programs-to-julia-python-backends):
-- the .tst rows' mock-NN parameters are already resolved to raw logit vectors
-- by 'resolveNeuralTestCase' before they reach here, so the network itself
-- only has to be pass-through. Empty for a non-neural program.
testJuliaAll :: [(Either CompilerError IREnv, [TestCase], [String])] -> Property
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
        (_, _, _, handle) <- createProcess (proc "julia" [tmpPath])
        waitForProcess handle
      return $ case code of
        ExitSuccess -> True === True
        ExitFailure _ -> counterexample "Julia batch test failed. See Julia error message above." False

-- The program goes to a temp file rather than @python3 -c@, matching
-- 'testJuliaAll'. An emitted program is not argv-sized: several -O0 compiles
-- exceed the kernel's per-argument limit and the spawn fails with "Argument
-- list too long" -- a harness failure indistinguishable, in the report, from
-- the program being wrong.
--
-- @netNames@ (empty for a non-neural program) gets one identity-mock
-- definition apiece -- see 'testJuliaAll'\'s note.
testPython :: [String] -> Either CompilerError IREnv -> [TestCase] -> Property
testPython netNames compiledE tc = ioProperty $ do
  case compiledE of
    Left err -> return $ counterexample err False
    Right compiled -> do
      let src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True compiled)
          mockDefs = concatMap (\nm -> "def " ++ nm ++ "(s):\n    return s\n") netNames
      -- Run as a file, so sys.path[0] is the temp dir rather than the project;
      -- pythonLib has to be put back on the path explicitly.
      projectDir <- getCurrentDirectory
      code <- withSystemTempFile "spll_test.py" $ \tmpPath tmpHandle -> do
        hPutStr tmpHandle ("import sys\nsys.path.insert(0, " ++ show projectDir ++ ")\n"
                           ++ mockDefs ++ pythonTestCode src tc)
        hClose tmpHandle
        (_, _, _, handle) <- createProcess (proc "python3" [tmpPath])
        waitForProcess handle
      case code of
        ExitSuccess -> return $ True === True
        ExitFailure _ -> return $ counterexample ("Python test " ++ testCaseName (head tc) ++ " failed. See Python error message") False

juliaBatchTestCode :: FilePath -> [(String, [TestCase], [String])] -> String
juliaBatchTestCode projectDir allCases =
  "include(\"" ++ projectDir ++ "/juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n" ++
  concatMap (\(idx, (src, tcs, nets)) ->
    let modName = "Prog" ++ show (idx :: Int)
    in "module " ++ modName ++ "\nusing ..JuliaSPPLLib\n" ++
       concatMap (\nm -> nm ++ "(s) = s\n") nets ++
       src ++ "\nend\n" ++
       juliaModuleTestCases modName tcs
  ) (zip [0..] allCases)

-- The compiled result is (prob, (dim, impossible)) -- the trailing field is the
-- internal impossibility flag (design inference-result-side-channels), which is
-- not stripped from the emitted code, hence the nested dim access below. The
-- dim check line is emitted only when the .tst row's 'Expectation' actually
-- states a dim ('Possible') -- unconditionally, not gated on the runtime
-- probability any more -- and omitted entirely for 'Impossible' rows, which
-- have none to check (see CLAUDE.md's ".tst dim expectations" note).
juliaModuleTestCases :: String -> [TestCase] -> String
juliaModuleTestCases modName tcs =
  modName ++ ".main_gen(" ++ intercalate ", " (map jVal exampleParams) ++ ")\n" ++
  concat (map (\tc ->
    let (name, sample, params, expct) = unpackTestCase tc
        call = modName ++ "." ++ mainName tc ++ "(" ++ jVal sample ++ ", " ++ intercalate ", " (map jVal params) ++ ")"
        outProb = VFloat (expectationProb expct)
        dimCheck = case expectationDim expct of
          Nothing -> ""
          Just d  ->
            "if tmp[2][1] != " ++ juliaVal (VFloat d) ++ "\n\
            \  error(\"Dimensionality wrong: \" * string(tmp[2][1]) * \"/=\" * string(" ++ juliaVal (VFloat d) ++ ") * \"in test case " ++ name ++ "\")\n\
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
    -- Dim check line emitted only when the .tst row's 'Expectation' states a
    -- dim ('Possible') -- unconditionally, not gated on the runtime
    -- probability any more -- and omitted for 'Impossible' rows, which have
    -- none to check (see CLAUDE.md's ".tst dim expectations" note).
    pyCase tc =
      let (name, sample, params, expct) = unpackTestCase tc
          outProb = VFloat (expectationProb expct)
          dimCheck = case expectationDim expct of
            Nothing -> ""
            Just d  ->
              "if tmp[1][0] != " ++ pyVal (VFloat d) ++ ":\n\
              \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1][0]) + \"/=\" + str(" ++ pyVal (VFloat d) ++ ") + \"in test case " ++ name ++ "\")\n"
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
-- venv path, then @python3@; if none imports torch the value differential is
-- skipped with a visible note (so a torch-less CI stays green). Torch import is
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
batchedPythonFixtures :: IO ( [(String, Either String (String, [BatchGroup], [String]))]
                             , [String]
                             , [(String, String, [BatchGroup], [String])]
                             , [(String, String, [BatchGroup], [String])]
                             , ([(String, String, [BatchGroup], [String])], [String])
                             , [(String, String, [BatchGroup], [String])]
                             , Maybe FilePath )
batchedPythonFixtures = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  -- `slow`-headered programs stay out of batched coverage by construction, the
  -- same way they stay out of the Interpreter groups.
  let entries = [ (takeBaseName pplPath, p, bs, tcs)
                | ((pplPath, _), (p, (bs, slow, tcs))) <- zip files cases
                , not slow ]
      -- The topK differential (M5) recompiles the `batched`-declaring programs
      -- at a cutoff, so it draws from the same declaration, not from a second
      -- eligibility condition of its own.
      batchedDeclared = [ (n, p, tcs) | (n, p, bs, tcs) <- entries, Batched `elem` bs ]
      denseNames = [ n | (n, _, bs, _) <- entries, Dense `elem` bs ]
  declared <- mapM (\(n, p, _, tcs) -> (,) n <$> batchedEligibility p tcs)
                   [ e | e@(_, _, bs, _) <- entries, Batched `elem` bs ]
  undeclared <- mapM (\(n, p, _, tcs) -> (,) n <$> batchedEligibility p tcs)
                     [ e | e@(_, _, bs, _) <- entries, Batched `notElem` bs ]
  let eligible = [ (n, src, gs, nets) | (n, Right (src, gs, nets)) <- declared ]
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
      denseTopK = [ e | e@(n, src, _, _) <- fst topkEligible
                      , takeWhile (/= '@') n `elem` denseNames
                      , not (null (denseEntryPoints src)) ]
  mpy <- findTorchPython
  return (declared, gained, eligible, denseDeclared, topkEligible, denseTopK, mpy)

-- | The cheap, always-on half of the batched-mode differential: pure-Haskell
-- eligibility bookkeeping (no torch, no subprocess) plus the two value
-- differentials cheap enough to run on every `stack test`
-- ('runBatchedPython'/'runBatchedGradients'/'runBatchedGenerate'/
-- 'runBatchedDense' False -- each well under 5s). The topK-threshold
-- differentials live in 'slowBatchedPythonTests' instead -- see there for why.
batchedPythonTests :: IO TestTree
batchedPythonTests = do
  (declared, gained, eligible, denseDeclared, _, _, mpy) <- batchedPythonFixtures
  let refused  = [ (n, msg) | (n, Left msg) <- declared ]
      denseNames = map (\(n, _, _, _) -> n) denseDeclared
      denseRefused = [ n | n <- denseNames
                         , n `notElem` [ m | (m, src, _, _) <- eligible, not (null (denseEntryPoints src)) ] ]
      denseGained = [ n | (n, src, _, _) <- eligible
                        , n `notElem` denseNames, not (null (denseEntryPoints src)) ]
  return $ testGroup "BatchedPython" $
    [ testProperty "declared-batched-eligible" (once (declaredEligibleProp (length declared) refused))
    , testProperty "eligibility-gain-note" (once (gainNoteProp gained))
    , testProperty "declared-dense-eligible" (once (declaredDenseProp (length denseNames) denseRefused))
    , testProperty "dense-eligibility-gain-note" (once (denseGainNoteProp denseGained))
    , testProperty "dense-domain-boundary" (once (denseBoundaryProp eligible))
    ] ++ case mpy of
      Nothing ->
        [ testProperty "skipped-no-torch" $ once $ ioProperty $ do
            hPutStrLn stderr "BatchedPython: value differential skipped -- no torch-enabled python found (set NEST_TORCH_PYTHON)."
            return True ]
      Just py ->
        [ testProperty "batched-vs-expected" (once (runBatchedPython py eligible))
        , testProperty "gradients-nan-free" (once (runBatchedGradients py eligible))
        , testProperty "generate-density-matches-expected" (once (runBatchedGenerate py eligible))
        , testProperty "dense-matches-expected" (once (runBatchedDense False py denseDeclared)) ]

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
slowBatchedPythonTests :: IO TestTree
slowBatchedPythonTests = do
  (_, _, _, _, topkEligible, denseTopK, mpy) <- batchedPythonFixtures
  return $ testGroup "BatchedPython (slow)" $ case mpy of
    Nothing -> []
    Just py ->
      [ testProperty "dense-inherits-topk" (once (runBatchedDense True py denseTopK))
      , testProperty "topk-is-per-element" (once (runBatchedTopK py topkEligible)) ]

-- | Everything the batched differential needs from one corpus program, or a
-- diagnostic saying why batched mode cannot take it: the three eligibility
-- conditions (a batched 'compile', a 'generateFunctionsBatched' emission, and
-- batchable query samples) plus the precondition that the @.tst@ file has
-- prob/cumulative points at all. Runs in IO so that a compiler @error@ (rather
-- than a @Left@) becomes a named diagnostic instead of derailing the group.
batchedEligibility :: Program -> [TestCase] -> IO (Either String (String, [BatchGroup], [String]))
batchedEligibility p tcs = do
  r <- try (evaluate (force (go p tcs))) :: IO (Either SomeException (Either String (String, [BatchGroup], [String])))
  return $ either (\e -> Left ("crashed while compiling for batched mode: " ++ show e)) id r
  where
    force res = case res of
      Left msg              -> length msg `seq` res
      Right (src, gs, nets) -> length src `seq` length gs `seq` length nets `seq` res
    go prog cs = do
      let qtcs = filter (\t -> isProbTestCase t || isCumulTestCase t) cs
          netNames = [nm | (nm, _, _) <- neurals prog]
      if null qtcs
        then Left "the .tst file declares no p()/cdf() query points to batch"
        else Right ()
      env <- compile defaultCompilerConfig{batched = True} prog
      srcLines <- generateFunctionsBatched True env
      groups <- maybe (Left "query samples are not structure-of-arrays batchable") Right
                      (batchGroups (not (null netNames)) qtcs)
      return (intercalate "\n" srcLines, groups, netNames)

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
-- @IREnumSum@/@IRIsPossible@, and generate-only recursion — are covered by the
-- synthetic-IR rows in "TestInternals" (@batchedRefusalUnitTests@), because on
-- any real program another guard always fires first.
batchedRefusalTests :: TestTree
batchedRefusalTests = testGroup "BatchedRefusal" $
  [ testProperty (prog ++ " -- " ++ needle) (once (refusalRow prog needle))
  | (prog, needle) <- batchedRefusalTable ]
  ++ [ testProperty (prog ++ " -- scalar advisory reports eligible")
         (once (ioProperty (advisoryRow prog Nothing <$> parseProgram ("testCases/" ++ prog ++ ".ppl"))))
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
  -- bucketing does not rescue: a list *constant* carrying per-element data
  -- (`listLiteralDeconstruction`'s `[1.0, 2.0]`, the same shape as the
  -- enumeration `SPLL.AutoNeural.indexOf` builds, see task
  -- batched-bool-enum-index) and IRMap.
  [ ("listLiteralDeconstruction", "constant with no batched representation (VList")
  , ("map",                       "list map (IRMap)")
  -- Either. Since heterogeneous M2 the tag is *structure*: it is part of the
  -- bucket signature, so the constructors, destructors and predicates are all
  -- in the fragment (`either`, `either_const`, `eitherDeconstruction`,
  -- `nestedDeconstruction`, `either_both_cont` are eligible programs now). What
  -- is refused is the dichotomy's other half -- `either_isleft` chooses which
  -- *arm* to build from a coin flip (`if Uniform < 0.4 then left .. else
  -- right ..`), so the sample's structure is per element and there is no bucket
  -- to run it in.
  , ("either_isleft",             "arms have different structure")
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
  -- `recursiveAdt`, `planEnumInline`/`Wide` are eligible programs now. These two
  -- are refused for an unrelated, pre-existing reason: their prob path evaluates
  -- a deterministic argument by *generating* it, and generate is a separate
  -- artifact batched mode does not call into.
  , ("adt",                       "calls func_gen, which is not a forward/integrate method")
  , ("adtNeuralCounting",         "calls countRed3_gen, which is not a forward/integrate method")
  -- prob/integ recursion. Structure-directed recursion is admitted since M1
  -- (its depth is uniform within a shape bucket, so it runs unchanged over [B]
  -- leaves -- `gaussList` is an eligible program now, checked in
  -- 'batchedPythonTests'); what stays refused is *value*-dependent recursion,
  -- where eager both-arm select semantics would not terminate.
  -- M4 (ANY-ness is a structural marker) makes one of dice's recursive call
  -- sites newly recognised as guarded (it sits under an isAny check, which is
  -- now correctly structural) -- true and unrelated to why it stays refused,
  -- which is the *other* reason 'recOffenders' still finds for it: the call
  -- does not descend into the tail of a list argument, since dice's recursion
  -- is genuinely value-dependent (a coin flip), not structure-directed.
  , ("dice",                      "calls dice_prob recursively without descending into the tail of a list argument")
  -- a prob/integ path reaching a method batched mode does not emit
  , ("factorial",                 "calls factorial_gen, which is not a forward/integrate method")
  , ("flip",                      "calls flip_gen, which is not a forward/integrate method")
  -- an inner lambda that did not reduce, once in each of the three method
  -- bodies (twiceApplication's forward/integrate *do* reduce; only its
  -- generate body keeps the literal lambda -- the accepted cost of generate's
  -- hard refusal rule, see 'generateFunctionsBatched')
  , ("either_arith_inv",          "main's forward uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  , ("injApply",                  "main's integrate uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  , ("twiceApplication",          "main's generate uses a construct outside the tensor fragment: inner lambda (IRLambda)")
  ]

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
          Nothing -> do
            hPutStrLn stderr "batched ADT-cdf NaN guard: runtime check skipped -- no torch-enabled python found (set NEST_TORCH_PYTHON)."
            return (property True)
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
      in do _ <- batchSamples samples
            paramExprs <- if isNeural
              then batchSymParamCols paramRows
              else Just (map pyVal (head paramRows))
            Just BatchGroup { bgIsCumul = c, bgParamExprs = paramExprs
                            , bgParamRows = paramRows, bgSamples = samples
                            , bgExpProb = [ep | (_, _, _, ep, _) <- g]
                            , bgExpDim  = [ed | (_, _, _, _, ed) <- g] }
    build [] = Nothing
    -- 'Impossible' rows (no stated dim) fall through to the final wildcard and
    -- are simply not batched, the same treatment 'containsAnyExceptV' above
    -- gives a 'VAnyExcept'-carrying query point.
    asQuery (ProbTestCase _ s ps (Possible (VFloat ep) (VFloat ed) _))  = Just (False, ps, s, ep, ed)
    asQuery (CumulTestCase _ s ps (Possible (VFloat ep) (VFloat ed) _)) = Just (True,  ps, s, ep, ed)
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

-- | The Python form of a group's samples, or 'Nothing' if they are not
-- batchable at all (a @VAnyExcept@ sample, or a leaf that is neither numeric,
-- bool, nor a structure of those).
batchSamples :: [IRValue] -> Maybe SampleBatch
batchSamples vs
  | any containsAnyExceptV vs  = Nothing
  | any containsStructureV vs =
      Just (Bucketed ("[" ++ intercalate ", " (map pyVal vs) ++ "]")
                     (length (nub (map shapeSig vs))))
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

-- | The Haskell twin of @pythonLibBatched.signature@: the sample's structural
-- skeleton with every scalar leaf erased, ANY-ness (M4) checked first exactly
-- as @signature@ checks @isAny@ first (a bare 'VAny' or an @AnyList@ nested
-- under a concrete constructor is its own bucket, not conflated with the
-- concrete case at that position). Used only to predict the bucket count.
shapeSig :: IRValue -> String
shapeSig VAny                 = "ANY"
shapeSig (VList AnyList)      = "ANY"
shapeSig (VList l)            = "L(" ++ intercalate "," (map shapeSig (toList l)) ++ ")"
shapeSig (VTuple a b)         = "T(" ++ shapeSig a ++ "," ++ shapeSig b ++ ")"
shapeSig (VEither (Left v))   = "L?(" ++ shapeSig v ++ ")"
shapeSig (VEither (Right v))  = "R?(" ++ shapeSig v ++ ")"
shapeSig _                    = "x"

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
batchedDriver :: Bool -> [(String, String, [BatchGroup], [String])] -> String
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
      [ "    _ns[" ++ show nm ++ "] = (lambda s: s)" | nm <- netNames ] ++
      [ "    _main = _ns['main']" ] ++
      concatMap (groupCall name) groups ++
      [ "except Exception as _e:"
      , "    failures.append(" ++ show name ++ " + ': exception ' + repr(_e) + '\\n' + traceback.format_exc())"
      ]
    groupCall name (BatchGroup isCumul paramExprs _ samples expP expD) =
      let method = if isCumul then "integrate" else "forward"
          -- A topK-compiled prob function takes an accumulated-probability
          -- parameter right after the sample (see 'compiledWithTopK'); seed it
          -- with 1.0 at the query root, exactly as the interpreter driver does.
          accStr = if accArg && not isCumul then ", 1.0" else ""
          paramStr = concatMap (", " ++) paramExprs
          (bucketCheck, call) = case batchSamples samples of
            Just (SoA xs) ->
              ([], "_main." ++ method ++ "(" ++ xs ++ accStr ++ paramStr ++ ")")
            -- Heterogeneous samples go through the host bucketing wrapper, and
            -- the bucket count is asserted: the M1 acceptance criterion is that
            -- the wrapper makes exactly one kernel call per distinct shape, not
            -- merely that the numbers come out right.
            Just (Bucketed xs n) ->
              ( [ "    _bucket_count(" ++ show name ++ ", " ++ xs ++ ", " ++ show n ++ ")" ]
              , "bucketed(_main." ++ method ++ ", " ++ xs ++ accStr ++ paramStr ++ ")" )
            Nothing -> ([], "None")
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
denseBoundaryProp :: [(String, String, [BatchGroup], [String])] -> Property
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
runBatchedDense :: Bool -> FilePath -> [(String, String, [BatchGroup], [String])] -> Property
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

denseDriver :: Bool -> [(String, String, [BatchGroup], [String])] -> String
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
  -- A topK-compiled prob function takes the accumulated probability right after
  -- the sample; seed it with 1.0 at the query root, as every other driver does.
  -- It is a scalar, so it broadcasts over the domain batch as well as over the
  -- query batch -- which is exactly why dense mode needs no topK plumbing.
  , "ACC = " ++ (if accArg then "(1.0,)" else "()")
  , "def _dense(name, method, main, samples, exp_p, exp_d, packed=None):"
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
      [ "    _ns[" ++ show nm ++ "] = (lambda s: s)" | nm <- netNames ] ++
      [ "    _main = _ns['main']" ] ++
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
           ++ ", " ++ pyFloatList (bgExpProb g) ++ ", " ++ pyFloatList (bgExpDim g) ++ packed ++ ")"
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
-- and topK does not apply to it. Input is the @batched@-declaring corpus
-- entries, the same declaration 'batchedPythonTests' filters on — a program
-- whose fragment eligibility is asserted there is silently dropped here if it
-- fails to compile at a cutoff, which is why the non-vacuity assertion below
-- exists.
-- Returns the driver entries plus the number of programs on which the threshold
-- actually bites (some point's pruned value differs from its topK-off value) —
-- the property asserts that is non-zero, so the differential can never quietly
-- degenerate into "topK changed nothing anywhere".
topKEntries :: [(String, Program, [TestCase])] -> ([(String, String, [BatchGroup], [String])], [String])
topKEntries entries = (map fst built, nub [n | ((n, _, _, _), True) <- built])
  where
    -- env0 (the plain default compile, used only to retarget expectations) does
    -- not depend on the threshold, so it is bound once per program -- outside
    -- the per-threshold loop -- rather than once per (program, threshold) pair.
    built =
      [ ((n ++ "@k=" ++ show thresh, src, groups', netNames), bites)
      | (n, p, tcs) <- entries
      , let qtcs = filter isProbTestCase tcs
      , not (null qtcs)
      , let netNames = [nm | (nm, _, _) <- neurals p]
      , Right env0 <- [compile defaultCompilerConfig p]
      , thresh <- topKDiffThresholds
      , let confK = defaultCompilerConfig{topKThreshold = Just thresh}
      , Right envK    <- [compile confK{batched = True}  p]
      , Right envKint <- [compile confK{batched = False} p]
      , Right srcLines <- [generateFunctionsBatched True envK]
      , Just groups  <- [batchGroups (not (null netNames)) qtcs]
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

runBatchedTopK :: FilePath -> ([(String, String, [BatchGroup], [String])], [String]) -> Property
runBatchedTopK py (topkEligible, biting)
  | null topkEligible = counterexample "BatchedPython topK: no eligible programs" False
  | null biting = counterexample
      ("BatchedPython topK: thresholds " ++ show topKDiffThresholds
       ++ " prune nothing anywhere in the corpus -- the differential is vacuous") False
  | otherwise = ioProperty $ do
      hPutStrLn stderr ("BatchedPython topK: " ++ show (length topkEligible)
                        ++ " program/threshold pairs over " ++ show topKDiffThresholds
                        ++ " (pruning bites on " ++ intercalate ", " biting ++ "), via " ++ py)
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
-- fresh per-point batch (the point's own read-logits symbol, repeated) and test
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
      [ "    _ns[" ++ show nm ++ "] = (lambda s: s)" | nm <- netNames ] ++
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
-- -- which means the emitted-code path for the one IR node a countBranches
-- compile builds and a default compile never does ('IREnumSumPaired', the
-- single-loop @(probability, branchCount)@ enum sum) is otherwise executed by
-- no backend at all. This group compiles the programs above with
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
-- | The property 'IREnumSumPaired' existed to provide, checked structurally on
-- the tensor lowering that replaced it (design ir-tensor-values): some
-- let-bound tensor map is read by two or more separate reductions.
--
-- This is the load-bearing half of that node. A branch-counting compile needs
-- both a probability sum and a branch-count sum over one enumeration, and two
-- single-scalar loops could not share a loop body -- so before the tensor
-- lowering each re-embedded the whole per-iteration computation, doubling the
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
type BranchCountCase = (String, Program, IREnv, [(TestCase, Double, Double, Double)])

loadBranchCountCase :: String -> IO BranchCountCase
loadBranchCountCase name = do
  prog <- parseProgram ("testCases/" ++ name ++ ".ppl")
  (_, _, tcs) <- parseTestCases ("testCases/" ++ name ++ ".tst")
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
branchCountPython :: String -> IREnv -> [(TestCase, Double, Double, Double)] -> Property
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
                \  if p != 0 and abs(d - ed) > " ++ show probTolerance ++ ":\n\
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
                \  if p != 0 && abs(d - ed) > " ++ show probTolerance ++ "\n\
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
    (_, _, _, h) <- createProcess (proc "julia" [tmpPath])
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
branchCountLogSpace :: String -> Program -> [(TestCase, Double, Double, Double)] -> Property
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
unoptimizedRecompileExempt :: [String]
unoptimizedRecompileExempt = ["recursiveAdtMultiCtor"]

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

-- | Builds the standard End2End test groups from already-loaded/compiled
-- cases. includeBackends controls whether the Normalization/Julia/Python
-- groups are built (skipped for the slow subset, whose programs are
-- Interpreter-only by design).
buildEnd2EndTree :: String -> Bool
                  -> [(String, Program, Either CompilerError IREnv, [Backend], [TestCase])]
                  -> TestTree
buildEnd2EndTree treeName includeBackends compiledCases = testGroup treeName $
    [ testGroup "Interpreter"
        [ testProperty n (once $ conjoin (map (testInterpreter p c) tcs)) | (n, p, c, bs, tcs) <- compiledCases, Interpreter `elem` bs ]
    -- Re-run every interpreter case at -O0 to confirm the optimizer changes no answer.
    , testGroup "Interpreter Unoptimized"
        [ testProperty n (once $ conjoin (map (testInterpreter p c) tcs)) | (n, p, c, bs, tcs) <- unoptCases, Interpreter `elem` bs ]
    ] ++
    ( if not includeBackends then [] else
      let queryTestCases = [(n, p, c, bs, filter (\x -> isProbTestCase x || isCumulTestCase x) tcs) | (n, p, c, bs, tcs) <- compiledCases]
          -- A query program routes onto every backend it lists, same as
          -- before, except that Python now also takes a neural program
          -- (@includeNeural = True@): the filter that used to drop one there
          -- existed only because Python has no network to call at runtime,
          -- not because the routing was otherwise unsound (task
          -- route-neural-programs-to-julia-python-backends). Once an identity
          -- mock is installed for each declared network ('testPython') and
          -- the .tst row's own mock-NN parameters are pre-resolved to the raw
          -- vectors that mock would have produced ('resolveNeuralTestCase'),
          -- a neural program is just another program. Julia keeps the old
          -- exclusion for now (@includeNeural = False@) -- the design doc's
          -- own recommendation (agreed on review) is Python first, Julia
          -- decided on the evidence of what that catches; 'testJuliaAll'
          -- gained the same identity-mock plumbing so extending it later is a
          -- routing-only change, not a harness one.
          routedQueries includeNeural b =
            [ (n, c, if null (neurals p) then tcs else map (resolveNeuralTestCase p) tcs, networkNames p)
            | (n, p, c, bs, tcs) <- queryTestCases, b `elem` bs, not (null tcs)
            , includeNeural || null (neurals p) ]
          unoptQueries b = [(n, c, tcs') | (n, p, c, bs, tcs) <- unoptCases, b `elem` bs, null (neurals p)
                           , n `elem` unoptimizedCodegenSmoke
                           , n `notElem` unoptimizedCodegenExempt
                           , let tcs' = filter (\x -> isProbTestCase x || isCumulTestCase x) tcs, not (null tcs')]
          neuralP = [(n, p, c) | (n, p, c, bs, _) <- compiledCases, Interpreter `elem` bs, not (null (neurals p))]
      in [ testGroup "Normalization"
             [ testProperty n (once $ discreteProbsNormalized p c) | (n, p, c) <- neuralP ]
         -- All Julia programs share one batch file (and one julia process) to amortize startup.
         , testProperty "Julia" (once $ testJuliaAll [(c, tcs, nets) | (_, c, tcs, nets) <- routedQueries False Julia])
         , testGroup "Python"
             [ testProperty n (once $ testPython nets c tcs) | (n, c, tcs, nets) <- routedQueries True Python ]
         -- The same corpus through the text backends at -O0. See
         -- \'unoptCases\' for why this is not merely a duplicate of the
         -- optimized groups. None of 'unoptimizedCodegenSmoke' is neural, so
         -- this stays on the plain (non-mock-resolved) test cases.
         , testProperty "Julia Unoptimized" (once $ testJuliaAll [(c, tcs, []) | (_, c, tcs) <- unoptQueries Julia])
         , testGroup "Python Unoptimized"
             [ testProperty n (once $ testPython [] c tcs) | (n, c, tcs) <- unoptQueries Python ]
         ]
    )
  where
    -- Every corpus program recompiled at -O0, shared by all the "Unoptimized"
    -- groups so the extra compile is paid once.
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
    unoptCases = [ (n, p, compile defaultCompilerConfig{optimizerLevel = 0} p, bs, tcs)
                 | (n, p, _, bs, tcs) <- compiledCases
                 , n `notElem` unoptimizedRecompileExempt ]
