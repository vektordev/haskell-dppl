{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Exit (exitWith, ExitCode(ExitFailure))
import System.Directory (listDirectory)
import System.FilePath (stripExtension, isExtensionOf)
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
import Test.QuickCheck hiding (verbose)
import Debug.Trace

standardCompiler :: CompilerConfig
standardCompiler = CompilerConfig {countBranches = False, topKThreshold = Nothing, optimizerLevel = 2, verbose = 0}

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

testInterpreter :: Program -> TestCase -> Property
testInterpreter p (ProbTestCase name sample params (VFloat expectedProb, VFloat expectedDim)) = do
  let VTuple (VFloat outProb) (VFloat outDim) = runProb standardCompiler p params sample
  counterexample ("Probability differs for test case " ++ name ++". Expected: " ++ show expectedProb ++ " Got: " ++ show outProb) ((abs (outProb - expectedProb)) < 0.0001) .&&.
    counterexample ("Dimensionality differs for test case " ++ name ++". Expected: " ++ show expectedDim ++ " Got: " ++ show outDim) (outProb === 0 .||. outDim === expectedDim)
testInterpreter p (ArgmaxPTestCase name params res) = ioProperty $ do
  let paramCnt = length params
  let mockedParams seeds = map (\(par, s) -> VTuple (VInt 1) (VTuple par (VInt s))) (zip params seeds)
  let mockedParamsList start = map mockedParams [[x .. x + (paramCnt-1)] | x <- [start, paramCnt..]]  -- [[((1, (p1, 0)), (1, (p2, 1)))], [(1, (p1, 2)), (1, (p2, 3))] ..]
  let resP = runProb standardCompiler p (head (mockedParamsList 0)) res
  let cntSamples = 100
  samples <- evalRandIO $ mapM (runGen standardCompiler p) (take cntSamples (mockedParamsList paramCnt))
  let samplesP = map (\(par, s) -> runProb standardCompiler p par s) (zip (take cntSamples (mockedParamsList (paramCnt * cntSamples))) samples)
  return $ conjoin (map (\(s, p) -> counterexample ("Test Case " ++ name ++ ": Sample " ++ show s ++ " has highest probability: " ++ show p ++ " instead of sample " ++ show res ++ " with probability: " ++ show resP) (p `lessEqualsProbs` resP)) (zip samples samplesP))

lessEqualsProbs :: IRValue -> IRValue -> Bool
lessEqualsProbs (VFloat a) (VFloat b) = a <= b
lessEqualsProbs (VTuple (VFloat aP) (VFloat aD)) (VTuple (VFloat bP) (VFloat bD)) | aD == bD = aP <= bP
lessEqualsProbs (VTuple _ (VFloat aD)) (VTuple _ (VFloat bD)) = aD > bD -- Lower dimensionality means higher probability

-- TODO: Maybe stop sampling early if no more new samples are found
discreteProbsNormalized :: Program -> Property
discreteProbsNormalized p = counterexample "Probability of randomly sampled values does not sum to 1" (sumProbSamples pSamples >= sufficientlyNormal)
  where
    paramCnt = progParameterCount p
    seedList = [0 .. (paramCnt - 1)] -- List of natural numbers split into parameter count sized chunks
    params = map (VTuple (VInt 0) . VInt) seedList  -- Made each element into a tuple with a 0 to select the random NN mock
    sampleCnt = 1000
    sufficientlyNormal = 0.99
    prob (VTuple (VFloat p) _) = p
    sumProbSamples samples = sum $ map (\sam -> prob $ runProb standardCompiler p params sam) samples
    pSamples = nub $ evalRand ((replicateM sampleCnt randomParams) >>= mapM (runGen standardCompiler p) ) (mkStdGen 42)
    randomParams = (replicateM paramCnt (getRandomR (1, 100000))) >>= mapM (\x -> return $ VTuple (VInt 0) (VInt x)) :: RandomGen g => Rand g [IRValue] -- Create a list of random ints and then make them into a tuple

progParameterCount :: Program -> Int
progParameterCount Program{functions=f} = countLambdas main
  where
    Just main = lookup "main" f
    countLambdas (Lambda _ _ e) = 1 + countLambdas e
    countLambdas _ = 0

testProbJulia :: Program -> [TestCase] -> Property
testProbJulia p tc = ioProperty $ do
  let src = intercalate "\n" (SPLL.CodeGenJulia.generateFunctions (compile standardCompiler p))
  (_, _, _, handle) <- createProcess (proc "julia" ["-e", juliaProbTestCode src tc])
  code <- waitForProcess handle
  case code of
    ExitSuccess -> return $ True === True
    ExitFailure _ -> return $ counterexample "Julia test failed. See Julia error message" False

testProbPython :: Program -> [TestCase] -> Property
testProbPython p tc = ioProperty $ do
  let src = intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True (compile standardCompiler p))
  (_, _, _, handle) <- createProcess (proc "python3" ["-c", pythonProbTestCode src tc])
  code <- waitForProcess handle
  case code of
    ExitSuccess -> return $ True === True
    ExitFailure _ -> return $ counterexample "Python test failed. See Python error message" False

juliaProbTestCode :: String -> [TestCase] -> String
juliaProbTestCode src tcs =
  "include(\"juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n\
  \" ++ src ++ "\n" ++ 
  "main_gen(" ++ intercalate ", " (map juliaVal exampleParams) ++ ")\n" ++
  concat (map (\(ProbTestCase name sample params (outProb, outDim)) -> "tmp = main_prob(" ++ juliaVal sample ++ intercalate ", " (map juliaVal params) ++ ")\n\
  \if abs(tmp[1] - " ++ juliaVal outProb ++ ") > 0.0001\n\
  \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ ") * \"in test case " ++ name ++ "\")\n\
  \end\n\
  \if tmp[1] != 0 && tmp[2] != " ++ juliaVal outDim ++ "\n\
  \  error(\"Dimensionality wrong: \" * string(tmp[2]) * \"/=\" * string(" ++ juliaVal outDim ++ ") * \"in test case " ++ name ++ "\")\n\
  \end\n") tcs) ++ 
  "exit(0)"
  where ProbTestCase _ _ exampleParams _ = head tcs 

pythonProbTestCode :: String -> [TestCase] -> String
pythonProbTestCode src tcs = 
  unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") (pack src)) ++ "\n" ++   -- Importing pyTorch is really slow and not needed
  "main.generate(" ++ intercalate ", " (map pyVal exampleParams) ++ ")\n" ++
  concat (map (\(ProbTestCase name sample params (outProb, outDim)) -> "tmp = main.forward(" ++ pyVal sample ++ intercalate ", " (map pyVal params) ++ ")\n\
  \if abs(tmp[0] - " ++ pyVal outProb ++ ") > 0.0001:\n\
  \  raise ValueError(\"Probability wrong: \" + str(tmp[0]) + \"!=\" + str(" ++ pyVal outProb ++ ") + \"in test case " ++ name ++ "\")\n\
  \if tmp[0] != 0 and tmp[1] != " ++ pyVal outDim ++ ":\n\
  \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1]) + \"/=\" + str(" ++ pyVal outDim ++ ") + \"in test case " ++ name ++ "\")\n\
  \") tcs) ++ 
  "exit(0)"
  where ProbTestCase _ _ exampleParams _ = head tcs 

test_end2end :: IO (Bool)
test_end2end = do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  let probTestCases = map (\(p, tcs) -> (p, filter isProbTestCase tcs)) cases
  let nonNeuralsProb = filter (null . neurals . fst) probTestCases
  let neuralP = map fst (filter (not . null . neurals . fst) cases)

  putStrLn "=== Test End2End Interpreter ==="
  let interprTest = label "End2End Interpreter" $ conjoin [conjoin $ map (testInterpreter p) tcs | (p, tcs) <- cases]
  interprProp <- quickCheckResult (withMaxSuccess 1 interprTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Interpreter Normalization ==="
  let interprNormalizeTest = label "End2End Interpreter Normalization" $ conjoin [discreteProbsNormalized p | p <- neuralP]
  interprNormalProp <- quickCheckResult (withMaxSuccess 1 interprNormalizeTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Julia ==="
  let juliaTest = label "End2End Julia" $ conjoin [testProbJulia p tcs | (p, tcs) <- nonNeuralsProb]
  juliaProp <- quickCheckResult (withMaxSuccess 1 juliaTest) >>= return . isSuccess

  putStrLn "\n=== Test End2End Python ==="
  let pythonTest = label "End2End Python" $ conjoin [testProbPython p tcs | (p, tcs) <- nonNeuralsProb]
  pythonProp <- quickCheckResult (withMaxSuccess 1 pythonTest) >>= return . isSuccess

  return $ interprProp && interprNormalProp && juliaProp && pythonProp
