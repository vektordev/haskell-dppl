{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Exit (exitWith, ExitCode(ExitFailure))
import System.Directory (listDirectory)
import System.FilePath (stripExtension, isExtensionOf)
import System.Process
import System.Exit
import Data.Maybe
import Data.List (intercalate)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.Parser (tryParseProgram, pValue)
import qualified Text.Megaparsec.Char.Lexer as L
import SPLL.CodeGenJulia
import SPLL.CodeGenPyTorch
import TestCaseParser
import SPLL.IntermediateRepresentation
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

testProbProgramInterpreter :: Program -> TestCase -> Property
testProbProgramInterpreter p (ProbTestCase sample params (VFloat expectedProb, VFloat expectedDim)) = do
  let VTuple (VFloat outProb) (VFloat outDim) = runProb standardCompiler p params sample
  counterexample "Probability differs" ((abs (outProb - expectedProb)) < 0.0001) .&&.
    counterexample "Dimensionality differs" (outDim === expectedDim)

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

--TODO Hardcoded precision of 4 digits
juliaProbTestCode :: String -> [TestCase] -> String
juliaProbTestCode src tcs = 
  "include(\"juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n\
  \" ++ src ++ "\n" ++ 
  "main_gen(" ++ intercalate ", " (map juliaVal exampleParams) ++ ")\n" ++
  concat (map (\(ProbTestCase sample params (outProb, outDim)) -> "tmp = main_prob(" ++ juliaVal sample ++ intercalate ", " (map juliaVal params) ++ ")\n\
  \if tmp[1] - " ++ juliaVal outProb ++ " > 0.0001\n\
  \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ "))\n\
  \end\n\
  \if tmp[2] != " ++ juliaVal outDim ++ "\n\
  \  error(\"Dimensionality wrong: \" * string(tmp[2]) * \"/=\" * string(" ++ juliaVal outDim ++ "))\n\
  \end\n") tcs) ++ 
  "exit(0)"
  where ProbTestCase _ exampleParams _ = head tcs 

--TODO Hardcoded precision of 4 digits
pythonProbTestCode :: String -> [TestCase] -> String
pythonProbTestCode src tcs = 
  src ++ "\n" ++
  "main.generate(" ++ intercalate ", " (map pyVal exampleParams) ++ ")\n" ++
  concat (map (\(ProbTestCase sample params (outProb, outDim)) -> "tmp = main.forward(" ++ pyVal sample ++ intercalate ", " (map pyVal params) ++ ")\n\
  \if abs(tmp[0] - " ++ pyVal outProb ++ ") > 0.0001:\n\
  \  raise ValueError(\"Probability wrong: \" + str(tmp[0]) + \"!=\" + str(" ++ pyVal outProb ++ "))\n\
  \if tmp[1] != " ++ pyVal outDim ++ ":\n\
  \  raise ValueError(\"Dimensionality wrong: \" + str(tmp[1]) * \"/=\" + str(" ++ pyVal outDim ++ "))\n\
  \") tcs) ++ 
  "exit(0)"
  where ProbTestCase _ exampleParams _ = head tcs 


prop_end2endTests :: Property
prop_end2endTests = ioProperty $ do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseTestCases tc >>= \t2 -> return (t1, t2)) files
  let interpProp = conjoin (map (\(p, tcs) -> conjoin $ map (testProbProgramInterpreter p) tcs) cases)
  let juliaProp = conjoin (map (\(p, tcs) -> testProbJulia p tcs) cases)
  let pythonProp = conjoin (map (\(p, tcs) -> testProbPython p tcs) cases)
  return $ interpProp .&&. pythonProp .&&. juliaProp


return []
--test_end2end = $quickCheckAll
test_end2end = quickCheckResult (withMaxSuccess 1 prop_end2endTests) >>= return . isSuccess