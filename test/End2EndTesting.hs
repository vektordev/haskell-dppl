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
import SPLL.Parser (tryParseProgram)
import SPLL.CodeGenJulia 
import Text.Megaparsec (errorBundlePretty)
import SPLL.IntermediateRepresentation
import Test.QuickCheck hiding (verbose)
import Debug.Trace

type ProbTestCase = (IRValue, [IRValue], (IRValue, IRValue))

standardCompiler :: CompilerConfig
standardCompiler = CompilerConfig {countBranches = False, topKThreshold = Nothing, optimizerLevel = 2, verbose = 0}

getAllTestFiles :: IO [(FilePath, FilePath)]
getAllTestFiles = do
  files <- listDirectory "testCases"
  let pplFiles = filter (".ppl" `isExtensionOf`) files
  let pplFullPath = map ("testCases/" ++) pplFiles
  let testCaseFiles = map ((++ ".tst") . (fromJust . stripExtension ".ppl")) pplFullPath
  return (zip pplFullPath testCaseFiles)

parseProgram :: FilePath -> IO Program
parseProgram fp = do
  src <- readFile fp
  let prog =  tryParseProgram fp src
  case prog of
    Left str -> error $ "Error parsing " ++ fp ++ ": " ++ errorBundlePretty str
    Right p -> return p

parseProbTestCases :: FilePath -> IO [ProbTestCase]
parseProbTestCases fp = do
  content <- readFile fp
  let lines = split '\n' content
  let valueStrs = map (split ';') lines
  let values =  map (map parseValue) valueStrs
  return $ map (\vals ->
    let (outDim, notDim) = (last vals, init vals)
        (outProb, notOut) = (last notDim, init notDim)
        sample:params = notOut in
          (sample, params, (outProb, outDim))
    ) values
  where split delim str = case break (==delim) str of
                      (a, delim:b) -> a : split delim b
                      (a, "")    -> [a]

parseValue :: String -> IRValue
parseValue s = VFloat (read s)

testProbProgramInterpreter :: Program -> ProbTestCase -> Property
testProbProgramInterpreter p (sample, params, (VFloat expectedProb, VFloat expectedDim)) = do
  let VTuple (VFloat outProb) (VFloat outDim) = runProb standardCompiler p params sample
  counterexample "Probability differs" (outProb === expectedProb) .&&.
    counterexample "Dimensionality differs" (outDim === expectedDim)

testProbJulia :: Program -> [ProbTestCase] -> Property
testProbJulia p tc = ioProperty $ do
  let src = intercalate "\n" (SPLL.CodeGenJulia.generateFunctions (compile standardCompiler p))
  (_, _, _, handle) <- createProcess (proc "julia" ["-e", juliaProbTestCode src tc])
  code <- waitForProcess handle
  case code of
    ExitSuccess -> return $ True === True
    ExitFailure _ -> return $ counterexample "Julia test failed. See Julia error message" False

--TODO Hardcoded precision of 4 digits
juliaProbTestCode :: String -> [ProbTestCase] -> String
juliaProbTestCode src tcs = 
  "include(\"juliaLib.jl\")\n\
  \using .JuliaSPPLLib\n\
  \" ++ src ++ "\n" ++ 
  concat (map (\(sample, params, (outProb, outDim)) -> "tmp = main_prob(" ++ juliaVal sample ++ intercalate ", " (map juliaVal params) ++ ")\n\
  \if round(tmp[1], digits=4) != " ++ juliaVal outProb ++ "\n\
  \  error(\"Probability wrong: \" * string(tmp[1]) * \"/=\" * string(" ++ juliaVal outProb ++ "))\n\
  \end\n\
  \if tmp[2] != " ++ juliaVal outDim ++ "\n\
  \  error(\"Dimensionality wrong: \" * string(tmp[2]) * \"/=\" * string(" ++ juliaVal outDim ++ "))\n\
  \end\n") tcs) ++ 
  "exit(0)" 


prop_end2endTests :: Property
prop_end2endTests = ioProperty $ do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseProbTestCases tc >>= \t2 -> return (t1, t2)) files
  let interpProp = conjoin (map (\(p, tcs) -> conjoin $ map (testProbProgramInterpreter p) tcs) cases)
  let juliaProp = conjoin (map (\(p, tcs) -> testProbJulia p tcs) cases)
  return $  juliaProp


return []
--test_end2end = $quickCheckAll
test_end2end = quickCheckResult (withMaxSuccess 1 prop_end2endTests) >>= return . isSuccess