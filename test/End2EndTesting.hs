{-# LANGUAGE TemplateHaskell #-}

module End2EndTesting where

import System.Exit (exitWith, ExitCode(ExitFailure))
import System.Directory (listDirectory)
import System.FilePath (stripExtension, isExtensionOf)
import Data.Maybe
import Data.Bifunctor (bimap)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import Text.Megaparsec (errorBundlePretty)
import SPLL.IntermediateRepresentation
import Test.QuickCheck hiding (verbose)

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
parseProbTestCases fp = return [(VFloat 0.5, [], (VFloat 1, VFloat 1))]

testProbProgramInterpreter :: Program -> ProbTestCase -> Property
testProbProgramInterpreter p (sample, params, (VFloat expectedProb, VFloat expectedDim)) = do
  let VTuple (VFloat outProb) (VFloat outDim) = runProb standardCompiler p params sample
  counterexample "Probability differs" (outProb === expectedProb) .&&.
    counterexample "Dimensionality differs" (outDim === expectedDim)

prop_end2endTests :: Property
prop_end2endTests = ioProperty $ do
  files <- getAllTestFiles
  cases <- mapM (\(p, tc) -> parseProgram p >>= \t1 -> parseProbTestCases tc >>= \t2 -> return (t1, t2)) files
  return $ conjoin (map (\(p, tcs) -> conjoin $ map (testProbProgramInterpreter p) tcs) cases)

return []
test_end2end = $quickCheckAll