module Main where

import Options.Applicative
import SPLL.Lang.Lang (Program)
import SPLL.Examples
import System.IO
import SPLL.IntermediateRepresentation
import Data.Char (toLower)
import SPLL.Parser
import System.Exit (exitFailure)
import Text.Megaparsec.Error (errorBundlePretty)
import SPLL.Lang.Types (Value(..), GenericValue (..))
import Text.Read
import SPLL.Prelude (runProb, runInteg, runGen, compile)
import Control.Monad.Random (randomIO, evalRandIO)
import SPLL.IntermediateRepresentation (CompilerConfig(..))
import Data.Foldable (asum)
import qualified SPLL.CodeGenJulia
import qualified SPLL.CodeGenPyTorch
import Data.List (intercalate)
import Text.Megaparsec (runParser)
import Control.Monad.State (runStateT)

data GlobalOpts = GlobalOpts {
  inputFile :: String,
  verbosity :: Int,
  countBranches :: Bool,
  topKCutoff :: Maybe Double,
  optimiziationLevel :: Int,
  pruneAnys :: Bool,
  commandOpts :: CommandOpts
}

data CommandOpts =
  CompileOpts {
    outputFile :: String,
    language :: Language,
    trunc :: Bool
  }
  | GenerateOpts
  | ProbabilityOpts{
    posP :: IRValue
  }
  | CumulativeOpts {
    posC :: IRValue
  } deriving Show

data Language = Python | Julia deriving Show

readLanguage :: ReadM Language
readLanguage = str >>= \s -> case map toLower s of
  "python" -> return Python
  "py" -> return Python
  "p" -> return Python
  "julia" -> return Julia
  "jul" -> return Julia
  "jl" -> return Julia
  "j" -> return Julia
  _ -> readerError "Only python or julia are supported as languages"

verbosityParser :: Parser Int
verbosityParser = length <$> many (flag' () (short 'v' <> help "Increases verbosity"))

readValue :: ReadM IRValue
readValue = eitherReader (\s -> 
  case runParser (runStateT pValue 0) "CLI" s of
    Left err -> Left (errorBundlePretty err)
    Right (val, _) -> Right (valueToIR val))

parseGlobalOpts :: Parser GlobalOpts
parseGlobalOpts = GlobalOpts
        <$> strOption
            ( long "inputFile"
            <> short 'i'
            <> metavar "INPUT_FILE"
            <> help "Input file to read the source code from")
        <*> verbosityParser
        <*> switch
            ( long "countBranches"
            <> short 'c'
            <> help "The compiled code will count the number of branches traversed")
        <*> optional (option auto
            ( long "topKCutoff"
            <> short 'k'
            <> help "Probabilities lower than the cutoff will not be considered. Range from 0-1"
            <> metavar "CUTOFF" ))
        <*> option auto
            ( long "optimizationLevel"
            <> short 'O'
            <> help "Level of optimization. 0: None, 1: Basic, 2: Advanced"
            <> showDefault
            <> value 2
            <> metavar "OPTIMIZATION" )
        <*> switch
            ( long "pruneAnyChecks"
            <> help "Prune any-checks from compiled code. WARNING: This may lead to unexpected results. You should probably leave this off")
        <*> hsubparser (
          command "compile" (info parseCompileOpts (progDesc "Compiles the program with inference interface into target language"))
          <> command "generate" (info parseGenerateOpts (progDesc "Runs the generate pass of the program"))
          <> command "probability" (info parseProbabilityOpts (progDesc "Runs probabilistic inference on the program. Returns the probability of a given value to be the output of the program"))
          <> command "cumulative" (info parseIntegrateOpts (progDesc "Runs probabilistic inference on the program. Returns the probability of the program output to be less than the given sample"))
        )

parseCompileOpts :: Parser CommandOpts
parseCompileOpts = CompileOpts
        <$> strOption
            ( long "outputFile"
            <> short 'o'
            <> metavar "OUTPUT_FILE"
            <> help "Output file the transpiled code is written into")
        <*> option readLanguage
            ( long "language"
            <> short 'l'
            <> metavar "LANG"
            <> help "Language the program is transpiled to. Either python or julia")
        <*> switch
            (long "truncate"
            <> short 't'
            <> help "Truncates boilerplate from the generated code")

parseGenerateOpts :: Parser CommandOpts
parseGenerateOpts = pure GenerateOpts

parseProbabilityOpts :: Parser CommandOpts
parseProbabilityOpts = ProbabilityOpts
        <$> option readValue
            ( short 'x'
            <> metavar "SAMPLE"
            <> help "Sample value to calculate inference for. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer.")

parseIntegrateOpts :: Parser CommandOpts
parseIntegrateOpts = CumulativeOpts
        <$> option readValue
            ( short 'x'
            <> metavar "SAMPLE"
            <> help "Sample value to calculate inference for. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer.")


-- Entry point for the program, parse CLI arguments and pass execution to transpile
main :: IO ()
--main = someFunc
--main = testParse
main = transpile =<< execParser opts
         where
           opts = info (parseGlobalOpts <**> helper)
             ( fullDesc
            <> progDesc "Compiles or computes probabilistic programs"
            <> header "Haskell DPPL" )

transpile :: GlobalOpts -> IO ()
transpile (GlobalOpts {inputFile=inFile, verbosity=verb, Main.countBranches=cb, topKCutoff=tkc, commandOpts=options, optimiziationLevel=oLvl, pruneAnys=anyChecks}) = do
  prog <- parseProgram inFile
  let conf = (CompilerConfig {SPLL.IntermediateRepresentation.countBranches = cb, topKThreshold = tkc, verbose=verb, optimizerLevel=oLvl, pruneAnyChecks=anyChecks})
  case options of
    CompileOpts{language=lang, outputFile=outFile, trunc=trnc} -> do
      transpiled <- codeGenToLang lang trnc conf prog
      writeOutputFile outFile transpiled
    GenerateOpts -> do
      -- TODO: Nicer Output
      val <- evalRandIO (runGen conf prog [])
      print ("X=" ++ show val)
    ProbabilityOpts{posP=x} ->
      -- TODO: Nicer Output
      print ("p(X="++ show x ++ ")=" ++ show (runProb conf prog [] x))
    CumulativeOpts{posC=x} ->
      -- TODO: Nicer Output
      print ("CDF("++ show x ++ ")=" ++ show (runInteg conf prog [] x))

parseProgram :: FilePath -> IO Program
--parseProgram path = return testLambdaParameter
parseProgram path = do
  content <- readFile path
  let maybeError = tryParseProgram path content
  case maybeError of
    Left err -> do
      putStrLn "### Parse Error ###"
      putStrLn (errorBundlePretty err)
      exitFailure
    Right prog -> return prog

codeGenToLang :: Language -> Bool -> CompilerConfig -> Program -> IO String
codeGenToLang lang trunc conf prog = do
  let compiled = compile conf prog
  case lang of
    Python -> return $ intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions (not trunc) compiled)
    Julia -> return $ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions compiled)

writeOutputFile :: String -> String -> IO()
writeOutputFile = writeFile
