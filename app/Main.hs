module Main where

import Options.Applicative
import SPLL.Lang.Lang (Program)
import SPLL.Examples
import System.IO
import System.Exit
import SPLL.IntermediateRepresentation
import Data.Char (toLower)
import SPLL.Parser
import System.Exit (exitFailure)
import Text.Megaparsec.Error (errorBundlePretty)
import SPLL.Lang.Types (Value(..), GenericValue (..), CompilerError, GenericList (EmptyList))
import Text.Read
import SPLL.Prelude (runProb, runInteg, runGen, compile)
import Control.Monad.Random (randomIO, evalRandIO)
import SPLL.IntermediateRepresentation (CompilerConfig(..))
import Data.Foldable (asum)
import qualified SPLL.CodeGenJulia
import qualified SPLL.CodeGenPyTorch
import Data.List (intercalate)
import Text.Megaparsec (runParser, sepBy)
import Control.Monad.State (runStateT)
import SPLL.Parser (pCSV)
import Data.Maybe (fromMaybe)

data GlobalOpts = GlobalOpts {
  inputFile :: String,
  verbosity :: Int,
  countBranches :: Bool,
  topKCutoff :: Maybe Double,
  optimiziationLevel :: Int,
  pruneAnys :: Bool,
  noInteg :: Bool,
  noProb :: Bool,
  noGen :: Bool, 
  commandOpts :: CommandOpts
}

data CommandOpts =
  CompileOpts {
    outputFile :: String,
    language :: Language,
    trunc :: Bool
  }
  | GenerateOpts {
    paramsG :: [IRValue]
  }
  | ProbabilityOpts{
    posP :: IRValue,
    paramsP :: [IRValue]
  }
  | CumulativeOpts {
    posC :: IRValue,
    paramsC :: [IRValue]
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

readValueList :: ReadM [IRValue]
readValueList = eitherReader (\s -> 
  case runParser (runStateT pCSV 0) "CLI" s of
    Left err -> Left (errorBundlePretty err)
    Right (val, _) -> Right (map valueToIR val))

optionalList :: Alternative f => f [a] -> f [a]
optionalList x = fmap (fromMaybe []) (optional x)

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
        <*> switch
            ( long "noIntegrate"
            <> short 'I'
            <> help "The compiler does not generate a CDF function. This function may be required for the code to work")
        <*> switch
            ( long "noProbability"
            <> short 'P'
            <> help "The compiler does not generate a PDF function. This function may be required for the code to work")
        <*> switch
            ( long "noGenerate"
            <> short 'G'
            <> help "The compiler does not generate a generate function. This function may be required for the code to work")
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
parseGenerateOpts = GenerateOpts
        <$> optionalList (option readValueList
            ( short 'p'
            <> metavar "PARAMS"
            <> help "Parameters passed to the main functions. List of values separated by commas. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer."))

parseProbabilityOpts :: Parser CommandOpts
parseProbabilityOpts = ProbabilityOpts
        <$> option readValue
            ( short 'x'
            <> metavar "SAMPLE"
            <> help "Sample value to calculate inference for. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer.")
        <*> optionalList (option readValueList
            ( short 'p'
            <> metavar "PARAMS"
            <> help "Parameters passed to the main functions. List of values separated by commas. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer."))

parseIntegrateOpts :: Parser CommandOpts
parseIntegrateOpts = CumulativeOpts
        <$> option readValue
            ( short 'x'
            <> metavar "SAMPLE"
            <> help "Sample value to calculate inference for. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer.")
        <*> optionalList (option readValueList
            ( short 'p'
            <> metavar "PARAMS"
            <> help "Parameters passed to the main functions. List of values separated by commas. Make sure to use the correct datatypes. E.g., use 3.0 for a float or 3 for an integer."))


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
transpile (GlobalOpts {inputFile=inFile, verbosity=verb, Main.countBranches=cb, topKCutoff=tkc, commandOpts=options, optimiziationLevel=oLvl, pruneAnys=anyChecks, noInteg=nInteg, noProb=nProb, noGen=nGen}) = do
  prog <- parseProgram inFile
  let conf = (CompilerConfig {SPLL.IntermediateRepresentation.countBranches = cb, topKThreshold = tkc, verbose=verb, optimizerLevel=oLvl, pruneAnyChecks=anyChecks, noIntegrate=nInteg, noProbability=nProb,noGenerate=nGen})
  case options of
    CompileOpts{language=lang, outputFile=outFile, trunc=trnc} -> do
      case codeGenToLang lang trnc conf prog of
        Left err -> handleError err
        Right trans -> writeOutputFile outFile trans
    GenerateOpts {paramsG=params} -> do
      -- TODO: Nicer Output
      case runGen conf prog params of
        Left err -> handleError err
        Right randVal -> do
          val <- evalRandIO randVal
          print ("X=" ++ show val)
    ProbabilityOpts{posP=x, paramsP=params} ->
      -- TODO: Nicer Output
      case runProb conf prog params x of
        Left err -> handleError err
        Right p -> print ("p(X="++ show x ++ ")=" ++ show p)
    CumulativeOpts{posC=x, paramsC=params} ->
      -- TODO: Nicer Output
      case runInteg conf prog params x of 
        Left err -> handleError err
        Right i -> print ("CDF("++ show x ++ ")=" ++ show i)

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

codeGenToLang :: Language -> Bool -> CompilerConfig -> Program -> Either CompilerError String
codeGenToLang lang trunc conf prog = do
  compiled <- compile conf prog
  case lang of
    Python -> Right $ intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions (not trunc) compiled)
    Julia -> Right $ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions compiled)

writeOutputFile :: String -> String -> IO()
writeOutputFile = writeFile

handleError :: CompilerError -> IO ()
handleError err = do
  putStrLn ("Error during execution: " ++ err)
  exitWith (ExitFailure 1)
