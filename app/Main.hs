module Main where

import Lib
import Options.Applicative
import SPLL.Lang.Lang (Program)
import SPLL.Examples
import System.IO
import SPLL.IntermediateRepresentation
import Data.Char (toLower)

data Opts = Opts {
  inputFile :: String,
  outputFile :: String,
  language :: Language,
  countBranches :: Bool,
  topKCutoff :: Maybe Double
} deriving Show

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

parseOpts :: Parser Opts
parseOpts = Opts
        <$> strOption
            ( long "inputFile"
            <> short 'i'
            <> metavar "INPUT_FILE"
            <> help "Input file to read the source code from")
        <*> strOption
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
            ( long "countBranches"
            <> short 'c'
            <> help "The compiled code will count the number of branches traversed")
        <*> optional (option auto
            ( long "topKCutoff"
            <> short 'k'
            <> help "Probabilities lower than the cutoff will not be considered. Range from 0-1"
            <> metavar "CUTOFF" ))

-- Entry point for the program, parse CLI arguments and pass execution to transpile
main :: IO ()
--main = someFunc
main = transpile =<< execParser opts
         where
           opts = info (parseOpts <**> helper)
             ( fullDesc
            <> progDesc "Print a greeting for TARGET"
            <> header "hello - a test for optparse-applicative" )

transpile :: Opts -> IO ()
transpile options = do
  print options
  content <- readInputFile (inputFile options)
  let prog = parseProgram content
  let transpiled = codeGenToLang (language options) (CompilerConfig {SPLL.IntermediateRepresentation.countBranches = Main.countBranches options, topKThreshold = topKCutoff options}) prog
  writeOutputFile (outputFile options) transpiled

readInputFile :: String -> IO String
readInputFile = readFile

parseProgram :: String -> Program Double
parseProgram inp = uniformProg  --TODO Real parse

writeOutputFile :: String -> String -> IO()
writeOutputFile = writeFile
