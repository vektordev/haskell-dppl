module Main (main) where

import Options.Applicative
import SPLL.Lang.Lang (Program)
import SPLL.IntermediateRepresentation
import SPLL.Parser
import Data.Char (toLower)
import Text.Megaparsec.Error (errorBundlePretty)
import SPLL.Lang.Types (CompilerError)
import SPLL.Prelude (runProb, runInteg, runGen, compile, batchedRefusal)
import Control.Monad.Random (evalRandIO)
import qualified SPLL.CodeGenJulia
import qualified SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import Data.List (intercalate)
import Text.Megaparsec (runParser)
import Control.Monad.State (runStateT)
import Data.Maybe (fromMaybe)
import System.Exit (exitFailure, exitWith, ExitCode (ExitFailure))
import System.IO (hPutStrLn, stderr)
import Control.Exception (SomeException, evaluate, try)

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
  debugIntermediates :: Bool,
  noTypeCheck :: Bool,
  batchedMode :: Bool,
  logSpaceMode :: Bool,
  optStatsMode :: Bool,
  extraSemiringsMode :: [SemiringFamily],
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

-- | Parses "--semiring=map" (task semiring-parametric-marginals) into
-- 'CompilerConfig's 'extraSemirings': a comma-separated list of the CLI-facing
-- names 'SPLL.Semiring.semiringSuffix' assigns each non-default
-- 'SemiringFamily' that actually has a sound 'SPLL.Semiring.Semiring'
-- instance -- 'SRSumProduct' is never a valid token here (it names the
-- ordinary compile every program already gets, not an extra one to request),
-- and 'SRCounting' is refused with a message pointing at the long comment
-- on it: the natural leaf-reweighting implementation is unsound under this
-- codebase's Boolean-condition representation (found and reverted during this
-- task rather than shipped), not merely unimplemented.
readSemiringList :: ReadM [SemiringFamily]
readSemiringList = eitherReader (\s -> mapM parseOne (splitOn ',' s))
  where
    parseOne "map"   = Right SRMaxProduct
    parseOne "count" = Left "--semiring=count: model counting has no sound implementation in this compiler (see the SRCounting comment in SPLL.IntermediateRepresentation) -- not merely unimplemented, refused"
    parseOne tok     = Left ("Unknown --semiring entry " ++ show tok ++ ": expected \"map\"")
    splitOn sep s' = case break (== sep) s' of
      (chunk, [])       -> [chunk]
      (chunk, _:rest)   -> chunk : splitOn sep rest

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
            <> help "Level of optimization. 0: None, 1: Basic, 2: Advanced, 3: Aggressive (trades compile time for smaller/faster output)"
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
        <*> switch
            ( long "debugIntermediates"
            <> short 'd'
            <> help "Print every intermediate AST state during compilation with full annotations (rType, pType, chainName, tags including Algorithm). Useful for diagnosing which stage introduces a defect.")
        <*> switch
            ( long "noTypeCheck"
            <> help "Omit the query-type guard that rejects a query value whose type does not match the program's return type (e.g. p(0.5) against a Bool program). The guard is on by default at every optimization level; disable it to shave the entry check off hot compiled code.")
        <*> switch
            ( long "batched"
            <> help "Opt into batched inference mode (design pytorch-tensorizer): with 'compile -l python', emits torch code that runs a whole [B]-shaped batch of query points through forward/integrate/generate at once (torch.where instead of data-dependent if), for the tensor fragment (float/int/bool leaves in fixed-shape tuples; no lists/ADTs/Either dispatch/recursion/marginal queries -- refused at compile time with a diagnostic naming the offending construct). Neural (ReadNN) programs are supported for forward/integrate/generate, including a read-logits network's own categorical/Gaussian sampling and cross-network composition (e.g. MNIST addition); an Either- or ADT-shaped neural output is refused at compile time like any other Either/ADT program. Only wires the IR select pass for other output languages (a behavioural no-op).")
        <*> switch
            ( long "logSpace"
            <> help "Compute probabilities in log space rather than linear space (task log-space-probability-computation). Motivation: deep conjunctions and long enumerations of small probabilities underflow in linear space long before they are numerically meaningless. Native log-pdf/log-cdf leaves are used for Normal/Uniform, and the compiled p()/cdf() functions return log-probabilities. Scope: the core PResult combinators, Uniform/Normal, discrete value-equality masses, and enumerable-InjF sums are log-aware; ReadNN/AutoNeural neural read-logits logit reads, the set-witness/plan-enum continuous measurement machinery, and batched mode remain linear-only under this flag.")
        <*> switch
            ( long "optStats"
            <> help "Report optimizer telemetry on stderr: how many fixed-point iterations the IR optimizer needed for each emitted function, plus a per-rule firing tally. Add -v for the per-iteration breakdown (which rule fired how often in which iteration). Diagnostic only -- it does not change what is compiled.")
        <*> optionalList (option readSemiringList
            ( long "semiring"
            <> metavar "FAMILY,..."
            <> help "Compile extra probability-mode entry points alongside the ordinary one (task semiring-parametric-marginals), one per comma-separated family: 'map' adds \"<name>_map\", the probability of the single most likely derivation of the query value (MAP/Viterbi) instead of the total over every derivation. Lands in the SAME output file as the ordinary generate/probability/integrate functions. Probability-mode only (no generate/integrate/normal_params variant), and not composed with --topKCutoff."))
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
transpile (GlobalOpts {inputFile=inFile, verbosity=verb, Main.countBranches=cb, topKCutoff=tkc, commandOpts=options, optimiziationLevel=oLvl, pruneAnys=anyChecks, noInteg=nInteg, noProb=nProb, noGen=nGen, debugIntermediates=dbgInter, noTypeCheck=nTypeChk, batchedMode=batchedFlag, logSpaceMode=logSpaceFlag, optStatsMode=optStatsFlag, extraSemiringsMode=extraSR}) = do
  prog <- parseProgram inFile
  let conf = (CompilerConfig {SPLL.IntermediateRepresentation.countBranches = cb, topKThreshold = tkc, verbose=verb, optimizerLevel=oLvl, pruneAnyChecks=anyChecks, noIntegrate=nInteg, noProbability=nProb,noGenerate=nGen, showIntermediates=dbgInter, checkQueryType=not nTypeChk, batched=batchedFlag, logSpace=logSpaceFlag, optStats=optStatsFlag, materializationCardinality=defaultMaterializationCardinality, extraSemirings=extraSR})
  case options of
    CompileOpts{language=lang, outputFile=outFile, trunc=trnc} -> do
      case codeGenToLang lang trnc conf prog of
        Left err -> handleError err
        Right trans -> do
          writeOutputFile outFile trans
          -- After the real compile, not before: the advisory is a closing note
          -- on a compile that succeeded, and there is nothing to advise about
          -- batching a program that does not compile scalar in the first place.
          reportBatchedEligibility conf prog
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
codeGenToLang lang truncOut conf prog = do
  compiled <- compile conf prog
  case lang of
    Python
      | batched conf -> intercalate "\n" <$> generateFunctionsBatched (not truncOut) compiled
      | otherwise    -> do
          anyExceptCodegenRefusal "Python" compiled
          Right $ intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions (not truncOut) compiled)
    Julia -> do
      anyExceptCodegenRefusal "Julia" compiled
      Right $ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions compiled)

writeOutputFile :: String -> String -> IO()
writeOutputFile = writeFile

handleError :: CompilerError -> IO ()
handleError err = do
  putStrLn ("Error during execution: " ++ err)
  exitWith (ExitFailure 1)

-- | Scalar-mode advisory (task @batched-scalar-mode-eligibility-warning@): tell
-- a user compiling normally whether @--batched@ would take this program, rather
-- than making them flip the flag and read a refusal.
--
-- Deliberately behind @-v@ and nothing lower. The check re-runs the whole
-- pipeline in batched mode and walks every prob/integ/generate body, which is
-- pure cost for the many programs nobody intends to batch; the corpus already
-- gets the same information for free from the @.tst@ @batched@ declaration's
-- @eligibility-gain-note@, so this is for the single-program case only.
--
-- It reports the *first* offender, matching the guard's own contract. An
-- advisory arguably wants the full list, but that is a different traversal —
-- so the note says so out loud instead of implying the one construct is all
-- there is.
--
-- Runs in 'IO' with the check forced under 'try' so that a compiler @error@ in
-- the batched pipeline degrades to an "unknown" line rather than killing a
-- scalar compile that had already succeeded on its own terms.
reportBatchedEligibility :: CompilerConfig -> Program -> IO ()
reportBatchedEligibility conf prog
  | verbose conf < 1 || batched conf = return ()
  | otherwise = do
      verdict <- try (evaluate (forceDiag (batchedRefusal conf prog)))
      hPutStrLn stderr $ case verdict of
        Left e ->
          "=== Batched Mode: eligibility unknown ===\n  the check itself failed: "
            ++ show (e :: SomeException)
        Right Nothing ->
          "=== Batched Mode: eligible ===\n  this program also compiles with --batched."
        Right (Just diag) ->
          "=== Batched Mode: not eligible ===\n  " ++ diag
            ++ "\n  (first offending construct only; more may be behind it.)"
  where
    -- 'batchedRefusal' is lazy in the diagnostic, so the guard has not actually
    -- run until the message is demanded -- force it inside the 'try'.
    forceDiag m@(Just s) = length s `seq` m
    forceDiag m = m
