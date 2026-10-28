module Main (main) where

import Options.Applicative
import SPLL.Lang.Lang (Program)
import SPLL.IntermediateRepresentation
import SPLL.Parser
import Data.Char (toLower)
import Text.Megaparsec.Error (errorBundlePretty)
import SPLL.Lang.Types (CompilerError, GenericValue (VError))
import SPLL.Prelude (runProb, runInteg, runGen, batchedRefusal, CodeGenTarget(..), compile, emitCompiled, marginalReport, renderMarginalReport, programWarnings, compiledWarnings, renderCompileWarning, memoRecursionIgnored)
import SPLL.Lang.Lang (adts)
import Control.Monad.Random (evalRandIO)
import Text.Megaparsec (runParser)
import Control.Monad.State (runStateT)
import Data.Maybe (fromMaybe)
import System.Exit (exitFailure, exitWith, ExitCode (ExitFailure))
import System.IO (hPutStrLn, stderr)
import Control.Exception (SomeException, evaluate, try)
import SPLL.DuplicationCensus (censusEnv, defaultMinSize, renderCensus)
import SPLL.StageDiff (StageDiffOpts(..), StageReport(..), defaultStageDiffOpts, stageDiff, renderStageReport)

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
  marginalSlotsBudget :: Int,
  materializationBudget :: Int,
  marginalsReport :: Bool,
  duplicationReport :: Bool,
  memoRecursionMode :: Bool,
  commandOpts :: CommandOpts
}

data CommandOpts =
  CompileOpts {
    outputFile :: String,
    language :: CodeGenTarget,
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
  }
  | StageDiffCmd {
    againstFile :: String,
    samplesD :: [IRValue],
    paramsD :: [IRValue]
  } deriving Show

readLanguage :: ReadM CodeGenTarget
readLanguage = str >>= \s -> case map toLower s of
  "python" -> return TargetPython
  "py" -> return TargetPython
  "p" -> return TargetPython
  "julia" -> return TargetJulia
  "jul" -> return TargetJulia
  "jl" -> return TargetJulia
  "j" -> return TargetJulia
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
        <*> option auto
            ( long "marginalSlots"
            <> metavar "N"
            <> value defaultMarginalSlots
            <> showDefault
            <> help "Budget on how many ENUMERATED observation slots one function may have before the per-mask analysis declines it (design witnessed-per-query-capability). A function with k enumerated slots has 2^k masks, so this bounds per-mask work; over budget, the function is reported as over budget and compiles as it does today.")
        <*> option auto
            ( long "materializationBudget"
            <> metavar "N"
            <> value defaultMaterializationCardinality
            <> showDefault
            <> help "Cardinality budget for dense enumeration and marginal materialization (CompilerConfig.materializationCardinality). A discrete domain larger than N is never enumerated densely or tabulated: such a program goes through plan-guided enumeration, or is refused if that path does not cover it. Raising N is an explicit, per-invocation opt-in to the dense path for a program whose domain you know is affordable -- the emitted module grows with the domain, and can reach megabytes. 0 disables materialization (and dense enumeration of any non-empty domain) entirely.")
        <*> switch
            ( long "marginals"
            <> help "Print the observation-mask report before running the subcommand: per function, its leaf observation slots with their accessor paths, the correlation classes, which slots are enumerated and why, and the per-mask capability table (the projected pType of each masked program). Analysis only -- it changes nothing about what is compiled.")
        <*> switch
            ( long "duplicationCensus"
            <> help "Print the duplication census before running the subcommand (design ir-duplication-census): the program is compiled at -O0, and for every function body the report gives M, the copy count of its most-copied subtree of at least 30 IR nodes (binders up to renaming), and its most-copied subtrees with the fresh-name tags that usually name the compiler site that built them. A count that grows with the program's nesting depth is an exponential compile blowup in the making. Analysis only -- it changes nothing about what is compiled.")
        <*> switch
            ( long "memoRecursion"
            <> help "Memoise the probability and integrate functions of every function on a recursive call cycle, keyed on their argument values, for the duration of one top-level query (task recursive-prob-calls-not-shared-across-branches). A recursion that calls itself with the same arguments from several branches -- an HMM's likelihood over a latent state the query does not fix -- then costs one call per distinct (suffix, state) instead of one per path: linear instead of exponential. Python backends only (scalar and --batched); the Julia backend ignores it with a warning. Ignored under --topKCutoff, whose pruned probability depends on the path to a call. Off by default; without it the emitted code is unchanged.")
        <*> hsubparser (
          command "compile" (info parseCompileOpts (progDesc "Compiles the program with inference interface into target language"))
          <> command "generate" (info parseGenerateOpts (progDesc "Runs the generate pass of the program"))
          <> command "probability" (info parseProbabilityOpts (progDesc "Runs probabilistic inference on the program. Returns the probability of a given value to be the output of the program"))
          <> command "cumulative" (info parseIntegrateOpts (progDesc "Runs probabilistic inference on the program. Returns the probability of the program output to be less than the given sample"))
          <> command "stagediff" (info parseStageDiffOpts (progDesc "Compiles the input program and a second one that should denote the same distribution (a rewrite of it) side by side, and reports the first pipeline stage whose output differs more than the rewrite explains (design transformation-differential-testing, isolation loop). Exits 1 if some stage diverges."))
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


parseStageDiffOpts :: Parser CommandOpts
parseStageDiffOpts = StageDiffCmd
        <$> strOption
            ( long "against"
            <> short 'j'
            <> metavar "OTHER_FILE"
            <> help "The rewritten program, compared against the input file")
        <*> many (option readValue
            ( short 'x'
            <> metavar "SAMPLE"
            <> help "A sample to compare p(X=SAMPLE) of both programs at, at -O0 and at the given -O level. Repeatable. Without one, only the stages are compared."))
        <*> optionalList (option readValueList
            ( short 'p'
            <> metavar "PARAMS"
            <> help "Parameters passed to both main functions, as for probability."))

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
transpile (GlobalOpts {inputFile=inFile, verbosity=verb, Main.countBranches=cb, topKCutoff=tkc, commandOpts=options, optimiziationLevel=oLvl, pruneAnys=anyChecks, noInteg=nInteg, noProb=nProb, noGen=nGen, debugIntermediates=dbgInter, noTypeCheck=nTypeChk, batchedMode=batchedFlag, logSpaceMode=logSpaceFlag, optStatsMode=optStatsFlag, extraSemiringsMode=extraSR, marginalSlotsBudget=mSlots, materializationBudget=matBudget, marginalsReport=wantMarginals, duplicationReport=wantCensus, memoRecursionMode=memoRec}) = do
  prog <- parseProgram inFile
  let conf = (CompilerConfig {SPLL.IntermediateRepresentation.countBranches = cb, topKThreshold = tkc, verbose=verb, optimizerLevel=oLvl, pruneAnyChecks=anyChecks, noIntegrate=nInteg, noProbability=nProb,noGenerate=nGen, showIntermediates=dbgInter, checkQueryType=not nTypeChk, batched=batchedFlag, logSpace=logSpaceFlag, optStats=optStatsFlag, materializationCardinality=matBudget, marginalSlots=mSlots, extraSemirings=extraSR, memoRecursion=memoRec})
  reportMarginals wantMarginals conf prog
  reportDuplicationCensus wantCensus conf prog
  -- The compile-time warnings that read only the program (today: functions
  -- over the --marginalSlots budget), for every subcommand. 'compiledWarnings'
  -- below adds the ones that depend on what a compile emitted.
  mapM_ (hPutStrLn stderr . renderCompileWarning) (programWarnings conf prog)
  case options of
    CompileOpts{language=lang, outputFile=outFile, trunc=trnc} -> do
      -- 'codeGenToLang', split so the warnings read the same compile.
      case compile conf prog >>= \compiled -> (,) compiled <$> emitCompiled lang trnc conf compiled of
        Left err -> handleError err
        Right (compiled, trans) -> do
          mapM_ (hPutStrLn stderr . renderCompileWarning) (compiledWarnings conf prog compiled)
          mapM_ (hPutStrLn stderr) (memoRecursionIgnored lang conf)
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
          case val of
            -- The sampled program failed at run time (e.g. @head@ of an empty
            -- list); the interpreter answers that as a value, not a sample.
            VError msg -> handleError msg
            _ -> print ("X=" ++ show val)
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
    StageDiffCmd{againstFile=other, samplesD=xs, paramsD=params} -> do
      prog' <- parseProgram other
      -- The dumps of -d would interleave both compiles; the report replaces them.
      let quiet = conf { showIntermediates = False }
      report <- stageDiff (defaultStageDiffOpts quiet) { sdQueries = [ (x, params) | x <- xs ] } prog prog'
      putStr (renderStageReport report)
      maybe (return ()) (const (exitWith (ExitFailure 1))) (firstDivergence report)

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

-- | The @--marginals@ report (task observation-mask-analysis): the observation
-- tree's leaf slots, their correlation classes, which are enumerated and why,
-- and the per-mask capability table. Printed before the subcommand runs, since
-- it is a statement about the program rather than about what is compiled from
-- it.
reportMarginals :: Bool -> CompilerConfig -> Program -> IO ()
reportMarginals False _ _ = return ()
reportMarginals True conf prog =
  case marginalReport conf prog of
    Left err -> handleError err
    Right rs -> putStr (renderMarginalReport (adts prog) rs)

-- | The @--duplicationCensus@ report (design ir-duplication-census): the
-- program's -O0 IR, counted for repeated subtrees. Printed before the
-- subcommand, like @--marginals@; quiet, so @-d@ does not dump the extra
-- compile.
reportDuplicationCensus :: Bool -> CompilerConfig -> Program -> IO ()
reportDuplicationCensus False _ _ = return ()
reportDuplicationCensus True conf prog =
  case compile conf { optimizerLevel = 0, showIntermediates = False, verbose = 0 } prog of
    Left err -> handleError err
    Right env -> putStr (renderCensus defaultMinSize 3 (censusEnv defaultMinSize env))
