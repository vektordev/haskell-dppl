{-# LANGUAGE ScopedTypeVariables #-}

-- | Backend agreement (docs-repo task @backend-agreement-fuzzing@): the
-- machinery behind 'TestFuzz.prop_Fuzz_BackendsAgree'.
--
-- A batch of compiled programs, each with the query points the interpreter
-- answered at, is evaluated by the scalar Python backend in /one/ @python3@
-- process and by the Julia backend in /one/ @julia --compile=min@ process
-- (a Python check is a ~70 ms subprocess and a Julia one ~470 ms, against a
-- ~1 ms compile, so per-program processes would dominate the run). Each
-- backend prints one line per query point, and the answers are compared to
-- the interpreter's: 'probAgrees' on the probability, exact on the dimension
-- and the impossibility flag. A backend raising, failing to load the module,
-- or the codegen itself throwing, where the interpreter answered, is a
-- disagreement too.
--
-- Isolation is by construction rather than by luck: each program is loaded
-- into its own namespace (a fresh @dict@ for Python, its own @module ProgN@
-- for Julia), every load and every query is wrapped in its own
-- @try@, and results are flushed line by line, so one broken program
-- reports against itself and never takes its batch-mates down with it.
--
-- Also here: 'irConstructs', the construct inventory of emitted IR that the
-- coverage table and the corpus-minus-fuzz exception list are built from.
module BackendAgreement
  ( Query(..)
  , queryPoint
  , Answer(..)
  , AgreementCase(..)
  , Disagreement(..)
  , renderDisagreement
  , interpreterAnswer
  , probAgrees
  , answersAgree
  , anyHoles
  , offSupport
  , runPythonBatch
  , runJuliaBatch
  , findJulia
  , parseAnswerLine
  , pythonDriver
  , juliaDriver
  , irConstructs
  , irEnvConstructs
  , inferenceBodies
  , allBodies
  ) where

import Control.Exception (SomeException, try, evaluate)
import Data.Char (toLower, isSpace)
import Data.List (intercalate, nub, sort)
import Data.Maybe (fromMaybe)
import System.Directory (getCurrentDirectory, findExecutable)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Text.Read (readMaybe)
import Data.Text (pack, unpack, replace)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Prelude (runProbC, runIntegC)
import qualified SPLL.CodeGenPyTorch as Py
import qualified SPLL.CodeGenJulia as Jl
import PrettyPrint (pPrintProg)
import TestTolerances (probTolerance)
import End2EndTesting (qualifyConstructors, juliaTestFlags)

-- ---------------------------------------------------------------------------
-- Queries and answers

-- | A point to evaluate @main@'s probability function (@QProb@) or its
-- integrate function (@QInteg@) at.
data Query = QProb IRValue | QInteg IRValue
  deriving (Show, Eq)

queryPoint :: Query -> IRValue
queryPoint (QProb v) = v
queryPoint (QInteg v) = v

-- | What one engine said at one point. 'Raised' is any failure to produce a
-- number: an exception in the backend, a module that did not load, codegen
-- throwing on the Haskell side, or (for the interpreter) a 'Left'.
data Answer = Answered Double Double Bool   -- ^ probability, dim, impossible
            | Raised String
  deriving (Show, Eq)

-- | One compiled program and the points the interpreter answered at, with its
-- answers. @acInterpArgs@ are what the interpreter takes for @main@'s
-- parameters (a neural draw's mock-NN envelope); @acBackendArgs@ are the same
-- resolved to the raw logit vector the text backends' identity mock passes
-- through ('End2EndTesting.resolveNeuralParams').
data AgreementCase = AgreementCase
  { acProgram     :: Program
  , acEnv         :: IREnv
  , acBackendArgs :: [IRValue]
  , acNets        :: [String]
  , acQueries     :: [(Query, Answer)]
  }

data Disagreement = Disagreement
  { dBackend  :: String
  , dProgram  :: Program
  , dQuery    :: Query
  , dInterp   :: Answer
  , dBackendA :: Answer
  }

renderDisagreement :: Disagreement -> String
renderDisagreement d = unlines
  [ "BACKEND DISAGREEMENT (" ++ dBackend d ++ ") at " ++ show (dQuery d)
  , "  interpreter: " ++ show (dInterp d)
  , "  " ++ dBackend d ++ ": " ++ show (dBackendA d)
  , "PROGRAM:"
  , pPrintProg (dProgram d)
  ]

-- | The interpreter's answer at a query, or 'Nothing' where it does not
-- answer (a refusal, a missing variant, a malformed result). Pure; the
-- caller forces it under its own timeout.
interpreterAnswer :: Program -> IREnv -> [IRValue] -> Query -> Maybe Answer
interpreterAnswer p env args q = case run of
  Right r@(VProbDim pr d) -> Just (Answered pr d (fromMaybe False (resultImpossible r)))
  _ -> Nothing
  where
    run = case q of
      QProb v  -> runProbC p env args v
      QInteg v -> runIntegC p env args v

-- | Probabilities agree when both are NaN, both are the same infinity, or
-- they are within 'probTolerance', relative above 1 (a density can be large,
-- and a fixed absolute tolerance on 1e4 would be a demand for bit-equality).
probAgrees :: Double -> Double -> Bool
probAgrees a b
  | isNaN a || isNaN b = isNaN a && isNaN b
  | isInfinite a || isInfinite b = a == b
  | otherwise = abs (a - b) <= probTolerance * max 1 (max (abs a) (abs b))

answersAgree :: Answer -> Answer -> Bool
answersAgree (Answered p1 d1 i1) (Answered p2 d2 i2) = probAgrees p1 p2 && d1 == d2 && i1 == i2
answersAgree _ _ = False

-- ---------------------------------------------------------------------------
-- Query points beyond the drawn samples

-- | Marginal variants of a sample: the whole point @ANY@, and each component
-- of a tuple (recursively) or an ADT field replaced by @ANY@ in turn. Lists
-- and @Either@ payloads are left alone: the observation-mask machinery
-- answers a partial list query through a different route and a sample's
-- 'Either' arm is better probed by 'offSupport'.
anyHoles :: IRValue -> [IRValue]
anyHoles v = VAny : inner v
  where
    inner (VTuple a b) = [VTuple a' b | a' <- anyHoles a] ++ [VTuple a b' | b' <- anyHoles b]
    inner (VADT c fs) = [ VADT c (take i fs ++ [f'] ++ drop (i + 1) fs)
                        | (i, f) <- zip [0 ..] fs, f' <- anyHoles f ]
    inner _ = []

-- | Points near a sample that are often off its support: scalars nudged
-- (a non-lattice offset for a float, an implausibly large int, the other
-- boolean), an 'Either' moved to the other arm, a list grown by one element.
-- Only one leaf changes per variant, so a structured point stays mostly
-- on-support and still reaches deep code.
offSupport :: IRValue -> [IRValue]
offSupport v = case v of
  VFloat x -> [VFloat (x + 0.3721)]
  VInt n -> [VInt (n + 7)]
  VBool b -> [VBool (not b)]
  VTuple a b -> [VTuple a' b | a' <- offSupport a] ++ [VTuple a b' | b' <- offSupport b]
  VEither (Left a) -> VEither (Right a) : [VEither (Left a') | a' <- offSupport a]
  VEither (Right b) -> VEither (Left b) : [VEither (Right b') | b' <- offSupport b]
  VList (ListCont x xs) -> [VList (ListCont x (ListCont x xs))]
  _ -> []

-- ---------------------------------------------------------------------------
-- Emitting and running the batch

-- | Force a codegen result, catching a Haskell-side exception as text.
forcedSource :: IO [String] -> IO (Either String String)
forcedSource act = do
  r <- try (act >>= \ls -> evaluate (length (concat ls)) >> return ls)
  return $ case r of
    Left (e :: SomeException) -> Left (oneLine (show e))
    Right ls -> Right (intercalate "\n" ls)

oneLine :: String -> String
oneLine = take 400 . map (\c -> if c == '\n' then ' ' else c)

-- | The Python driver. @programs@ holds, per program, the path of its emitted
-- module (already prefixed with its identity mocks), the backend arguments
-- and the queries. Output lines: @R i j prob dim imposs@, @E i j message@,
-- @L i message@ (the module did not load).
pythonDriver :: FilePath -> [(FilePath, [IRValue], [Query])] -> String
pythonDriver projectDir programs = unlines $
  [ "import sys, signal"
  , "sys.path.insert(0, " ++ show projectDir ++ ")"
  , "sys.setrecursionlimit(20000)"
  , "class _Timeout(Exception): pass"
  , "def _alarm(signum, frame): raise _Timeout('query exceeded its time limit')"
  , "signal.signal(signal.SIGALRM, _alarm)"
  , "def _out(s):"
  , "    sys.stdout.write(s + '\\n'); sys.stdout.flush()"
  , "def _msg(e):"
  , "    return (type(e).__name__ + ': ' + str(e)).replace('\\n', ' ')[:400]"
  ] ++ concat (zipWith program [0 :: Int ..] programs)
  where
    program i (path, args, qs) =
      [ "_ns = {}"
      , "try:"
      , "    exec(compile(open(" ++ show path ++ ").read(), " ++ show path ++ ", 'exec'), _ns)"
      , "    _loaded = True"
      , "except BaseException as _e:"
      , "    _out('L " ++ show i ++ " ' + _msg(_e))"
      , "    _loaded = False"
      , "if _loaded:"
      ] ++ concat (zipWith (query i args) [0 :: Int ..] qs)
      ++ ["    pass"]
    query i args j q =
      [ "    try:"
      , "        signal.setitimer(signal.ITIMER_REAL, 10.0)"
      -- Evaluated inside the program's namespace: a query point names the
      -- program's own ADT constructor classes.
      , "        _r = eval(" ++ show ("main." ++ method q ++ "(" ++ intercalate ", " (map Py.pyVal (queryPoint q : args)) ++ ")") ++ ", _ns)"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('R " ++ show i ++ " " ++ show j ++ " ' + repr(float(_r[0])) + ' ' + repr(float(_r[1][0])) + ' ' + str(bool(_r[1][1])))"
      , "    except BaseException as _e:"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('E " ++ show i ++ " " ++ show j ++ " ' + _msg(_e))"
      ]
    method (QProb _) = "forward"
    method (QInteg _) = "integrate"

-- | The Julia driver; same output protocol as 'pythonDriver'. Each program is
-- a @module ProgN@ in its own file, @include@d inside a @try@ so a module
-- that fails to load reports @L@ and the rest still run. Calls go through
-- @Base.invokelatest@ because the module is defined at run time.
juliaDriver :: FilePath -> [(FilePath, [IRValue], [Query])] -> String
juliaDriver projectDir programs = unlines $
  [ "include(" ++ show (projectDir </> "juliaLib.jl") ++ ")"
  , "using .JuliaSPPLLib"
  , "_msg(e) = first(replace(sprint(showerror, e), '\\n' => ' '), 400)"
  ] ++ concat (zipWith program [0 :: Int ..] programs)
  where
    program i (path, args, qs) =
      let modName = "Prog" ++ show i
          jv = Jl.juliaVal . qualifyConstructors modName
      in [ "try"
         , "  include(" ++ show path ++ ")"
         , "catch e"
         , "  println(\"L " ++ show i ++ " \", _msg(e)); flush(stdout)"
         , "end"
         ] ++ concat [ [ "try"
                       , "  r = Base.invokelatest(" ++ modName ++ "." ++ fn q ++ ", " ++ intercalate ", " (map jv (queryPoint q : args)) ++ ")"
                       , "  println(\"R " ++ show i ++ " " ++ show j ++ " \", repr(Float64(r[1])), \" \", repr(Float64(r[2][1])), \" \", Bool(r[2][2])); flush(stdout)"
                       , "catch e"
                       , "  println(\"E " ++ show i ++ " " ++ show j ++ " \", _msg(e)); flush(stdout)"
                       , "end"
                       ]
                     | (j, q) <- zip [0 :: Int ..] qs ]
    fn (QProb _) = "main_prob"
    fn (QInteg _) = "main_integ"

-- | One line of driver output: @(program, Just query, answer)@ for a query,
-- @(program, Nothing, Raised msg)@ for a module that did not load.
parseAnswerLine :: String -> Maybe (Int, Maybe Int, Answer)
parseAnswerLine l = case words l of
  ("R" : i : j : p : d : imp : _) -> do
    i' <- readMaybe i; j' <- readMaybe j
    p' <- readNum p; d' <- readNum d; b <- readBool imp
    return (i', Just j', Answered p' d' b)
  ("E" : i : j : _) -> do
    i' <- readMaybe i; j' <- readMaybe j
    return (i', Just j', Raised (dropFields 3 l))
  ("L" : i : _) -> do
    i' <- readMaybe i
    return (i', Nothing, Raised ("module did not load: " ++ dropFields 2 l))
  _ -> Nothing
  where
    dropFields n = dropWhile isSpace . go n
      where go 0 s = s
            go k s = go (k - 1 :: Int) (dropWhile (not . isSpace) (dropWhile isSpace s))
    readBool s = case map toLower s of
      "true" -> Just True
      "false" -> Just False
      _ -> Nothing

-- | Python's @repr@ and Julia's @repr@ of a Float64, read back exactly:
-- @inf@/@Inf@, @nan@/@NaN@, an exponent with an explicit @+@, and Python's
-- @1e-05@ (no fractional part) all have to be handled, none of which
-- 'read' accepts.
readNum :: String -> Maybe Double
readNum s0 = case map toLower s0 of
  "inf" -> Just (1 / 0)
  "-inf" -> Just (-1 / 0)
  "nan" -> Just (0 / 0)
  "-nan" -> Just (0 / 0)
  s -> readMaybe (fixup s)
  where
    fixup s = let (mant, ex) = break (== 'e') s
                  mant' = if '.' `elem` mant then mant else mant ++ ".0"
                  ex' = case ex of
                          ('e' : '+' : r) -> 'e' : r
                          _ -> ex
              in mant' ++ ex'

-- | Run one batch through a backend: emit every program's source, run the
-- driver once, and pair every interpreter answer with the backend's.
-- A query with no output line (the process died or timed out before it) is
-- 'Raised' with the process's own stderr tail.
runBatch :: String
         -> (AgreementCase -> IO (Either String String))   -- ^ emitted module text
         -> String                                        -- ^ module file extension
         -> (FilePath -> [(FilePath, [IRValue], [Query])] -> String)
         -> (FilePath -> IO (ExitCode, String, String))    -- ^ run the driver file
         -> [AgreementCase] -> IO [Disagreement]
runBatch backend emit ext driver runDriver cases =
  withSystemTempDirectory ("nest-" ++ backend) $ \dir -> do
    projectDir <- getCurrentDirectory
    sources <- mapM emit cases
    let files = [ dir </> ("prog" ++ show i ++ ext) | i <- [0 .. length cases - 1] ]
    sequence_ [ writeFile f s | (f, Right s) <- zip files sources ]
    let entries = [ (f, acBackendArgs c, map fst (acQueries c))
                  | (f, c, Right _) <- zip3 files cases sources ]
        -- Programs whose codegen threw are not in the driver; keep the
        -- driver's indices aligned with 'entries', not with 'cases'.
        emitted = [ c | (c, Right _) <- zip cases sources ]
        failedGen = [ (c, e) | (c, Left e) <- zip cases sources ]
        driverPath = dir </> ("driver" ++ ext)
    writeFile driverPath (driver projectDir entries)
    (_, out, err) <- runDriver driverPath
    let parsed = [ x | Just x <- map parseAnswerLine (lines out) ]
        tailErr = oneLine (reverse (take 400 (reverse err)))
        answerFor i j = case [ a | (i', Just j', a) <- parsed, i' == i, j' == j ] of
          (a : _) -> a
          [] -> case [ a | (i', Nothing, a) <- parsed, i' == i ] of
            (a : _) -> a
            [] -> Raised ("no answer from the " ++ backend ++ " process; stderr: " ++ tailErr)
        fromRun = [ Disagreement backend (acProgram c) q ia ba
                  | (i, c) <- zip [0 ..] emitted
                  , (j, (q, ia)) <- zip [0 ..] (acQueries c)
                  , let ba = answerFor i j
                  , not (answersAgree ia ba) ]
        fromGen = [ Disagreement backend (acProgram c) q ia (Raised ("codegen threw: " ++ e))
                  | (c, e) <- failedGen, (q, ia) <- acQueries c ]
    return (fromGen ++ fromRun)

-- | A whole-process bound on top of the Python driver's per-query alarm:
-- a hang in a module's top level, or in Julia (which has no per-query bound),
-- must still end the batch. Generous, because a batch is many programs.
processTimeoutMicros :: Int
processTimeoutMicros = 300 * 1000 * 1000

runBounded :: String -> [String] -> IO (ExitCode, String, String)
runBounded exe args = do
  r <- timeout processTimeoutMicros (readProcessWithExitCode exe args "")
  return (fromMaybe (ExitFailure 124, "", exe ++ " exceeded " ++ show processTimeoutMicros ++ "us") r)

-- | The scalar Python backend, as End2End's Python group runs it: torch's
-- @Module@ stubbed out (the scalar backend never uses torch), plus an identity
-- mock per declared network.
runPythonBatch :: [AgreementCase] -> IO [Disagreement]
runPythonBatch = runBatch "python" emit ".py" pythonDriver (\f -> runBounded "python3" [f])
  where
    emit c = fmap (fmap (\src -> mocks c ++ stubTorch src))
                  (forcedSource (return (Py.generateFunctions True (acEnv c))))
    mocks c = concatMap (\nm -> "def " ++ nm ++ "(s):\n    return s\n") (acNets c)
    stubTorch = unpack . replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") . pack

-- | 'Nothing' when no @julia@ is on the PATH; the caller then skips the arm
-- with a note, as the batched groups do for a missing torch.
findJulia :: IO (Maybe FilePath)
findJulia = findExecutable "julia"

runJuliaBatch :: FilePath -> [AgreementCase] -> IO [Disagreement]
runJuliaBatch julia cases = runBatch "julia" emit ".jl" juliaDriver (\f -> runBounded julia (juliaTestFlags ++ [f])) cases
  where
    indexed = zip [0 :: Int ..] cases
    emit c = do
      let i = head [ k | (k, c') <- indexed, sameCase c c' ]
          modName = "Prog" ++ show i
      fmap (fmap (\src -> "module " ++ modName ++ "\nusing ..JuliaSPPLLib\n"
                           ++ concatMap (\nm -> nm ++ "(s) = s\n") (acNets c)
                           ++ src ++ "\nend\n"))
           (forcedSource (return (Jl.generateFunctions (acEnv c))))
    -- Cases have no identity of their own; programs in one batch are
    -- distinct draws, so their printed forms are distinct enough to index by.
    sameCase a b = show (acProgram a) == show (acProgram b) && map fst (acQueries a) == map fst (acQueries b)

-- ---------------------------------------------------------------------------
-- Construct inventory

-- | Every IR construct a body uses, as a label naming its kind:
-- @IRExpr:IRIf@, @Operand:OpPlus@, @UnaryOperand:OpExp@, @Builtin:BReduce ROpAdd@,
-- @Distribution:IRNormal Log@ (density/cumulative leaves, with their log-space
-- flag), @Sample:IRUniform@, @ConTag:TgCons@, @Accessor:AcHead@. These are the
-- axes along which the two text backends' lowerings differ case by case.
irConstructs :: IRExpr -> [String]
irConstructs e = nub (go e)
  where
    go x = here x ++ concatMap go (getIRSubExprs x) ++ inValues x
    here x = ("IRExpr:" ++ ctor (show x)) : case x of
      IROp op _ _ -> ["Operand:" ++ show op]
      IRUnaryOp op _ -> ["UnaryOperand:" ++ show op]
      IRBuiltin b _ -> ["Builtin:" ++ builtinLabel b]
      IRDensity d ls _ -> ["Density:" ++ show d ++ " " ++ show ls]
      IRCumulative d ls _ -> ["Cumulative:" ++ show d ++ " " ++ show ls]
      IRSample d -> ["Sample:" ++ show d]
      IRConstruct t _ -> ["ConTag:" ++ show t]
      IRDestruct a _ -> ["Accessor:" ++ ctor (show a)]
      _ -> []
    -- A closure or a lambda-valued constant carries IR of its own.
    inValues (IRConst v) = concatMap go (valueExprs v)
    inValues _ = []
    ctor = takeWhile (not . isSpace)
    builtinLabel b = case b of
      BReduce op _ -> "BReduce " ++ show op
      BZip op -> "BZip " ++ show op
      _ -> ctor (show b)

valueExprs :: IRValue -> [IRExpr]
valueExprs v = case v of
  VTuple a b -> valueExprs a ++ valueExprs b
  VEither (Left a) -> valueExprs a
  VEither (Right b) -> valueExprs b
  VList l -> listExprs l
  VADT _ fs -> concatMap valueExprs fs
  VClosure _ _ body -> [body]
  _ -> []
  where
    listExprs (ListCont x xs) = valueExprs x ++ listExprs xs
    listExprs _ = []

-- | The probability and integrate bodies of every group: what
-- 'prop_Fuzz_BackendsAgree' actually evaluates in both backends.
inferenceBodies :: IREnv -> [IRExpr]
inferenceBodies (IREnv gs _ _) = [ b | g <- gs, Just (b, _) <- [probFun g, integFun g] ]

-- | Every emitted body, generate and writeLogits included: what a corpus
-- program asks of the backends.
allBodies :: IREnv -> [IRExpr]
allBodies (IREnv gs _ _) =
  [ b | g <- gs, Just (b, _) <- [genFun g, probFun g, integFun g, writeLogitsFun g, normalFun g] ]

irEnvConstructs :: (IREnv -> [IRExpr]) -> IREnv -> [String]
irEnvConstructs which env = sort (nub (concatMap irConstructs (which env)))
