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
-- Besides @main@'s probability and integrate functions, the property also
-- evaluates the other two deterministic bodies of a group (task
-- @backend-agreement-writelogits-and-normal-functions@): a Gaussian function's
-- normal-parameter function (@QNormal@, its @(mu, sigma)@) and a
-- logit-representable function's writeLogits function (@QWriteLogits@, its
-- logit vector). Both answer a vector ('AnsweredVec'), compared element-wise
-- with 'probAgrees'. They take the function's own arguments rather than a
-- query point, so a query of either kind carries its arguments.
--
-- Also here: 'irConstructs', the construct inventory of emitted IR that the
-- coverage table and the corpus-minus-fuzz exception list are built from.
module BackendAgreement
  ( Query(..)
  , queryPoint
  , bodyKind
  , Answer(..)
  , AgreementCase(..)
  , Disagreement(..)
  , renderDisagreement
  , interpreterAnswer
  , interpreterBodyAnswer
  , probAgrees
  , answersAgree
  , anyHoles
  , offSupport
  , runPythonBatch
  , runJuliaBatch
  , findJulia
  , BatchedCase(..)
  , BatchedGroup(..)
  , prepareBatchedCase
  , runBatchedPythonBatch
  , batchedComparedBodies
  , batchedRefusalReason
  , float32Point
  , parseAnswerLine
  , pythonDriver
  , juliaDriver
  , irConstructs
  , irEnvConstructs
  , inferenceBodies
  , deterministicBodies
  , comparedBodies
  , maskedConstruct
  , allBodies
  ) where

import Control.Exception (SomeException, try, evaluate)
import Data.Char (toLower, isSpace)
import Data.List (intercalate, nub, sort, isPrefixOf)
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
import SPLL.Prelude (runProbC, runIntegC, runWriteLogitsRandC, compile)
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import SPLL.ReservedNames (componentNormalName)
import IRInterpreter (generateDet)
import Control.Monad.Random (evalRand)
import System.Random (mkStdGen)
import qualified SPLL.CodeGenPyTorch as Py
import qualified SPLL.CodeGenJulia as Jl
import PrettyPrint (pPrintProg)
import TestTolerances (probTolerance)
import End2EndTesting (qualifyConstructors, juliaTestFlags, SampleBatch(..), batchSamples,
                       batchSymColumn, networkMocks, batchedMockExpr, netMockName)

-- ---------------------------------------------------------------------------
-- Queries and answers

-- | A point to evaluate @main@'s probability function (@QProb@) or its
-- integrate function (@QInteg@) at; or a group's normal-parameter function
-- (@QNormal@) or writeLogits function (@QWriteLogits@), named by the group,
-- with the arguments the text backends take (a neural @main@'s mock envelope
-- already resolved, as 'acBackendArgs' is).
data Query = QProb IRValue | QInteg IRValue
           | QNormal String [IRValue] | QWriteLogits String [IRValue]
  deriving (Show, Eq)

-- | The argument list a backend calls the query's function with, given the
-- case's backend arguments for @main@.
callArgs :: [IRValue] -> Query -> [IRValue]
callArgs args (QProb v) = v : args
callArgs args (QInteg v) = v : args
callArgs _ (QNormal _ as) = as
callArgs _ (QWriteLogits _ as) = as

-- | The query point of an inference query. A body query has none; its first
-- argument stands in (only used for labelling).
queryPoint :: Query -> IRValue
queryPoint (QProb v) = v
queryPoint (QInteg v) = v
queryPoint q = case callArgs [] q of
  (v : _) -> v
  [] -> VAny

-- | Which body a query evaluates: @prob@, @integ@, @normal@ or @writeLogits@.
bodyKind :: Query -> String
bodyKind (QProb _) = "prob"
bodyKind (QInteg _) = "integ"
bodyKind (QNormal _ _) = "normal"
bodyKind (QWriteLogits _ _) = "writeLogits"

-- | What one engine said at one point. 'Raised' is any failure to produce a
-- number: an exception in the backend, a module that did not load, codegen
-- throwing on the Haskell side, or (for the interpreter) a 'Left'.
--
-- 'AnsweredVec' is a body query's vector: @[mu, sigma]@ or the logit vector.
-- A 'Nothing' slot is not compared: a writeLogits slot of a dead arm holds iid
-- noise (task @writelogits-dead-arm-nan@), recognised by the interpreter
-- answering it differently under two seeds.
data Answer = Answered Double Double Bool   -- ^ probability, dim, impossible
            | AnsweredVec [Maybe Double]
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
-- caller forces it under its own timeout. @args@ are @main@'s; a body query
-- takes its own and is answered by 'interpreterBodyAnswer' instead.
interpreterAnswer :: Program -> IREnv -> [IRValue] -> Query -> Maybe Answer
interpreterAnswer p env args q = case run of
  Just (Right r@(VProbDim pr d)) -> Just (Answered pr d (fromMaybe False (resultImpossible r)))
  _ -> Nothing
  where
    run = case q of
      QProb v  -> Just (runProbC p env args v)
      QInteg v -> Just (runIntegC p env args v)
      QNormal _ _ -> Nothing
      QWriteLogits _ _ -> Nothing

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
answersAgree (AnsweredVec xs) (AnsweredVec ys) = length xs == length ys && and (zipWith slot xs ys)
  where slot (Just a) (Just b) = probAgrees a b
        slot _ _ = True
answersAgree _ _ = False

-- | The interpreter's answer to a body query ('QNormal', 'QWriteLogits'),
-- given the arguments the interpreter takes (for a neural @main@ the mock
-- envelope, not the resolved vector the query carries). 'Nothing' where it
-- does not answer: no such body, a 'Left', or a result that is not a flat
-- vector of floats. Pure, like 'interpreterAnswer'.
interpreterBodyAnswer :: Program -> IREnv -> [IRValue] -> Query -> Maybe Answer
interpreterBodyAnswer p env args q = case q of
  QNormal g _ -> do
    (body, _) <- normalFun (lookupIREnv g env)
    case generateDet (neurals p) (writeLogitsDecls p) env (map IRConst args) body of
      Right (VTuple (VFloat m) (VFloat s)) -> Just (AnsweredVec [Just m, Just s])
      _ -> Nothing
  QWriteLogits g _ -> do
    xs <- floatsAt g 0
    ys <- floatsAt g 1
    if length xs /= length ys then Nothing else
      Just (AnsweredVec [ if x == y || (isNaN x && isNaN y) then Just x else Nothing | (x, y) <- zip xs ys ])
  _ -> Nothing
  where
    floatsAt g seed = case evalRand (runWriteLogitsRandC p env g args) (mkStdGen seed) of
      Right (VList l) -> mapM asFloat (listItems l)
      _ -> Nothing
    asFloat (VFloat x) = Just x
    asFloat _ = Nothing
    listItems (ListCont x xs) = x : listItems xs
    listItems _ = []

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
  , "def _vals(r):"
  , "    if hasattr(r, 't1') and hasattr(r, 't2'): return [r.t1, r.t2]"
  , "    return list(r)"
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
      , "        _r = eval(" ++ show (target q ++ "." ++ method q ++ "(" ++ intercalate ", " (map Py.pyVal (callArgs args q)) ++ ")") ++ ", _ns)"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out(" ++ output i j q ++ ")"
      , "    except BaseException as _e:"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('E " ++ show i ++ " " ++ show j ++ " ' + _msg(_e))"
      ]
    method (QProb _) = "forward"
    method (QInteg _) = "integrate"
    method (QNormal _ _) = "normal_params"
    method (QWriteLogits _ _) = "writeLogits"
    target (QNormal g _) = g
    target (QWriteLogits g _) = g
    target _ = "main"
    output i j q = case q of
      QProb _ -> rLine
      QInteg _ -> rLine
      _ -> "'V " ++ show i ++ " " ++ show j ++ " ' + ' '.join(repr(float(x)) for x in _vals(_r))"
      where rLine = "'R " ++ show i ++ " " ++ show j ++ " ' + repr(float(_r[0])) + ' ' + repr(float(_r[1][0])) + ' ' + str(bool(_r[1][1]))"

-- | The Julia driver; same output protocol as 'pythonDriver'. Each program is
-- a @module ProgN@ in its own file, @include@d inside a @try@ so a module
-- that fails to load reports @L@ and the rest still run. Calls go through
-- @Base.invokelatest@ because the module is defined at run time.
juliaDriver :: FilePath -> [(FilePath, [IRValue], [Query])] -> String
juliaDriver projectDir programs = unlines $
  [ "include(" ++ show (projectDir </> "juliaLib.jl") ++ ")"
  , "using .JuliaSPPLLib"
  , "_msg(e) = first(replace(sprint(showerror, e), '\\n' => ' '), 400)"
  , "_vals(r) = r isa JuliaSPPLLib.T ? [r.t1, r.t2] : collect(r)"
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
                       , "  r = Base.invokelatest(" ++ intercalate ", " ((modName ++ "." ++ fn q) : map jv (callArgs args q)) ++ ")"
                       , "  " ++ output i j q ++ "; flush(stdout)"
                       , "catch e"
                       , "  println(\"E " ++ show i ++ " " ++ show j ++ " \", _msg(e)); flush(stdout)"
                       , "end"
                       ]
                     | (j, q) <- zip [0 :: Int ..] qs ]
    fn (QProb _) = "main_prob"
    fn (QInteg _) = "main_integ"
    fn (QNormal g _) = g ++ "_normal"
    fn (QWriteLogits g _) = g ++ "_writeLogits"
    output i j q = case q of
      QProb _ -> rLine
      QInteg _ -> rLine
      _ -> "println(\"V " ++ show i ++ " " ++ show j ++ " \", join([repr(Float64(x)) for x in _vals(r)], \" \"))"
      where rLine = "println(\"R " ++ show i ++ " " ++ show j ++ " \", repr(Float64(r[1])), \" \", repr(Float64(r[2][1])), \" \", Bool(r[2][2]))"

-- | One line of driver output (@R@ an inference answer, @V@ a body query's
-- vector): @(program, Just query, answer)@ for a query,
-- @(program, Nothing, Raised msg)@ for a module that did not load.
parseAnswerLine :: String -> Maybe (Int, Maybe Int, Answer)
parseAnswerLine l = case words l of
  ("R" : i : j : p : d : imp : _) -> do
    i' <- readMaybe i; j' <- readMaybe j
    p' <- readNum p; d' <- readNum d; b <- readBool imp
    return (i', Just j', Answered p' d' b)
  ("V" : i : j : xs) -> do
    i' <- readMaybe i; j' <- readMaybe j
    vs <- mapM readNum xs
    return (i', Just j', AnsweredVec (map Just vs))
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
-- The batched arm (task backend-agreement-batched-arm)

-- | One batched call: all of a program's answered points of one inference
-- kind (@forward@ or @integrate@), handed over as one batch, the way the
-- corpus's @batched-vs-expected@ hands over a @.tst@ file's points
-- ('End2EndTesting.batchSamples': one structure-of-arrays tensor, or the host
-- bucketing wrapper when a point carries structure). Each query carries the
-- interpreter's answer and, for a point a float32 batch literal rounds, the
-- interpreter's answer at the rounded point ('float32Point').
data BatchedGroup = BatchedGroup
  { bgCumul   :: Bool
  , bgBatch   :: SampleBatch
  , bgQueries :: [(Query, Answer, Maybe Answer)]
  }

-- | A compared case that batched mode takes: its batched compile, the emitted
-- module and its groups.
data BatchedCase = BatchedCase
  { bcCase   :: AgreementCase
  , bcEnv    :: IREnv
  , bcSource :: String
  , bcGroups :: [BatchedGroup]
  }

-- | Batched eligibility, decided as the corpus decides it
-- ('End2EndTesting.batchedEligibility'): a @batched = True@ compile, a
-- 'generateFunctionsBatched' emission, and batchable query points. 'Left' is
-- the reason it is not eligible, normalised for tabulation
-- ('batchedRefusalReason'); a refusal is not a disagreement.
--
-- Only the inference queries go through this arm (the batched backend emits
-- no @normal_params@ or @writeLogits@), and of those not the ones the
-- interpreter answers with a NaN: every batched return goes through
-- @check_result@, which raises on a NaN by design (task
-- batched-adt-cdf-refusal-becomes-nan), and it would take the whole batch
-- with it. @interpArgs@ are what the interpreter takes for @main@.
prepareBatchedCase :: [IRValue] -> AgreementCase -> IO (Either String BatchedCase)
prepareBatchedCase interpArgs c = do
  compiled <- try (evaluate (forceEither (compile defaultCompilerConfig{batched = True} (acProgram c))))
  case compiled of
    Left (e :: SomeException) -> return (Left ("batched compile crashed: " ++ batchedRefusalReason (show e)))
    Right (Left msg) -> return (Left ("batched compile failed: " ++ batchedRefusalReason msg))
    Right (Right env) -> do
      emitted <- try (evaluate (forceEither (generateFunctionsBatched True env)))
      case emitted of
        Left (e :: SomeException) -> return (Left ("batched codegen crashed: " ++ batchedRefusalReason (show e)))
        Right (Left msg) -> return (Left (batchedRefusalReason msg))
        Right (Right src) -> do
          let kinds = [ (cumul, qs) | cumul <- [False, True], let qs = inference cumul, not (null qs) ]
          if null kinds then return (Left "no non-NaN inference answer") else
            case mapM (\(cumul, qs) -> (,,) cumul qs <$> batchSamples (map (queryPoint . fst) qs)) kinds of
              Nothing -> return (Left "query points not batchable")
              Just gs -> do
                groups <- mapM (\(cumul, qs, sb) -> BatchedGroup cumul sb <$> mapM (withRounded sb) qs) gs
                return (Right (BatchedCase c env (intercalate "\n" src) groups))
  where
    inference cumul = [ (q, a) | (q, a@(Answered pr _ _)) <- acQueries c, isCumul q == Just cumul, not (isNaN pr) ]
    isCumul (QProb _) = Just False
    isCumul (QInteg _) = Just True
    isCumul _ = Nothing
    forceEither :: Show a => Either String a -> Either String a
    forceEither r = length (show r) `seq` r
    -- Only a structure-of-arrays literal is float32 ('batchLiteral' leaves
    -- torch's default dtype); the bucketing wrapper packs at the runtime's
    -- float64.
    withRounded (SoA _) (q, a) =
      let v = queryPoint q
          v' = float32Point v
      in if v' == v then return (q, a, Nothing) else do
           r <- try (evaluate (forceShow (interpreterAnswer (acProgram c) (acEnv c) interpArgs (retarget q v'))))
           return (q, a, either (\(_ :: SomeException) -> Nothing) id r)
    withRounded _ (q, a) = return (q, a, Nothing)
    retarget (QInteg _) v = QInteg v
    retarget _ v = QProb v
    forceShow x = length (show x) `seq` x

-- | A query point as a float32 batch literal delivers it: every float leaf
-- rounded to the nearest float32. The corpus's structure-of-arrays literals
-- are float32 too, so this arm compares under the corpus's own float32
-- awareness: a batched answer agrees if it matches the interpreter at the
-- point, or at the rounded point.
float32Point :: IRValue -> IRValue
float32Point v = case v of
  VFloat x -> VFloat (realToFrac (realToFrac x :: Float))
  VTuple a b -> VTuple (float32Point a) (float32Point b)
  _ -> v

-- | A batched refusal, stripped of the program-specific names in it (group
-- names, generated identifiers), so the eligibility table groups refusals by
-- kind: the construct named after "fragment:" where there is one, else the
-- message with every word containing an underscore or a digit, and the
-- function name a message starts with, dropped.
batchedRefusalReason :: String -> String
batchedRefusalReason msg0 = take 90 $ case breakOn "outside the tensor fragment: " msg of
  Just rest -> "outside the tensor fragment: " ++ clause rest
  Nothing -> clause (unwords (filter generic (words msg)))
  where
    -- The kind of refusal, not its instance: up to a parenthesised detail
    -- (the offending constant) or the next sentence.
    clause = trim . upTo
    upTo (ch : rest)
      | ch `elem` "(.;" = []
      | ch == ':', take 1 rest == " " = []
      | ch == ' ', "CallStack" `isPrefixOf` rest = []
      | otherwise = ch : upTo rest
    upTo [] = []
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
    msg = dropPrefix "batched PyTorch codegen: " $ dropPrefix "batched mode: " $ (map (\ch -> if ch == '\n' then ' ' else ch) msg0)
    dropPrefix pre s = if pre `isPrefixOf` s then drop (length pre) s else s
    breakOn pat s
      | null s = Nothing
      | pat `isPrefixOf` s = Just (drop (length pat) s)
      | otherwise = breakOn pat (tail s)
    generic w = not (any (`elem` "_0123456789'") w)

-- | The bodies a batched case puts through the batched backend: every group's
-- probability and integrate body, from the batched compile (so after the
-- select pass: @IRSelect@ rather than @IRIf@ where it applied).
batchedComparedBodies :: BatchedCase -> [IRExpr]
batchedComparedBodies = inferenceBodies . bcEnv

-- | The batched driver: every case in one torch process, each module in its
-- own namespace with its network mocks ('End2EndTesting.batchedMockExpr'),
-- each group one call under a 20 s alarm. Same output protocol as
-- 'pythonDriver'; a group that raises reports every one of its queries.
batchedDriver :: FilePath -> [BatchedCase] -> String
batchedDriver projectDir cases = unlines $
  [ "import sys, signal"
  , "sys.path.insert(0, " ++ show projectDir ++ ")"
  , "import torch"
  , "from pythonLibBatched import bucketed"
  , "sys.setrecursionlimit(20000)"
  , "class _Timeout(Exception): pass"
  , "def _alarm(signum, frame): raise _Timeout('batch exceeded its time limit')"
  , "signal.signal(signal.SIGALRM, _alarm)"
  , "def _out(s):"
  , "    sys.stdout.write(s + '\\n'); sys.stdout.flush()"
  , "def _msg(e):"
  , "    return (type(e).__name__ + ': ' + str(e)).replace('\\n', ' ')[:400]"
  , "def _leaf(x, k):"
  , "    if torch.is_tensor(x):"
  , "        return x[k].item() if x.dim() > 0 else x.item()"
  , "    return x"
  ] ++ concat (zipWith program [0 :: Int ..] cases)
  where
    program i bc =
      let c = bcCase bc
          nets = networkMocks (acProgram c)
          offsets = scanl (+) 0 (map (length . bgQueries) (bcGroups bc))
      in [ "_ns = {}"
         , "try:"
         , "    exec(compile(" ++ show (bcSource bc) ++ ", " ++ show ("prog" ++ show i) ++ ", 'exec'), _ns)"
         ] ++ [ "    _ns[" ++ show (netMockName nm) ++ "] = " ++ batchedMockExpr nm | nm <- nets ] ++
         [ "    _ns['bucketed'] = bucketed"
         , "    _loaded = True"
         , "except BaseException as _e:"
         , "    _out('L " ++ show i ++ " ' + _msg(_e))"
         , "    _loaded = False"
         , "if _loaded:"
         ] ++ concat (zipWith (group i (not (null nets)) (acBackendArgs c)) offsets (bcGroups bc))
         ++ [ "    pass" ]
    group i neural args off g =
      let n = length (bgQueries g)
          method = if bgCumul g then "integrate" else "forward"
          params = concatMap ((", " ++) . paramExpr neural n) args
          (setup, call) = case bgBatch g of
            SoA lit -> ([], "main." ++ method ++ "(" ++ lit ++ params ++ ")")
            -- Evaluated inside the program's namespace: a sample may name
            -- the program's own ADT constructors.
            Bucketed lit _ -> ( [ "        _ns['_samples'] = eval(" ++ show lit ++ ", _ns)" ]
                              , "bucketed(main." ++ method ++ ", _samples" ++ params ++ ")" )
          ix = "str(" ++ show off ++ " + _k)"
      in [ "    try:"
         , "        signal.setitimer(signal.ITIMER_REAL, 20.0)"
         ] ++ setup ++
         [ "        _r = eval(" ++ show call ++ ", _ns)"
         , "        signal.setitimer(signal.ITIMER_REAL, 0)"
         , "        for _k in range(" ++ show n ++ "):"
         , "            try:"
         , "                _out('R " ++ show i ++ " ' + " ++ ix ++ " + ' ' + repr(float(_leaf(_r[0], _k))) + ' ' + repr(float(_leaf(_r[1][0], _k))) + ' ' + str(bool(_leaf(_r[1][1], _k))))"
         , "            except BaseException as _e:"
         , "                _out('E " ++ show i ++ " ' + " ++ ix ++ " + ' ' + _msg(_e))"
         , "    except BaseException as _e:"
         , "        signal.setitimer(signal.ITIMER_REAL, 0)"
         , "        for _k in range(" ++ show n ++ "):"
         , "            _out('E " ++ show i ++ " ' + " ++ ix ++ " + ' ' + _msg(_e))"
         ]
    -- A neural @main@'s argument is one logit vector shared by every point;
    -- batched, it is a @[B, n]@ column of it, as the corpus passes per-point
    -- symbols. Any other argument broadcasts.
    paramExpr neural n v
      | neural, VList _ <- v, Just col <- batchSymColumn (replicate n (VTuple (VInt 2) v)) = col
      | otherwise = Py.pyVal v

-- | Run every batched case through one torch-enabled Python process and pair
-- each query with the interpreter's answer. A batched answer agrees if it
-- agrees with the interpreter at the point or, for a float32-rounded point,
-- at the rounded point.
runBatchedPythonBatch :: FilePath -> [BatchedCase] -> IO [Disagreement]
runBatchedPythonBatch py cases = withSystemTempDirectory "nest-batched" $ \dir -> do
  projectDir <- getCurrentDirectory
  let driverPath = dir </> "driver.py"
  writeFile driverPath (batchedDriver projectDir cases)
  (_, out, err) <- runBounded py [driverPath]
  let parsed = [ x | Just x <- map parseAnswerLine (lines out) ]
      tailErr = oneLine (reverse (take 400 (reverse err)))
      answerFor i j = case [ a | (i', Just j', a) <- parsed, i' == i, j' == j ] of
        (a : _) -> a
        [] -> case [ a | (i', Nothing, a) <- parsed, i' == i ] of
          (a : _) -> a
          [] -> Raised ("no answer from the batched process; stderr: " ++ tailErr)
  return [ Disagreement "batched" (acProgram (bcCase bc)) q ia ba
         | (i, bc) <- zip [0 ..] cases
         , (j, (q, ia, rounded)) <- zip [0 ..] (concatMap bgQueries (bcGroups bc))
         , let ba = answerFor i j
         , not (answersAgree ia ba || maybe False (`answersAgree` ba) rounded) ]

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

-- | The probability, integrate, writeLogits and normal bodies of every group:
-- every body that has a value the backends can agree on. The corpus side of
-- 'BackendCoverage''s census.
deterministicBodies :: IREnv -> [IRExpr]
deterministicBodies (IREnv gs _ _) =
  [ b | g <- gs, Just (b, _) <- [probFun g, integFun g, writeLogitsFun g, normalFun g] ]

-- | The bodies a compared case puts through the backends: every group's
-- inference bodies (as 'inferenceBodies'; a helper's are reached through
-- @main@'s), the normal and writeLogits body of each group a query of that
-- kind was answered for, and, when any writeLogits query was, the per-tuple-
-- component normal functions a writeLogits body calls.
comparedBodies :: AgreementCase -> [IRExpr]
comparedBodies c = inferenceBodies env ++
  [ b | g <- gs, Just (b, _) <- [normalFun g], groupName g `elem` normals ] ++
  [ b | g <- gs, Just (b, _) <- [writeLogitsFun g], groupName g `elem` logits ] ++
  [ b | not (null logits), g <- gs, Just _ <- [componentNormalName (groupName g)], Just (b, _) <- [normalFun g] ]
  where
    env@(IREnv gs _ _) = acEnv c
    normals = [ g | (QNormal g _, _) <- acQueries c ]
    logits = [ g | (QWriteLogits g _, _) <- acQueries c ]

-- | A construct a compared body contains but the property does not certify: a
-- random draw in a writeLogits body (the noise of a dead arm, task
-- @writelogits-dead-arm-nan@). The property finds its slots by the
-- interpreter answering them differently under two seeds and leaves them out
-- of the comparison, so a draw's lowering is never checked. 'BackendCoverage'
-- removes it from the fuzz side, so it stays listed while the corpus uses it.
maskedConstruct :: String -> Bool
maskedConstruct c = c == "IRExpr:IRSample" || "Sample:" `isPrefixOf` c

-- | Every emitted body, generate and writeLogits included: what a corpus
-- program asks of the backends.
allBodies :: IREnv -> [IRExpr]
allBodies (IREnv gs _ _) =
  [ b | g <- gs, Just (b, _) <- [genFun g, probFun g, integFun g, writeLogitsFun g, normalFun g] ]

irEnvConstructs :: (IREnv -> [IRExpr]) -> IREnv -> [String]
irEnvConstructs which env = sort (nub (concatMap irConstructs (which env)))
