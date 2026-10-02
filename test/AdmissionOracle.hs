-- | The admission-totality oracle (task @admission-totality-property@, phase P0
-- of design @pipeline-coherence@).
--
-- The mid-pipeline rests on one contract that two independent authorities
-- maintain by hand: **if the modality engine admits a function, the IR compiler
-- compiles it and the result evaluates; if the engine refuses it, @generate@
-- still works.** "Admits" is a top-level binding's own @pType@ being one of the
-- four rungs 'SPLL.IRCompiler.envToIRUnoptimized'' compiles a probability and
-- an integrate function for ('Deterministic', 'PNormal', 'PLogNormal',
-- 'Integrate'); "refuses" is 'Bottom'. Every row of @pipeline-coherence@'s F2
-- table is a violation of the first half: the lattice promised a closed form,
-- no IR equation builds it, and the compiler crashes (or the emitted function
-- does at run time).
--
-- 'admissionCheck' states that contract for one program. It reads the
-- verdicts from 'SPLL.Prelude.admissionTyped' -- the very program the variant
-- gate reads -- so it knows what was admitted even when the compile it then
-- checks throws. Each admitted function is evaluated in both inference modes
-- at a point drawn from its own @generate@, and each evaluation lands in one of
-- three buckets ('Outcome'): a value, a refusal through the error channel (a
-- @Left@, or an 'IRError' surfacing as a 'VError'), or a crash -- a Haskell
-- exception of any other kind. Crash is the contract violation. A refusal is
-- not, today: it is the precision metric @static-refusals-become-absent-variants@
-- turns into one (an admitted node refusing at run time means the lattice
-- over-promised, the F2 class in its graceful form), so the fuzz property
-- tabulates it rather than failing on it.
--
-- Not in scope, deliberately: whether any value is *right*. The @.tst@ files
-- and @SamplingMatchesPDF@ own correctness; this is crash-freedom and
-- existence.
module AdmissionOracle
  ( Mode(..)
  , Outcome(..)
  , Check(..)
  , AdmissionReport(..)
  , admitted
  , admissionCheck
  , violations
  , refusals
  , outcomeBucket
  , canonicalValue
  , renderViolation
  ) where

import Control.Exception (try, evaluate, throwIO, fromException, SomeException, SomeAsyncException(..))
import Control.Monad.Random (evalRandIO)
import Data.List (find, isPrefixOf)
import Data.Maybe (isJust)

import SPLL.Lang.Types
import SPLL.Lang.Lang (getTypeInfo)
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.PType (PType(..))
import SPLL.IntermediateRepresentation
import SPLL.Prelude (compile, admissionTyped, runGenNamedC, runProbNamedC, runIntegNamedC)

-- | Which compiled variant a check exercised.
data Mode = ModeCompile | ModeGenerate | ModeProbability | ModeIntegrate
  deriving (Show, Eq, Ord)

-- | What one exercised variant did.
data Outcome
  = Value
    -- ^ Evaluated to a result.
  | Refusal String
    -- ^ Answered through the error channel: a @Left@ from a runner, a 'VError'
    -- result, or an admitted variant that is absent outright.
  | Crash String
    -- ^ A Haskell exception (@error@, a failed pattern match, ...). The
    -- violation this oracle exists for.
  | Skipped String
    -- ^ Nothing to check: no argument could be built for a parameter, or the
    -- sampled program itself failed at run time (a partial destructor out of
    -- its domain, which is a well-typed program's legitimate behaviour).
  deriving (Show, Eq)

-- | One exercised variant of one top-level function.
data Check = Check
  { ckFunction :: String
  , ckPType    :: PType
  , ckMode     :: Mode
  , ckOutcome  :: Outcome
  } deriving (Show, Eq)

data AdmissionReport
  = NotTyped String
    -- ^ The program did not reach the modality engine's verdict: rejected
    -- (a @Left@ before IR compilation) or crashed before it. Neither is this
    -- contract's business -- @TypedCompileNeverCrashes@ owns the second.
  | Checked [(String, PType)] [Check]
    -- ^ The engine's verdict per top-level function, and every check made.
  deriving (Show)

-- | The four rungs 'SPLL.IRCompiler.envToIRUnoptimized'' compiles a
-- probability and an integrate function for.
admitted :: PType -> Bool
admitted pt = pt `elem` [Deterministic, PNormal, PLogNormal, Integrate]

-- | Catch only synchronous exceptions, so a per-case 'System.Timeout.timeout'
-- around the caller still cancels it (see @TestFuzz.trySync@).
trySync :: IO a -> IO (Either SomeException a)
trySync act = do
  r <- try act
  case r of
    Left e | Just (SomeAsyncException _) <- fromException e -> throwIO e
    _ -> return r

-- | `show` forces every field, so a crash hidden in a lazy thunk surfaces here
-- rather than in whoever prints the value later.
forceShow :: Show a => a -> a
forceShow x = length (show x) `seq` x

-- | The violations in a report: every crash, plus an admitted variant that is
-- absent ('absentNote').
violations :: AdmissionReport -> [Check]
violations (NotTyped _) = []
violations (Checked _ cs) = [ c | c <- cs, isViolation (ckOutcome c) ]
  where isViolation (Crash _) = True
        isViolation (Refusal msg) = msg == absentNote
        isViolation _ = False

refusals :: AdmissionReport -> [Check]
refusals (NotTyped _) = []
refusals (Checked _ cs) = [ c | c@Check{ckOutcome = Refusal msg} <- cs, msg /= absentNote ]

-- | The tabulation bucket of an outcome.
outcomeBucket :: Outcome -> String
outcomeBucket Value       = "value"
outcomeBucket (Refusal _) = "refusal"
outcomeBucket (Crash _)   = "crash"
outcomeBucket (Skipped _) = "skipped"

absentNote :: String
absentNote = "admitted, but the compiled group has no such function"

renderViolation :: Check -> String
renderViolation (Check f pt m o) =
  "function " ++ show f ++ " (pType " ++ show pt ++ "), mode " ++ show m ++ ": " ++ firstLine o
  where
    -- The exception's text up to its call stack, which names only the
    -- interpreter's own recursion and buries the message.
    firstLine (Crash msg) = "Crash: " ++ takeWhile (/= '\n') msg
    firstLine other       = show other

-- | Check the admission contract on one program.
--
-- @args@ supplies @main@'s arguments (empty for a nullary @main@; a fuzz draw
-- with a neural declaration needs its mock-network symbol). Every other
-- function's parameters are filled with 'canonicalValue's of their types, and a
-- function with a parameter no value can be built for (an arrow, a symbol) is
-- checked for existence only.
admissionCheck :: CompilerConfig -> Program -> [IRValue] -> IO AdmissionReport
admissionCheck conf p mainArgs = do
  typed <- trySync (evaluate (forceShow (admissionTyped conf p)))
  case typed of
    Left e -> do
      msg <- describe e
      return (NotTyped ("crashed before the verdict: " ++ msg))
    Right (Left err) -> return (NotTyped ("rejected: " ++ err))
    Right (Right tp) -> do
      let verdicts = [ (nm, pType (getTypeInfo b)) | (nm, b) <- functions tp ]
      compiled <- trySync (evaluate (forceShow (compile conf p)))
      checks <- case compiled of
        Left e -> describe e >>= compileCrash verdicts
        Right (Left err) ->
          -- Typing succeeded, so this refusal came from IR compilation itself.
          return [ Check nm pt ModeCompile (Refusal err) | (nm, pt) <- verdicts ]
        Right (Right env) -> concat <$> mapM (checkFunction tp env) verdicts
      return (Checked verdicts checks)
  where
    -- A crash forcing the whole compile cannot be pinned to one function's
    -- variant directly: the generate-backed guard and the optimizer both walk
    -- every group. Recompiling generate-only separates the two halves of the
    -- contract: if that succeeds, an admitted function's inference variant is
    -- what crashed; if it does not, generate did.
    compileCrash verdicts msg = do
      genOnly <- trySync (evaluate (forceShow (compile conf { noProbability = True, noIntegrate = True } p)))
      let genOk = case genOnly of
            Right (Right _) -> True
            _               -> False
          blamed
            | genOk     = [ (nm, pt,  ModeProbability) | (nm, pt) <- verdicts, admitted pt ]
            | otherwise = [ (nm, pt,  ModeGenerate) | (nm, pt) <- verdicts ]
      return [ Check nm pt m (Crash ("compile (generate-only " ++ (if genOk then "succeeds" else "crashes too") ++ "): " ++ msg)) | (nm, pt, m) <- blamed ]

    checkFunction tp env (nm, pt) = case find ((== nm) . groupName) (groups env) of
      Nothing -> return [Check nm pt ModeCompile (Refusal "no compiled group")]
      Just grp
        | admitted pt, not (isJust (probFun grp)) -> return [Check nm pt ModeProbability (Refusal absentNote)]
        | admitted pt, not (isJust (integFun grp)) -> return [Check nm pt ModeIntegrate (Refusal absentNote)]
        | not (isJust (genFun grp)) -> return [Check nm pt ModeGenerate (Refusal "refused, and generate is absent too")]
        | otherwise -> case argsFor tp nm of
            Nothing -> return [Check nm pt ModeGenerate (Skipped "no argument value for a parameter")]
            Just as -> do
              sampled <- trySync (evalRandIO (runGenNamedC p env nm as) >>= evaluate . forceShow)
              case sampled of
                Left e -> do
                  msg <- describe e
                  return $ case irErrorRaise msg of
                    Just m  -> [Check nm pt ModeGenerate (Skipped ("sample raised: " ++ m))]
                    Nothing -> [Check nm pt ModeGenerate (Crash msg)]
                Right (VError msg) -> return [Check nm pt ModeGenerate (Skipped ("sample failed at run time: " ++ msg))]
                Right x
                  | admitted pt -> do
                      pr <- infer (runProbNamedC p env nm as x)
                      ig <- infer (runIntegNamedC p env nm as x)
                      return [ Check nm pt ModeGenerate Value
                             , Check nm pt ModeProbability pr
                             , Check nm pt ModeIntegrate ig ]
                  | otherwise -> return [Check nm pt ModeGenerate Value]

    infer r = do
      out <- trySync (evaluate (forceShow r))
      case out of
        Left e -> do
          msg <- describe e
          return $ maybe (Crash msg) Refusal (irErrorRaise msg)
        Right (Left err)          -> return (Refusal err)
        Right (Right (VError m))  -> return (Refusal m)
        Right (Right _)           -> return Value

    groups (IREnv gs _ _) = gs

    argsFor tp nm
      | nm == "main" = Just mainArgs
      | otherwise = do
          b <- lookup nm (functions tp)
          mapM (canonicalValue (adts tp)) (paramTypes b)

-- | An exception's message, fully forced. The message of an @error@ is itself
-- a lazy string, and the compiler builds some of them by 'show'ing a value
-- that throws in turn, so rendering one can raise a second exception -- after
-- the 'trySync' that caught the first, where it would escape the oracle. A
-- message that throws is replaced by the one it throws (a few levels deep).
describe :: SomeException -> IO String
describe = go (3 :: Int)
  where
    go depth e = do
      r <- trySync (evaluate (forceShow (show e)))
      case r of
        Right msg -> return msg
        Left inner
          | depth > 0 -> ("(while rendering an exception) " ++) <$> go (depth - 1) inner
          | otherwise -> return "(an exception whose message keeps throwing)"

-- | An 'IRError' node the compiler emitted on purpose, raised by the
-- interpreter. 'IRInterpreter' deliberately throws it rather than answering
-- 'Left' (see its comment at the 'IRError' equation: a run-time failure of the
-- user's program, as the text backends render it with a raise), so this is the
-- one exception that is a refusal rather than a crash. Recognised by the
-- interpreter's own prefix, which nothing else produces.
irErrorRaise :: String -> Maybe String
irErrorRaise msg = case breakOn "Error during interpretation: " msg of
  Just rest -> Just (takeWhile (/= '\n') rest)
  Nothing   -> Nothing
  where
    breakOn needle hay
      | needle `isPrefixOf` hay = Just (drop (length needle) hay)
      | null hay = Nothing
      | otherwise = breakOn needle (tail hay)

-- | The parameter types of a binding, read off its leading lambdas.
paramTypes :: Expr -> [RType]
paramTypes (Expr ti (Lambda _ body)) = case rType ti of
  TArrow a _ -> a : paramTypes body
  _          -> []
paramTypes _ = []

-- | A fixed, small value of a type, for a function parameter: the oracle needs
-- *a* point to run each variant at, not a representative one. 'Nothing' for a
-- type that has no first-order value to give (an arrow, a symbol, an
-- unresolved type variable).
canonicalValue :: [ADTDecl] -> RType -> Maybe (GenericValue a)
canonicalValue decls = go (3 :: Int)
  where
    go _ TFloat = Just (VFloat 0.5)
    go _ TInt   = Just (VInt 1)
    go _ TBool  = Just (VBool True)
    go _ TUnit  = Just VUnit
    go _ (ListOf _) = Just (VList EmptyList)
    go d (Tuple a b) = VTuple <$> go d a <*> go d b
    go d (TEither a _) = VEither . Left <$> go d a
    go d (TADT n)
      | d > 0
      , Just decl <- find ((== n) . dataName) decls
      = case [ v | (c, fs) <- constructors decl
                 , Just v <- [VADT c <$> mapM (go (d - 1) . snd) fs] ] of
          (v : _) -> Just v
          []      -> Nothing
    go _ _ = Nothing
