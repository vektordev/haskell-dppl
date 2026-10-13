-- | The sampling primitives of the two scalar text backends, checked one at a
-- time (task scalar-sampling-primitives-runtime-tests).
--
-- A generate body reaches its runtime through three primitives only: @rand()@
-- ('IRSample' 'IRUniform'), @randn()@ ('IRSample' 'IRNormal') and
-- @categorical_index@ ('BCategoricalIndex'). On scalar Python they live in
-- @pythonLib.py@; on Julia @rand@/@randn@ are @Base@'s and @categorical_index@
-- is @juliaLib.jl@'s. The rest of the suite runs each backend's generate body
-- once per program and checks nothing about the draw, so these checks are what
-- says the primitives still draw from the distribution the interpreter does.
--
-- * @categorical_index@ is checked exactly, against the interpreter, on the
--   boundary fixture of @TestInternals.categoricalIndexTests@: an off-by-one
--   window or a @<@/@<=@ slip at a CDF step changes an answer there, where a
--   statistical check would not notice. Each container the runtime has a
--   separate path for is fed the same cases.
-- * @rand@ and @randn@ are checked statistically on a fixed seed: range, mean
--   and variance within 5 standard errors, and a Kolmogorov-Smirnov distance
--   below its 0.1% critical value.
--
-- One subprocess per backend, shared by that backend's checks; each check
-- names its primitive. The Julia checks are skipped, with a note, when no
-- @julia@ is on the PATH.
module TestSamplingPrimitives (samplingPrimitiveTests) where

import Data.List (intercalate)
import System.Directory (getCurrentDirectory, findExecutable)
import System.Exit (ExitCode(..))
import System.IO (hPutStr, hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Text.Read (readMaybe)
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (testCaseInfo, assertFailure, assertEqual)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import IRInterpreter (generateDet)

-- | One @categorical_index(u, w, start, n)@ call.
data CatCase = CatCase { ccU :: Double, ccW :: [Double], ccStart :: Int, ccN :: Int }

-- | The interpreter's boundary fixture (@TestInternals.categoricalIndexTests@):
-- weights [1, 0, 3, 4] (total 8, so every CDF step is exact in binary) in the
-- window @start = 1, n = 4@ of a six-slot vector whose outer slots are large,
-- every u listed there, the clamp at u = 1, and all-zero weights.
catCases :: [CatCase]
catCases =
  [ CatCase u fixture 1 4 | u <- [0.0, 0.05, 0.124, 0.125, 0.3, 0.49, 0.5, 0.6, 0.99, 0.999, 1.0] ] ++
  [ CatCase u (replicate 6 0) 1 4 | u <- [0.0, 0.3, 1.0] ]
  where fixture = [100, 1, 0, 3, 4, 100]

-- | What the interpreter answers for a case: the reference.
interpreterIndex :: CatCase -> Either String Integer
interpreterIndex (CatCase u w s n) =
  case generateDet [] [] (IREnv [] [] []) [] (IRBuiltin (BCategoricalIndex s n) [IRConst (VFloat u), wl]) of
    Right (VInt k) -> Right (fromIntegral k)
    other -> Left ("the interpreter answered " ++ show other)
  where wl = IRConst (VList (foldr (ListCont . VFloat) EmptyList w))

-- | Draws per statistical check.
drawCount :: Int
drawCount = 100000

-- | Fixed, so a red result reproduces.
seed :: Int
seed = 20261013

samplingPrimitiveTests :: TestTree
samplingPrimitiveTests = testGroup "SamplingPrimitives (scalar-sampling-primitives-runtime-tests)"
  [ backendGroup "Python" (Just "python3") pythonScript ["list", "InferenceList", "cumsum (numpy array)"]
  , backendGroup "Julia" Nothing juliaScript ["Array", "InferenceList"]
  ]

-- | The output of one backend's run: its lines, each a key and its values.
type RunResult = Either String [(String, [String])]

-- | One subprocess per backend, shared through 'withResource'. @Nothing@ for
-- the interpreter means \"julia from the PATH, skipped when absent\".
backendGroup :: String -> Maybe FilePath -> (FilePath -> String) -> [String] -> TestTree
backendGroup name interp script containers =
  withResource (runBackend name interp script) (const (return ())) $ \getRun ->
    testGroup name $
      [ testCaseInfo ("categorical_index (" ++ c ++ ") matches the interpreter at every CDF boundary") $
          withRun getRun $ \out -> checkCategorical c out
      | c <- containers ] ++
      [ testCaseInfo "rand draws uniformly from [0, 1)" $ withRun getRun (checkMoments uniform)
      , testCaseInfo "randn draws from the standard normal" $ withRun getRun (checkMoments normal)
      ]

withRun :: IO (Maybe RunResult) -> ([(String, [String])] -> IO String) -> IO String
withRun getRun k = getRun >>= go
  where
    go Nothing = return "skipped: no julia on the PATH"
    go (Just (Left err)) = assertFailure err >> return ""
    go (Just (Right out)) = k out

runBackend :: String -> Maybe FilePath -> (FilePath -> String) -> IO (Maybe RunResult)
runBackend name interp script = do
  exe <- maybe (findExecutable "julia") (return . Just) interp
  case exe of
    Nothing -> return Nothing
    Just e -> do
      cwd <- getCurrentDirectory
      (code, out, err) <- withSystemTempFile "sampling_primitives" $ \path h -> do
        hPutStr h (script cwd)
        hClose h
        readProcessWithExitCode e [path] ""
      return $ Just $ case code of
        ExitSuccess -> Right [ (k, vs) | l <- lines out, (k:vs) <- [splitOn '\t' l] ]
        ExitFailure _ -> Left (name ++ " sampling-primitive script failed:\n" ++ out ++ err)

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, []) -> [a]
  (a, _:rest) -> a : splitOn c rest

checkCategorical :: String -> [(String, [String])] -> IO String
checkCategorical container out = case lookup ("categorical_index " ++ container) out of
  Nothing -> assertFailure ("no categorical_index result for " ++ container) >> return ""
  Just ["skipped", why] -> return ("skipped: " ++ why)
  Just got -> do
    want <- either assertFailure return (mapM interpreterIndex catCases)
    let describe (cc, w, g) = "u = " ++ show (ccU cc) ++ ", w = " ++ show (ccW cc)
                              ++ ", start = " ++ show (ccStart cc) ++ ", n = " ++ show (ccN cc)
                              ++ ": interpreter " ++ show w ++ ", runtime " ++ g
        bad = [ describe t | t@(_, w, g) <- zip3 catCases want got, readMaybe g /= Just w ]
    assertEqual "number of answers" (length catCases) (length got)
    assertEqual "categorical_index disagreements" [] bad
    return ""

-- | A distribution's reference statistics for the moment check.
data Dist = Dist
  { dName :: String, dMean :: Double, dVar :: Double
  , dVarOfSq :: Double  -- ^ Var((X - mean)^2), for the variance's standard error
  , dRange :: Maybe (Double, Double)  -- ^ closed below, open above
  }

uniform, normal :: Dist
uniform = Dist "rand" 0.5 (1 / 12) (1 / 80 - 1 / 144) (Just (0, 1))
normal = Dist "randn" 0 1 2 Nothing

-- | Mean and variance within 5 standard errors, and the KS distance to the
-- reference CDF (computed by the script) below the 0.1% critical value
-- 1.95 / sqrt n.
checkMoments :: Dist -> [(String, [String])] -> IO String
checkMoments d out = case lookup ("moments " ++ dName d) out of
  Nothing -> assertFailure ("no moments for " ++ dName d) >> return ""
  Just vs -> case mapM readMaybe vs :: Maybe [Double] of
    Just [n, lo, hi, m, v, ks] -> do
      let fails =
            [ "range [" ++ show lo ++ ", " ++ show hi ++ "] leaves [" ++ show a ++ ", " ++ show b ++ ")"
            | Just (a, b) <- [dRange d], lo < a || hi >= b ] ++
            [ "mean " ++ show m ++ ", want " ++ show (dMean d) ++ " +- " ++ show seM
            | abs (m - dMean d) > seM ] ++
            [ "variance " ++ show v ++ ", want " ++ show (dVar d) ++ " +- " ++ show seV
            | abs (v - dVar d) > seV ] ++
            [ "Kolmogorov-Smirnov distance " ++ show ks ++ " exceeds " ++ show ksCrit | ks > ksCrit ]
          seM = 5 * sqrt (dVar d / n)
          seV = 5 * sqrt (dVarOfSq d / n)
          ksCrit = 1.95 / sqrt n
      assertEqual (dName d ++ " (" ++ show (round n :: Int) ++ " draws, seed " ++ show seed ++ ")") [] fails
      return ""
    _ -> assertFailure ("unreadable moments line for " ++ dName d ++ ": " ++ unwords vs) >> return ""

-- Scripts ------------------------------------------------------------------

-- | Lines are tab-separated: a key (@categorical_index <container>@ or
-- @moments <primitive>@), then values.
pythonScript :: FilePath -> String
pythonScript cwd = unlines
  [ "import sys, math, random as _random"
  , "sys.path.insert(0, " ++ show cwd ++ ")"
  , "from pythonLib import *"
  , "cases = [" ++ intercalate ", " [ "(" ++ show u ++ ", " ++ pyList w ++ ", " ++ show s ++ ", " ++ show n ++ ")" | CatCase u w s n <- catCases ] ++ "]"
  , "def out(key, vals): print('\\t'.join([key] + [str(v) for v in vals]))"
  , "def to_inference_list(ws):"
  , "  l = EmptyInferenceList()"
  , "  for x in reversed(ws): l = ConsInferenceList(x, l)"
  , "  return l"
  , "out('categorical_index list', [categorical_index(u, list(w), s, n) for (u, w, s, n) in cases])"
  , "out('categorical_index InferenceList', [categorical_index(u, to_inference_list(w), s, n) for (u, w, s, n) in cases])"
  , "try:"
  , "  import numpy"
  , "  out('categorical_index cumsum (numpy array)', [categorical_index(u, numpy.array(w), s, n) for (u, w, s, n) in cases])"
  , "except ImportError:"
  , "  out('categorical_index cumsum (numpy array)', ['skipped', 'python3 cannot import numpy, so the cumsum path went unchecked'])"
  , "def moments(name, draw, cdf, n):"
  , "  xs = [draw() for _ in range(n)]"
  , "  m = sum(xs) / n"
  , "  v = sum((x - m) ** 2 for x in xs) / (n - 1)"
  , "  d = 0.0"
  , "  for i, x in enumerate(sorted(xs)):"
  , "    f = cdf(x)"
  , "    d = max(d, (i + 1) / n - f, f - i / n)"
  , "  out('moments ' + name, [repr(float(t)) for t in (n, min(xs), max(xs), m, v, d)])"
  , "_random.seed(" ++ show seed ++ ")"
  , "moments('rand', rand, lambda x: x, " ++ show drawCount ++ ")"
  , "moments('randn', randn, lambda x: math.erfc(-x / math.sqrt(2.0)) / 2.0, " ++ show drawCount ++ ")"
  ]
  where pyList w = "[" ++ intercalate ", " (map show w) ++ "]"

-- | @rand@ and @randn@ resolve to @Base@'s, as in emitted code.
juliaScript :: FilePath -> String
juliaScript cwd = unlines
  [ "include(" ++ show (cwd ++ "/juliaLib.jl") ++ ")"
  , "using .JuliaSPPLLib"
  , "using Random"
  , "cases = [" ++ intercalate ", " [ "(" ++ show u ++ ", Float64" ++ jlList w ++ ", " ++ show s ++ ", " ++ show n ++ ")" | CatCase u w s n <- catCases ] ++ "]"
  , "out(key, vals) = println(join(vcat([key], [string(v) for v in vals]), \"\\t\"))"
  , "to_inference_list(ws) = foldr(prepend, ws; init = EmptyInferenceList())"
  , "out(\"categorical_index Array\", [categorical_index(u, w, s, n) for (u, w, s, n) in cases])"
  , "out(\"categorical_index InferenceList\", [categorical_index(u, to_inference_list(w), s, n) for (u, w, s, n) in cases])"
  , "function moments(name, draw, cdf, n)"
  , "    xs = [draw() for _ in 1:n]"
  , "    m = sum(xs) / n"
  , "    v = sum((xs .- m) .^ 2) / (n - 1)"
  , "    d = 0.0"
  , "    for (i, x) in enumerate(sort(xs))"
  , "        f = cdf(x)"
  , "        d = max(d, i / n - f, f - (i - 1) / n)"
  , "    end"
  , "    out(\"moments \" * name, [Float64(t) for t in (n, minimum(xs), maximum(xs), m, v, d)])"
  , "end"
  , "Random.seed!(" ++ show seed ++ ")"
  , "moments(\"rand\", rand, x -> x, " ++ show drawCount ++ ")"
  , "moments(\"randn\", randn, x -> ccall((:erfc, Base.Math.libm), Float64, (Float64,), -x / sqrt(2.0)) / 2.0, " ++ show drawCount ++ ")"
  ]
  where jlList w = "[" ++ intercalate ", " (map show w) ++ "]"
