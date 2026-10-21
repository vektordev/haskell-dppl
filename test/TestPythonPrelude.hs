{-# LANGUAGE LambdaCase #-}
-- | The Python runtime libraries under torch (task
-- python-codegen-silent-precision-traps).
--
-- @pythonLib.py@ and @pythonLibBatched.py@ are hand-written Python the emitted
-- code calls into, so the rest of the suite -- which checks values at query
-- points, in plain floats -- says nothing about how they behave when a model is
-- trained through them. Three defects of one signature were each found by an
-- experiment, months apart: emitted source that looks exact, runs without a
-- warning, and answers a number that is silently wrong (a severed gradient, or
-- a constant truncated to float32). This group is the compiler-side check that
-- makes that class visible; the probes themselves live in
-- @test/prelude_numerics_probe.py@.
--
-- Everything but the classification check needs a torch-enabled python
-- ('findTorchPython', same lookup as the @BatchedPython@ group) and is skipped
-- with a visible note without one.
module TestPythonPrelude (pythonPreludeTests) where

import Data.List (intercalate)
import System.Directory (getCurrentDirectory)
import System.Exit (ExitCode(..))
import System.IO (hPutStr, hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

import SPLL.IntermediateRepresentation (CompilerConfig(..), defaultCompilerConfig)
import SPLL.Prelude (compile)
import SPLL.Parser (tryParseProgram)
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import End2EndTesting (findTorchPython, noTorch)

pythonPreludeTests :: TestTree
pythonPreludeTests = testGroup "PythonPrelude (python-codegen-silent-precision-traps)"
  [ testCase "every public pythonLib function is classified" $
      probe "python3" "scalar-coverage"
  , testCase "scalar prelude keeps the autograd graph (value and gradient)" $
      withTorch "scalar autograd" $ \py -> probe py "scalar-autograd"
  , testCase "batched prelude materialises python floats in float64" $
      withTorch "batched dtype" $ \py -> probe py "batched-dtype"
  , testCase "a folded batched tail constant keeps all its digits" $
      withTorch "batched tail constant" batchedTailConstant
  , testCase "a batched ANY list tail matches a longer constant list" $
      withTorch "batched ANY list tail" batchedAnyTailList
  ]

withTorch :: String -> (FilePath -> IO ()) -> IO ()
withTorch what k = findTorchPython >>= \case
  Nothing -> noTorch ("PythonPrelude: " ++ what) >>= mapM_ assertFailure
  Just py -> k py

probe :: FilePath -> String -> IO ()
probe py mode = do
  cwd <- getCurrentDirectory
  (code, out, err) <- readProcessWithExitCode py ["test/prelude_numerics_probe.py", mode, cwd] ""
  case code of
    ExitSuccess -> return ()
    ExitFailure _ -> assertFailure (mode ++ ":\n" ++ out ++ err)

-- | The shape experiment exp-exact-rare-event-verification hit: an answer the
-- compiler folds to one constant, @P(Normal > 3.7) ~ 1.08e-4@, selected by a
-- @torch.where@ between two python floats. With no dtype anchor torch built
-- that select in its global default dtype (float32), truncating the constant
-- that carries the whole answer to ~7 digits while the emitted source showed
-- all 16. Checked against the scalar formula in float64, far inside the ~2.5e-8
-- a float32 round-trip costs.
batchedTailConstant :: FilePath -> IO ()
batchedTailConstant py = do
  p <- either (assertFailure . ("parse: " ++) . show) return (tryParseProgram "" "main = Normal > 3.7")
  env <- either (assertFailure . ("compile: " ++) . show) return (compile defaultCompilerConfig{batched = True} p)
  srcLines <- either (assertFailure . ("batched codegen: " ++) . show) return (generateFunctionsBatched True env)
  cwd <- getCurrentDirectory
  let script = unlines $
        [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++ srcLines ++
        [ "import math, torch"
        , "r = main.integrate(torch.tensor([True, False]))[0]"
        , "want = [1.0, (1.0 + math.erf(3.7 / math.sqrt(2.0))) / 2.0]"
        , "if r.dtype != torch.float64:"
        , "    raise SystemExit('integrate answered ' + str(r.dtype))"
        , "for got, w in zip(r.tolist(), want):"
        , "    if abs(got - w) > 1e-15:"
        , "        raise SystemExit('integrate answered %r, want %r' % (got, w))"
        ]
  (code, out, err) <- withSystemTempFile "batched_tail_constant.py" $ \path h -> do
    hPutStr h script
    hClose h
    readProcessWithExitCode py [path] ""
  case code of
    ExitSuccess -> return ()
    ExitFailure _ -> assertFailure (out ++ err)

-- | head's inverse compares @Cons(sample, ANY)@ against each arm's list, and
-- the batched runtime's list equality used to require equal lengths, so the
-- arm whose constant list was longer than one element lost all its mass
-- (docs-repo tasks batched-head-of-arm-dependent-list-drops-arm and
-- batched-refuses-list-constants-with-data). Exercised here directly rather
-- than through the corpus: @batched-vs-expected@ skips a program the batched
-- fuzz arms certify, and this bug lived in a construct those arms did reach.
-- One ADT-element and one Either-element repro (the two shrunk seeds), each
-- checked against the interpreter's value.
batchedAnyTailList :: FilePath -> IO ()
batchedAnyTailList py = mapM_ check
  [ ( "data Pt = MkPt x::Float, b::Bool\n\
      \main = head (if Uniform > 0.88 then [MkPt 0.05 True, MkPt 6.2 False] else [MkPt 1.0 (Uniform < 0.86)])"
    , [("MkPt(0.05, True)", 0.12), ("MkPt('ANY', True)", 0.8768), ("MkPt(1.0, True)", 0.7568)] )
  , ( "main = head (if Uniform < 0.5 then [left True, right False] else [left (Uniform < 0.5)])"
    , [("Left(True)", 0.75), ("Left(False)", 0.25)] ) ]
  where
    check :: (String, [(String, Double)]) -> IO ()
    check (src, pts) = do
      p <- either (assertFailure . ("parse: " ++) . show) return (tryParseProgram "" src)
      env <- either (assertFailure . ("compile: " ++) . show) return (compile defaultCompilerConfig{batched = True} p)
      srcLines <- either (assertFailure . ("batched codegen: " ++) . show) return (generateFunctionsBatched True env)
      cwd <- getCurrentDirectory
      let script = unlines $
            [ "import sys", "sys.path.insert(0, " ++ show cwd ++ ")" ] ++ srcLines ++
            [ "r = bucketed(main.forward, [" ++ intercalate ", " (map fst pts) ++ "])[0].tolist()"
            , "want = " ++ show (map snd pts)
            , "if any(abs(g - w) > 1e-9 for g, w in zip(r, want)):"
            , "    raise SystemExit('forward answered %r, want %r' % (r, want))"
            ]
      (code, out, err) <- withSystemTempFile "batched_any_tail_list.py" $ \path h -> do
        hPutStr h script
        hClose h
        readProcessWithExitCode py [path] ""
      case code of
        ExitSuccess -> return ()
        ExitFailure _ -> assertFailure (src ++ ":\n" ++ out ++ err)
