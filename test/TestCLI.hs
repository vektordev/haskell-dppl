-- | The @nest@ executable's command line, driven as a subprocess.
--
-- Everything else in the suite calls the library ('SPLL.Prelude.compile') with
-- a hand-built 'CompilerConfig', so it cannot see whether a CLI flag actually
-- reaches that config: @app/Main.hs@ built one with a hard-coded field until
-- task materialization-budget-cli-flag. This group runs the real binary
-- (@haskell-dppl-exe@, put on PATH by the test-suite's @build-tools@ entry).
module TestCLI (cliTests) where

import System.Directory (getFileSize, doesFileExist)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

cliTests :: TestTree
cliTests = testGroup "CLI"
  [ testGroup "--materializationBudget (task materialization-budget-cli-flag)"
      [ testCase "default budget does not enumerate the 21845-value scene densely" $
          withCompile [] $ \code _ size ->
            -- Today this is a refusal (the plan traversal has no tuple case,
            -- known issue planOverBudgetOfTupleRefused). Once task
            -- plan-path-coverage-for-over-budget-bodies lands it compiles on
            -- the plan path instead, to a module of tens of KB. Either way it
            -- must not be the multi-MB dense module.
            case (code, size) of
              (ExitFailure _, _) -> return ()
              (ExitSuccess, Just n) ->
                assertBool ("default compile emitted a dense-sized module (" ++ show n ++ " bytes)") (n < denseThreshold)
              (ExitSuccess, Nothing) -> assertFailure "compile succeeded but wrote no output file"
      , testCase "a budget above the domain size opts in to dense enumeration" $
          withCompile ["--materializationBudget", "30000"] $ \code err size ->
            case (code, size) of
              (ExitSuccess, Just n) ->
                assertBool ("expected the dense module (> " ++ show denseThreshold ++ " bytes), got " ++ show n) (n >= denseThreshold)
              (ExitSuccess, Nothing) -> assertFailure "compile succeeded but wrote no output file"
              (ExitFailure _, _) -> assertFailure ("compile with a raised budget failed:\n" ++ err)
      ]
  ]

-- | The dense module for this program is ~6MB; the plan path's is tens of KB.
denseThreshold :: Integer
denseThreshold = 1000000

-- | Compile 'overBudgetTuple' to Python with the given extra global flags and
-- hand the exit code, stderr and emitted file size to the continuation.
withCompile :: [String] -> (ExitCode -> String -> Maybe Integer -> IO ()) -> IO ()
withCompile flags k = withSystemTempDirectory "nest-cli" $ \dir -> do
  let src = dir </> "prog.ppl"
      out = dir </> "prog.py"
  writeFile src overBudgetTuple
  (code, _, err) <- readProcessWithExitCode "haskell-dppl-exe"
    (["-i", src] ++ flags ++ ["compile", "-o", out, "-l", "python"]) ""
  exists <- doesFileExist out
  size <- if exists then Just <$> getFileSize out else return Nothing
  k code err size

-- | The shift-2 repro of plan-path-coverage-for-over-budget-bodies: an @of@
-- enumeration of 21845 scene values (over the default budget of 10000) whose
-- body builds a tuple. Kept inline rather than read from
-- @test/cases/known-issues/@, which that task will move it out of.
overBudgetTuple :: String
overBudgetTuple = unlines
  [ "data Color = Red | Green | Blue"
  , "data Object = NoObj | Obj color::Color"
  , "data Scene = Empty | SCons obj::Object, rest::Scene depth 7"
  , "neural readScene :: (Symbol -> Scene) of 7x.{Empty | SCons {NoObj | Obj {Red|Green|Blue}} x}"
  , "numRed s = if isEmpty s then 0.0 else (if isObj (obj s) then (if isRed (color (obj s)) then 1.0 else 0.0) else 0.0) + numRed (rest s)"
  , "main sym = draw scene = readScene sym in (numRed scene, numRed scene)"
  ]
