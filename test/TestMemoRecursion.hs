{-# LANGUAGE LambdaCase #-}
-- | The recursion memo, @--memoRecursion@ (docs task
-- recursive-prob-calls-not-shared-across-branches).
--
-- A recursive probability function called with equal arguments from several
-- branches recomputed the whole subtree each time, so an HMM's likelihood cost
-- 2^n calls. The memo is a run-time table, so what it buys is invisible to the
-- rest of the suite, which checks values (and the known-issues harness, which
-- measures compiles): these checks count the executions of the recursive
-- method's body. Everything goes through the real binary (as "TestCLI" does),
-- so the flag's plumbing is under test too, and the Python half lives in
-- @test/memo_recursion_probe.py@.
module TestMemoRecursion (memoRecursionTests) where

import Control.Monad (forM_, unless, when)
import Data.List (isInfixOf)
import System.Directory (getCurrentDirectory)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertBool)

import End2EndTesting (findTorchPython, noTorch)

memoRecursionTests :: TestTree
memoRecursionTests = testGroup "MemoRecursion (recursive-prob-calls-not-shared-across-branches)"
  [ testCase "the HMM repro costs at most 2n+1 calls, with the forward recursion's answer" $ probeCheck "hmm"
  , testCase "canFinish at k = 50 costs at most the reachable (n, k) pairs and matches a hand DP" $ probeCheck "canfinish"
  , testCase "the rung-2 noisy channel at word length 20 matches the alignment DP" $ probeCheck "corrupt"
  , testCase "several entries into one cycle key their pass-through rate apart (floats and tensors)" $ probeCheck "walk"
  , testCase "a neural-transition HMM has the same -log p and gradient with the memo" $ probeCheck "neural"
  , testCase "the batched backend runs the same programs with the memo" $ probeCheck "batched"
  , testCase "a program without recursion compiles byte-identically with the flag" $
      withSystemTempDirectory "nest-memo" $ \dir -> do
        let prog = "f x = x + Normal\nmain = f 1.0 * 2.0\n"
        a <- compileTo dir "plain" prog [] "python"
        b <- compileTo dir "flagged" prog ["--memoRecursion"] "python"
        assertBool "the emitted modules differ" (a == b)
  , testCase "the flag is ignored, with a warning, under topK and on Julia" $
      withSystemTempDirectory "nest-memo" $ \dir -> do
        let src = dir </> "walk.ppl"
        writeFile src walk
        forM_ [ (["--memoRecursion", "-k", "0.01"], "python", "--topKCutoff")
              , (["--memoRecursion"], "julia", "Julia backend") ] $ \(flags, lang, why) -> do
          let out = dir </> ("out." ++ lang)
          (code, _, err) <- readProcessWithExitCode "haskell-dppl-exe"
            (["-i", src] ++ flags ++ ["compile", "-o", out, "-l", lang]) ""
          unless (code == ExitSuccess) $ assertFailure ("compile failed:\n" ++ err)
          assertBool ("no warning naming " ++ why ++ ":\n" ++ err)
            ("--memoRecursion is ignored" `isInfixOf` err && why `isInfixOf` err)
          emittedCode <- readFile out
          when ("nest_memo" `isInfixOf` emittedCode) $ assertFailure ("the memo was emitted anyway (" ++ lang ++ ")")
  ]

-- | Compile the check's programs without and with the flag (and, for the
-- batched check, with @--batched@ too) and run that check of the probe.
probeCheck :: String -> IO ()
probeCheck check = findTorchPython >>= \case
  Nothing -> noTorch ("MemoRecursion: " ++ check) >>= mapM_ assertFailure
  Just py -> withSystemTempDirectory "nest-memo" $ \dir -> do
    forM_ (programsFor check) $ \(name, src) -> do
      _ <- compileTo dir name src [] "python"
      _ <- compileTo dir (name ++ "_memo") src ["--memoRecursion"] "python"
      when (check == "batched") $
        () <$ compileTo dir (name ++ "_memo_b") src ["--memoRecursion", "--batched"] "python"
    cwd <- getCurrentDirectory
    (code, out, err) <- readProcessWithExitCode py ["-W", "ignore", "test/memo_recursion_probe.py", cwd, dir, check] ""
    case code of
      ExitSuccess -> return ()
      ExitFailure _ -> assertFailure (out ++ err)

-- | Write a program to @dir/name.ppl@ and compile it to @dir/name.py@ (or
-- @.jl@); the emitted text.
compileTo :: FilePath -> String -> String -> [String] -> String -> IO String
compileTo dir name src flags lang = do
  let inp = dir </> (name ++ ".ppl")
      out = dir </> (name ++ if lang == "julia" then ".jl" else ".py")
  writeFile inp src
  (code, _, err) <- readProcessWithExitCode "haskell-dppl-exe"
    (["-i", inp] ++ flags ++ ["compile", "-o", out, "-l", lang]) ""
  case code of
    ExitSuccess -> readFile out
    ExitFailure _ -> assertFailure ("compile of " ++ name ++ " " ++ unwords flags ++ " failed:\n" ++ err) >> return ""

programsFor :: String -> [(String, String)]
programsFor = \case
  "hmm"       -> [("hmm", hmm)]
  "canfinish" -> [("canfinish", canFinish)]
  "corrupt"   -> [("corrupt", corrupt)]
  "walk"      -> [("walk", walk), ("walkp", walkP)]
  "neural"    -> [("nhmm", neuralHmm)]
  "batched"   -> [("hmm", hmm), ("canfinish", canFinish), ("walk", walk)]
  other       -> error ("memo_recursion_probe: no programs for " ++ other)

-- | The ticket's repro: a two-state HMM whose state the query does not fix.
hmm :: String
hmm = unlines
  [ "emit s = if s == 0 then Normal else Normal + 2.0"
  , "gen s = if Uniform < 0.1 then [] else if s == 0 then (if Uniform < 0.7 then (emit 0) : gen 0 else (emit 1) : gen 1) else (if Uniform < 0.4 then (emit 0) : gen 0 else (emit 1) : gen 1)"
  , "main = gen 0" ]

-- | The lookahead's surrogate future (docs task exp-llm-lookahead-constraints).
canFinish :: String
canFinish = unlines
  [ "canFinish pEnd pOpen pClose n k ="
  , "  if n < 0 then False"
  , "  else if k == 0 then n == 0"
  , "  else if Uniform < pEnd then n == 0"
  , "  else if Uniform < pOpen then canFinish pEnd pOpen pClose (n + 1) (k - 1)"
  , "  else if Uniform < pClose then canFinish pEnd pOpen pClose (n - 1) (k - 1)"
  , "  else canFinish pEnd pOpen pClose n (k - 1)"
  , ""
  , "main pEnd pOpen pClose n k = canFinish pEnd pOpen pClose n k" ]

-- | The rung-2 channel of docs task exp-llm-noisy-channel-decoding
-- (substitution, deletion, insertion), over a four-letter alphabet.
corrupt :: String
corrupt = unlines
  [ "randChar = if Uniform < 0.25 then 0 else (if Uniform < 0.3333333333333333 then 1 else (if Uniform < 0.5 then 2 else 3))"
  , ""
  , "nbr c = if c == 0 then (if Uniform < 0.5 then 1 else 2) else (if c == 1 then (if Uniform < 0.5 then 0 else 2) else (if c == 2 then (if Uniform < 0.5 then 1 else 3) else (if Uniform < 0.5 then 2 else 0)))"
  , ""
  , "emit pSub c = if Uniform < pSub then nbr c else c"
  , ""
  , "ins pIns xs = if Uniform < pIns then randChar : xs else xs"
  , ""
  , "corrupt pSub pDel pIns cs ="
  , "  if not (isNull cs)"
  , "  then (if Uniform < pDel then ins pIns (corrupt pSub pDel pIns (tail cs))"
  , "        else (emit pSub (head cs)) : (ins pIns (corrupt pSub pDel pIns (tail cs))))"
  , "  else []"
  , ""
  , "main cs pSub pDel pIns = corrupt pSub pDel pIns cs" ]

-- | Two entries into one cycle with different pass-through rates: a key
-- without @p@ answered 0.147 instead of 0.1215.
walk :: String
walk = unlines
  [ "walk p = if Uniform < p then [] else 1.0 : walk p"
  , ""
  , "main = if Uniform < 0.5 then walk 0.3 else walk 0.6" ]

-- | 'walk' with the rates as arguments, so the probe can pass tensors.
walkP :: String
walkP = unlines
  [ "walk p = if Uniform < p then [] else 1.0 : walk p"
  , ""
  , "main p q = if Uniform < 0.5 then walk p else walk q" ]

-- | An HMM whose transitions are networks of a fixed input.
neuralHmm :: String
neuralHmm = unlines
  [ "neural t0 :: (Symbol -> Int) of [0, 1]"
  , "neural t1 :: (Symbol -> Int) of [0, 1]"
  , ""
  , "emit s = if s == 0 then Normal else Normal + 2.0"
  , ""
  , "step x s = if s == 0 then t0 x else t1 x"
  , ""
  , "gen x s = if Uniform < 0.1 then [] else (if step x s == 0 then (emit 0) : gen x 0 else (emit 1) : gen x 1)"
  , ""
  , "main x = gen x 0" ]
