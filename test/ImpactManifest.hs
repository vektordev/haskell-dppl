{-# LANGUAGE BangPatterns #-}
-- | Test impact analysis for the corpus sweeps (docs-repo task
-- emitted-code-test-impact-analysis, method (1) of design test-speedup).
--
-- A corpus check's verdict is a pure function of what it consumes: the
-- artifact the compiler emitted for the program (generated Python or Julia
-- text, or the optimized 'IREnv' an interpreter check walks), the program's
-- @.tst@ rows, the runtime that evaluates the artifact, and the harness code
-- itself. If none of that changed since the check last passed, re-executing
-- it cannot change the verdict. Each check therefore hashes what it consumes
-- into a key, and only executes when that key is not the one recorded for its
-- (check, program) slot in the manifest of passes.
--
-- * The compile is never skipped: the key is computed from the emitted
--   artifact, so the program is always compiled, and a compile that fails has
--   no key and simply runs (and fails). Only execution is skipped.
-- * A skipped check still appears in the tasty tree and passes, labelled
--   @skipped: unchanged since <commit>@; 'flushManifest' prints a summary line
--   per check ("End2End.Python: 412 unchanged, 9 run") so a skip never reads
--   as a fresh pass.
-- * The manifest is per checkout (@.stack-work/nest-impact-manifest@, so each
--   worktree has its own), never committed. It maps a slot to the key of its
--   last pass, so it holds at most one entry per (check, program) and a run
--   filtered with @-p@ leaves every other slot alone.
-- * @NEST_FULL_TESTS=1@ ignores the manifest for lookups, executes every
--   check, and overwrites the slot of every check that passes. A missing or
--   unreadable manifest is an empty one, i.e. a full run.
--
-- What goes into a key is decided per check at its call site (End2EndTesting),
-- from the fingerprints here: 'harnessFingerprint' (the harness sources, the
-- backstop for a change to a check's logic), 'interpreterFingerprint' (M1: the
-- source of every module in the interpreter's import closure),
-- 'pythonFingerprint' and 'juliaFingerprint' (the runtime library file and the
-- language version).
module ImpactManifest
  ( Manifest
  , openManifest
  , flushManifest
  , writeManifest
  , manifestFile
  , fullTestsRequested
  , cachedProperty
  , cachedBatch
  , manifestStats
  , hashKey
  , harnessFingerprint
  , interpreterFingerprint
  , interpreterClosure
  , pythonFingerprint
  , juliaFingerprint
  ) where

import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Control.Concurrent.MVar (MVar, newMVar, modifyMVar, modifyMVar_, readMVar)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM, when, unless)
import Data.Char (isSpace, isUpper)
import Data.List (intercalate, sort)
import Data.Maybe (isJust, mapMaybe)
import System.Directory (createDirectoryIfMissing, doesFileExist, renameFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), takeDirectory)
import System.IO (hPutStrLn, stderr)
import System.Info (compilerVersion)
import Data.Version (showVersion)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck (Property, ioProperty, label, property)
import Test.QuickCheck.Property (callback, Callback(PostTest), CallbackKind(NotCounterexample), ok, expect)

-- | The passes recorded by earlier runs, plus what this run adds to them.
data Manifest = Manifest
  { mFile   :: FilePath
  , mFull   :: Bool                                 -- ^ NEST_FULL_TESTS: never skip
  , mCommit :: String                               -- ^ HEAD of the checkout, for the log
  , mOld    :: Map.Map String (String, String)      -- ^ slot -> (key, commit), as loaded
  , mNew    :: MVar (Map.Map String (String, String))   -- ^ slots passed this run
  , mStats  :: MVar (Map.Map String (Int, Int))     -- ^ check -> (executed, skipped)
  , mHarness, mInterpreter, mPython, mJulia :: IO String  -- ^ fingerprints, each computed once
  }

-- | Where the default manifest lives, relative to the package root (the test
-- binary's working directory under @stack test@).
manifestFile :: FilePath
manifestFile = ".stack-work" </> "nest-impact-manifest"

manifestHeader :: String
manifestHeader = "nest-impact-manifest v1"

fullTestsRequested :: IO Bool
fullTestsRequested = (`elem` [Just "1", Just "true", Just "yes"]) <$> lookupEnv "NEST_FULL_TESTS"

-- | Load a manifest file. Missing or malformed means empty; @full@ disables
-- lookups (every check executes) but passes are still recorded.
openManifest :: FilePath -> Bool -> IO Manifest
openManifest file full = do
  exists <- doesFileExist file
  old <- if not exists then return Map.empty else do
    r <- try (readFile file >>= \s -> evaluate (length s) >> return s) :: IO (Either SomeException String)
    case r of
      Right s | (h : rows) <- lines s, h == manifestHeader
              , Just entries <- mapM parseRow rows -> return (Map.fromList entries)
      _ -> do
        hPutStrLn stderr ("impact analysis: ignoring unreadable manifest " ++ file ++ " (full run)")
        return Map.empty
  commit <- headCommit
  newVar <- newMVar Map.empty
  statsVar <- newMVar Map.empty
  harness <- once' computeHarness
  interp <- once' computeInterpreter
  py <- once' computePython
  jl <- once' computeJulia
  return Manifest { mFile = file, mFull = full, mCommit = commit, mOld = old
                  , mNew = newVar, mStats = statsVar
                  , mHarness = harness, mInterpreter = interp, mPython = py, mJulia = jl }
  where
    parseRow row = case splitTabs row of
      [slot, key, commit] | not (null slot), length key == 64 -> Just (slot, (key, commit))
      _ -> Nothing
    splitTabs s = case break (== '\t') s of
      (a, [])       -> [a]
      (a, _ : rest) -> a : splitTabs rest

headCommit :: IO String
headCommit = do
  r <- try (readProcessWithExitCode "git" ["rev-parse", "--short", "HEAD"] "") :: IO (Either SomeException (ExitCode, String, String))
  return $ case r of
    Right (ExitSuccess, out, _) | not (null (trim out)) -> trim out
    _ -> "unknown"

-- | Write this run's passes back (merged over the loaded slots, this run's
-- winning), then print one summary line per cached check. A no-op when no
-- cached check ran. Call once, after the test tree has finished.
flushManifest :: Manifest -> IO ()
flushManifest m = do
  stats <- readMVar (mStats m)
  unless (Map.null stats) $ do
    writeManifest m
    let line (check, (ran, skipped)) = check ++ ": " ++ show skipped ++ " unchanged, " ++ show ran ++ " run"
        mode = if mFull m then " (NEST_FULL_TESTS: nothing skipped)" else ""
    putStrLn ("Impact analysis" ++ mode ++ " -- " ++ intercalate "; " (map line (Map.toList stats)))

-- | 'flushManifest' without the summary line.
writeManifest :: Manifest -> IO ()
writeManifest m = do
  new <- readMVar (mNew m)
  let merged = Map.union new (mOld m)
      tmp = mFile m ++ ".tmp"
      body = unlines (manifestHeader : [ intercalate "\t" [slot, key, commit] | (slot, (key, commit)) <- Map.toList merged ])
  r <- try (do createDirectoryIfMissing True (takeDirectory (mFile m))
               writeFile tmp body
               renameFile tmp (mFile m)) :: IO (Either SomeException ())
  either (\e -> hPutStrLn stderr ("impact analysis: could not write " ++ mFile m ++ ": " ++ show e)) return r

-- | Per check: (executed, skipped).
manifestStats :: Manifest -> IO (Map.Map String (Int, Int))
manifestStats = readMVar . mStats

slotOf :: String -> String -> String
slotOf check prog = check ++ "/" ++ prog

-- | The commit a slot's current key passed at, if it did.
lookupPass :: Manifest -> String -> String -> String -> Maybe String
lookupPass m check prog key
  | mFull m = Nothing
  | otherwise = case Map.lookup (slotOf check prog) (mOld m) of
      Just (k, commit) | k == key -> Just commit
      _ -> Nothing

recordPass :: Manifest -> String -> String -> String -> IO ()
recordPass m check prog key = update (mNew m) (Map.insert (slotOf check prog) (key, mCommit m))

bump :: Manifest -> String -> Int -> Int -> IO ()
bump m check ran skipped = update (mStats m) (Map.insertWith add check (ran, skipped))
  where add (a, b) (c, d) = let !x = a + c; !y = b + d in (x, y)

-- | Every test thread updates these tables. The new table is evaluated
-- before the lock is released: an 'atomicModifyIORef'' here would install
-- each update as a thunk over the previous one for several threads to force
-- at once, which is the shape that deadlocked the fuzz tier (docs-repo task
-- fuzz-tier-blackhole-deadlock-at-property-start, docs/testing.md).
update :: MVar (Map.Map String v) -> (Map.Map String v -> Map.Map String v) -> IO ()
update var f = modifyMVar_ var (\mp -> evaluate (f mp))

-- | Evaluate a key, treating an exception (a compile that crashes while
-- rendering) like an absent key: the check then executes and reports it.
forceKey :: IO (Maybe String) -> IO (Maybe String)
forceKey mk = do
  r <- try (mk >>= \k -> evaluate (maybe () (\s -> length s `seq` ()) k) >> return k) :: IO (Either SomeException (Maybe String))
  return (either (const Nothing) id r)

-- | One check on one program. @mkKey@ yields 'Nothing' when there is nothing to
-- key on (the compile failed), in which case the check always executes. On a
-- hit the check passes without executing; on a miss it executes, and its key
-- is recorded once it passes.
cachedProperty :: Manifest -> String -> String -> IO (Maybe String) -> Property -> Property
cachedProperty m check prog mkKey prop = ioProperty $ do
  mk <- forceKey mkKey
  case mk of
    Just key | Just commit <- lookupPass m check prog key -> do
      bump m check 0 1
      return (label ("skipped: unchanged since " ++ commit) (property True))
    _ -> do
      bump m check 1 0
      return $ case mk of
        Nothing  -> prop
        Just key -> callback (PostTest NotCounterexample (\_ res ->
                      when (ok res == Just True && expect res) (recordPass m check prog key))) prop

-- | One check over a batch of programs that share a process (the Julia
-- shards). Programs whose key hits are dropped from the batch; the rest run
-- together and are all recorded if the batch passes (a failing batch records
-- none, since the failure cannot be attributed). An all-hit batch never
-- starts the process.
cachedBatch :: Manifest -> String -> [(String, IO (Maybe String), a)] -> ([a] -> Property) -> Property
cachedBatch m check items runBatch = ioProperty $ do
  keyed <- forM items $ \(prog, mkKey, x) -> do
    k <- forceKey mkKey
    return (prog, k, x)
  let hit (prog, Just k, _) = isJust (lookupPass m check prog k)
      hit _ = False
      todo = filter (not . hit) keyed
      skipped = length keyed - length todo
  bump m check (length todo) skipped
  if null todo
    then return (label ("skipped: all " ++ show skipped ++ " unchanged") (property True))
    else return $ callback (PostTest NotCounterexample (\_ res ->
           when (ok res == Just True && expect res)
             (mapM_ (\(prog, k, _) -> maybe (return ()) (recordPass m check prog) k) todo)))
         (runBatch [ x | (_, _, x) <- todo ])

-- | SHA-256 (hex) of the parts, NUL-separated so part boundaries are
-- unambiguous.
hashKey :: [String] -> String
hashKey parts = hex (SHA256.hash (TE.encodeUtf8 (T.pack (intercalate "\0" parts))))

hex :: BS.ByteString -> String
hex = concatMap byte . BS.unpack
  where byte w = [digits !! fromIntegral (w `div` 16), digits !! fromIntegral (w `mod` 16)]
        digits = "0123456789abcdef"

fileHash :: FilePath -> IO String
fileHash path = do
  r <- try (BS.readFile path) :: IO (Either SomeException BS.ByteString)
  return $ either (const ("missing:" ++ path)) (\bs -> path ++ ":" ++ hex (SHA256.hash bs)) r

-- | An action that runs @act@ the first time it is asked, however many
-- threads ask at once (they wait on the lock), and answers the fully
-- evaluated result from then on.
once' :: IO String -> IO (IO String)
once' act = do
  cell <- newMVar Nothing
  return $ modifyMVar cell $ \c -> case c of
    Just v  -> return (c, v)
    Nothing -> do
      v <- act
      _ <- evaluate (length v)
      return (Just v, v)

-- | The harness: the test modules a corpus check's logic lives in. Any edit to
-- them invalidates every cached check -- the backstop for a change to a
-- check's logic that its per-check version constant was not bumped for.
harnessFingerprint :: Manifest -> IO String
harnessFingerprint = mHarness

computeHarness :: IO String
computeHarness = do
  hs <- mapM fileHash [ "test" </> f | f <- ["End2EndTesting.hs", "CorpusSweep.hs", "ImpactManifest.hs", "TestCaseParser.hs", "TestTolerances.hs"] ]
  return (hashKey ("harness" : hs))

-- | Every @src/@ module the interpreter transitively imports (M1 of the task:
-- any change to them invalidates every interpreter-run check), plus
-- @SPLL/Prelude.hs@ itself, which holds the @run*C@ entry points the checks
-- call (but not its own imports: those are the compiler, whose output the
-- key already contains). Computed from the import lines, so a new import is
-- picked up without a hand-kept list going stale.
interpreterClosure :: IO [FilePath]
interpreterClosure = do
  mods <- go [] ["IRInterpreter"]
  return (sort ("src/SPLL/Prelude.hs" : map modPath mods))
  where
    modPath m = "src" </> map (\c -> if c == '.' then '/' else c) m ++ ".hs"
    go seen [] = return seen
    go seen (m : rest)
      | m `elem` seen = go seen rest
      | otherwise = do
          exists <- doesFileExist (modPath m)
          if not exists then go seen rest else do
            src <- readFile (modPath m)
            length src `seq` go (m : seen) (importsOf src ++ rest)
    importsOf src = mapMaybe importOf (lines src)
    importOf l = case words l of
      ("import" : "qualified" : m : _) -> modName m
      ("import" : m : _)               -> modName m
      _ -> Nothing
    modName m = let n = takeWhile (\c -> c /= '(' && not (isSpace c)) m
                in if not (null n) && isUpper (head n) then Just n else Nothing

-- | The interpreter's sources (see 'interpreterClosure'), the snapshot that
-- fixes its library versions, and the GHC version.
interpreterFingerprint :: Manifest -> IO String
interpreterFingerprint = mInterpreter

computeInterpreter :: IO String
computeInterpreter = do
  files <- interpreterClosure
  hs <- mapM fileHash ("stack.yaml" : files)
  return (hashKey ("interpreter" : showVersion compilerVersion : hs))

-- | @pythonLib.py@ and the @python3@ the harness runs.
pythonFingerprint :: Manifest -> IO String
pythonFingerprint = mPython

computePython :: IO String
computePython = do
  lib <- fileHash "pythonLib.py"
  ver <- versionOf "python3" ["-c", "import sys; print(sys.executable, sys.version)"]
  return (hashKey ["python", lib, ver])

-- | @juliaLib.jl@ and the @julia@ the harness runs.
juliaFingerprint :: Manifest -> IO String
juliaFingerprint = mJulia

computeJulia :: IO String
computeJulia = do
  lib <- fileHash "juliaLib.jl"
  ver <- versionOf "julia" ["--version"]
  return (hashKey ["julia", lib, ver])

-- | A tool's version output; an absent tool gets a fixed marker (its checks
-- fail anyway, and are not recorded).
versionOf :: FilePath -> [String] -> IO String
versionOf tool args = do
  r <- try (readProcessWithExitCode tool args "") :: IO (Either SomeException (ExitCode, String, String))
  return $ case r of
    Right (ExitSuccess, out, _) -> trim out
    _ -> "unavailable:" ++ tool

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
