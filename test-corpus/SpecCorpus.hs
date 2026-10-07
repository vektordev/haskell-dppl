-- | Entry point for the @haskell-dppl-test-corpus@ test-suite: just the
-- @Corpus@ tasty group (see 'TestCorpus''s module haddock), run as its own
-- OS process/executable rather than as part of @haskell-dppl-test@'s single
-- process. Splitting it out means its full-corpus-times-eight compiled
-- footprint is reclaimed by the OS when this process exits, instead of
-- staying resident (via tasty's own TestTree retention) for whatever else
-- shares its process -- which is what drove a combined @stack test@ to an
-- OOM kill. @stack test@ still runs this test-suite automatically, as a
-- separate process from @haskell-dppl-test@.
module Main (main) where

import Test.Tasty (defaultMain)
import System.Environment (lookupEnv, setEnv)
import Data.Maybe (isNothing)
import Control.Exception (finally)
import TestCorpus (corpusTests)
import CorpusSweep (loadCorpus, timeWholeRun, reportSweeps)

main :: IO ()
main = do
  -- Mirrors Spec.hs's own default: quiet-on-success unless overridden.
  hideSuccesses <- lookupEnv "TASTY_HIDE_SUCCESSES"
  if isNothing hideSuccesses then setEnv "TASTY_HIDE_SUCCESSES" "true" else return ()
  corpus <- loadCorpus
  tree <- corpusTests corpus
  -- The per-sweep cost table (CorpusSweep), printed once the tree has run.
  flip finally (reportSweeps corpus) $ defaultMain (timeWholeRun corpus tree)
