-- | Small compile/query helpers shared between 'Spec.hs' (the main test
-- suite) and 'TestCorpus' (the Corpus group, split into its own test-suite
-- process -- see the module haddock on 'TestCorpus' for why).
module TestSupport
  ( topKConf
  , topKBCConf
  , bcConf
  , irDensity
  , reasonablyClose
  , expectCompiled
  ) where

import Test.QuickCheck
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Prelude (runProb)
import TestTolerances (reasonablyCloseTolerance)

topKConf :: Double -> CompilerConfig
topKConf thresh = defaultCompilerConfig {topKThreshold = Just thresh}

topKBCConf :: Double -> CompilerConfig
topKBCConf thresh = (topKConf thresh) {countBranches = True}

bcConf :: CompilerConfig
bcConf = defaultCompilerConfig {countBranches = True}

irDensity :: CompilerConfig -> Program -> IRValue -> [IRValue] -> IRValue
irDensity conf p s params = either error id $ runProb conf p params s

reasonablyClose :: IRValue -> IRValue -> Property
reasonablyClose (VFloat a) (VFloat b) = counterexample (show a ++ "/=" ++ show b) (property $ abs (a - b) <= reasonablyCloseTolerance)
reasonablyClose a b = a === b

-- | A compile the test asserts must succeed. Failing here is a broken fixture,
-- so surface the compiler's own message instead of a pattern-match panic.
expectCompiled :: Either CompilerError IREnv -> IREnv
expectCompiled (Right env) = env
expectCompiled (Left err)  = error ("test fixture failed to compile: " ++ show err)
