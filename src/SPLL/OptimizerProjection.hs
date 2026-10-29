-- | The one place a 'CompilerConfig' is projected onto the IR optimizer's own
-- 'OptimizerConfig'.
module SPLL.OptimizerProjection (optimizerConfig) where

import SPLL.CompilerConfig (CompilerConfig(..))
import SPLL.IROptimizer (OptimizerConfig(..))

-- | The slice of the configuration the IR optimizer reads.
optimizerConfig :: CompilerConfig -> OptimizerConfig
optimizerConfig c = OptimizerConfig
  { optLevel = optimizerLevel c
  , optPruneAnyChecks = pruneAnyChecks c
  , optVerbose = verbose c
  , optShowStats = optStats c }
