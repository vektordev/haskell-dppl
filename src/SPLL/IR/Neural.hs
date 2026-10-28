-- | The IR's neural primitive (design ir-package-boundary, step B5).
--
-- In the IR a neural network is a named external function from its input value
-- to its logit vector. What that function computes is not the IR's business:
-- the interpreter takes it as a 'NeuralOracle', injected by whoever runs the
-- program, and the IR type checker takes the same oracle's signatures
-- ('oracleSignatures') as externals. The frontend builds the oracle from a
-- program's neural declarations (the mock one is "MockNN"'s
-- 'MockNN.mockNeuralOracle').
--
-- Semantics in the interpreter ("IRInterpreter"): a name bound in the oracle
-- and not bound locally is a neural primitive. Applied to an argument, it
-- evaluates the argument and answers 'neuralEval' of the value. Referenced
-- without an argument (passed as a function value), it is a closure that does
-- the same once applied. The oracle takes precedence over a top-level binding
-- of the same name.
module SPLL.IR.Neural
  ( NeuralPrimitive(..)
  , NeuralOracle
  , neuralOracle
  , noNeurals
  , lookupNeuralPrimitive
  , oracleSignatures
  ) where

import SPLL.IntermediateRepresentation (IRValue)
import SPLL.IR.Type (IRType)
import Data.Maybe (mapMaybe)
import qualified Data.Map.Strict as Map

-- | One network.
data NeuralPrimitive = NeuralPrimitive
  { neuralSignature :: Maybe IRType
    -- ^ Its IR type, input to logit vector, for the checker. 'Nothing' for a
    -- declaration the IR has no type for; the checker then sees no external
    -- of that name.
  , neuralEval :: IRValue -> IRValue
    -- ^ The network: its input value to its output value.
  }

-- | The networks a program may call, by name.
newtype NeuralOracle = NeuralOracle (Map.Map String NeuralPrimitive)

-- | An oracle over the given networks. A name given twice keeps its first entry.
neuralOracle :: [(String, NeuralPrimitive)] -> NeuralOracle
neuralOracle = NeuralOracle . Map.fromListWith (\_new old -> old)

-- | The oracle of a program without networks.
noNeurals :: NeuralOracle
noNeurals = NeuralOracle Map.empty

lookupNeuralPrimitive :: String -> NeuralOracle -> Maybe NeuralPrimitive
lookupNeuralPrimitive name (NeuralOracle m) = Map.lookup name m

-- | The externals the networks contribute to 'SPLL.IRTypeCheck.checkIREnvWith'.
oracleSignatures :: NeuralOracle -> [(String, IRType)]
oracleSignatures (NeuralOracle m) =
  mapMaybe (\(n, p) -> (,) n <$> neuralSignature p) (Map.toList m)
