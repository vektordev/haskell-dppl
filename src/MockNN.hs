module MockNN where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.AutoNeural
import SPLL.Typing.RType

import System.Random
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)


evaluateMockNN :: PartitionPlan -> IRValue -> IRValue
evaluateMockNN part (VTuple a b) | a == VInt 0 = randomMockNN part b
evaluateMockNN part (VTuple a b) | a == VInt 1 = spikingMockNN part b

randomMockNN :: PartitionPlan -> IRValue -> IRValue
randomMockNN part@(Discretes _ _) (VInt seed) = constructVList (map VFloat normalized)
  where 
    randGen = mkStdGen seed
    planSize = getSize part
    uniformRands :: [Double]
    uniformRands = randoms randGen
    firstRands = take planSize uniformRands
    sumRands = sum firstRands
    normalized = map (/ sumRands) firstRands

spikingMockNN :: PartitionPlan -> IRValue -> IRValue
spikingMockNN (Discretes TInt tgs) (VTuple v@(VInt val) (VInt seed)) = do
  let idx = case tgs of
              EnumRange (VInt low, VInt high) -> if val <= high && val >= low then val - low else error "Spinking element cannot be produced by NN"
              EnumList eLst -> fromMaybe (error "Spinking element cannot be produced by NN") (elemIndex v (map valueToIR eLst))
  let size = case tgs of
              EnumRange (VInt low, VInt high) -> high - low + 1
              EnumList eLst -> length eLst
  let g = mkStdGen val
  -- The coice of 0.1 is completely arbitrary. The algorithm used here is not good, but sufficient for now.
  -- Problem: The maximum value of the noise does not scale with the amount of possible values.
  -- The more values possible, the less prominent the spike will be
  let noise = take size (randomRs (0, 0.1) g) :: [Double]   
  let sumNoise = sum noise
  let spike = [if i == idx then 1 else 0 | i <- [0..size - 1]]
  constructVList (map (\(n, s) -> VFloat ((n + s) / (1 + sumNoise))) (zip noise spike)) -- Noise + spike normalized

symbolEnvName :: String
symbolEnvName = "sym"
-- The interpreter does not inherently know how to handle neural networs.
-- We create entries in the environment so that they look like functions.
-- We declare here which entry in the enviroment the symbol is set to
-- so we can read them when jumping to the NN
neuralRTypeToEnv :: NeuralDecl -> (String, IRExpr)
neuralRTypeToEnv (name, _, _) = (name, IRLambda symbolEnvName (IRVar (name ++ "_mock")))