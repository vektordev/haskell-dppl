module MockNN where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.AutoNeural
import SPLL.Typing.RType

import System.Random

randomNN :: IRValue
randomNN = VInt 0

evaluateMockNN :: PartitionPlan -> IRValue -> IRValue
evaluateMockNN part (VTuple a b) | a == randomNN = randomMockNN part b

randomMockNN :: PartitionPlan -> IRValue -> IRValue
randomMockNN part (VInt seed) = constructVList (map VFloat normalized)
  where 
    randGen = mkStdGen seed
    planSize = getSize part
    uniformRands :: [Double]
    uniformRands = randoms randGen
    firstRands = take planSize uniformRands
    sumRands = sum firstRands
    normalized = map (/ sumRands) firstRands

symbolEnvName :: String
symbolEnvName = "sym"
-- The interpreter does not inherently know how to handle neural networs.
-- We create entries in the environment so that they look like functions.
-- We declare here which entry in the enviroment the symbol is set to
-- so we can read them when jumping to the NN
neuralRTypeToEnv :: NeuralDecl -> (String, IRExpr)
neuralRTypeToEnv (name, _, _) = (name, IRLambda symbolEnvName (IRVar (name ++ "_mock")))