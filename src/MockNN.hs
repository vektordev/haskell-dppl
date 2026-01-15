module MockNN where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.AutoNeural
import SPLL.Typing.RType

import System.Random
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Control.Monad.Random
import Data.Functor ((<&>))
import Debug.Trace
import Data.Foldable (Foldable(toList))


evaluateMockNN :: PartitionPlan -> IRValue -> IRValue
--evaluateMockNN part val | trace ("evalMockNN: " ++ show part ++ " Value: " ++ show val) False = undefined
evaluateMockNN part (VTuple a (VInt seed)) | a == VInt 0 = evalRand (randomMockNN part) (mkStdGen seed)
evaluateMockNN part (VTuple a (VTuple b (VInt seed))) | a == VInt 1 = evalRand (spikingMockNN part b) (mkStdGen seed)

randomMockNN :: RandomGen g => PartitionPlan -> Rand g IRValue
randomMockNN part@(Discretes _ _) = do
  let planSize = getSize part
  uniformRands <- randomList
  let firstRands = take planSize uniformRands
  let sumRands = sum firstRands
  let normalized = map (/ sumRands) firstRands
  return $ constructVList (map VFloat normalized)
randomMockNN part@(EitherPlan planL planR) = do
  selector <- getRandom
  leftMock <- randomMockNN planL
  let VList lMockL = leftMock
  rightMock <- randomMockNN planR
  let VList rMockL = rightMock
  let res = VFloat selector : toList lMockL ++ toList rMockL
  return (constructVList res)

spikingMockNN :: RandomGen g => PartitionPlan -> IRValue -> Rand g IRValue
--spikingMockNN part val | trace ("spinkingNN: " ++ show part ++ " Value: " ++ show val) False = undefined
spikingMockNN (Discretes TInt tgs) v = do
  let idx = case tgs of
              MultiDiscretes eLst -> fromMaybe (error "Spinking element cannot be produced by NN") (elemIndex v (map valueToIR eLst))
              t -> error $ "Mock NN currently not supports the return type: " ++ show t
  let size = case tgs of
              MultiDiscretes eLst -> length eLst
              t -> error $ "Mock NN currently not supports the return type: " ++ show t
  -- The coice of 0.1 is completely arbitrary. The algorithm used here is not good, but sufficient for now.
  -- Problem: The maximum value of the noise does not scale with the amount of possible values.
  -- The more values possible, the less prominent the spike will be
  randomNumbers <- randomList <&> map (*0.1)
  let noise = take size randomNumbers
  let sumNoise = sum noise
  let spike = [if i == idx then 1 else 0 | i <- [0..size - 1]]
  return $ constructVList (map (\(n, s) -> VFloat ((n + s) / (1 + sumNoise))) (zip noise spike)) -- Noise + spike normalized
spikingMockNN (EitherPlan planL planR) (VEither v) = do
  case v of
        Left l -> do
          selector <- getRandomR (0.8, 1.0) :: RandomGen g => Rand g Double
          leftMock <- spikingMockNN planL l
          let VList lMockL = leftMock
          rightMock <- randomMockNN planR
          let VList rMockL = rightMock
          let res = VFloat selector : toList lMockL ++ toList rMockL
          return (constructVList res)
        Right r -> do
          selector <- getRandomR (0.0, 0.2) :: RandomGen g => Rand g Double
          leftMock <- randomMockNN planL
          let VList lMockL = leftMock
          rightMock <- spikingMockNN planR r
          let VList rMockL = rightMock
          let res = VFloat selector : toList lMockL ++ toList rMockL
          return (constructVList res)

randomList :: (RandomGen g, Random a) => Rand g [a]
randomList = do
  x <- getRandom
  xs <- randomList
  return (x:xs)

symbolEnvName :: String
symbolEnvName = "sym"
-- The interpreter does not inherently know how to handle neural networs.
-- We create entries in the environment so that they look like functions.
-- We declare here which entry in the enviroment the symbol is set to
-- so we can read them when jumping to the NN
neuralRTypeToEnv :: NeuralDecl -> (String, IRExpr)
neuralRTypeToEnv (name, _, _) = (name, IRLambda symbolEnvName (IRVar (name ++ "_mock")))