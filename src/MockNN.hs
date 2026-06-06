module MockNN
  ( evaluateMockNN
  , symbolEnvName
  , neuralRTypeToEnv
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.AutoNeural

import System.Random
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Control.Monad.Random
import Data.Functor ((<&>))
import Data.Foldable (Foldable(toList))
import Utils

-- Expected Syntax:
-- Random Mock NN:
--    (0, seed)
-- Spinking Mock NN:
--    (1, (spikeAt, seed))
evaluateMockNN :: PartitionPlan -> IRValue -> IRValue
--evaluateMockNN part val | trace ("evalMockNN: " ++ show part ++ " Value: " ++ show val) False = undefined
evaluateMockNN part (VTuple a (VInt seed)) | a == VInt 0 = evalRand (randomMockNN part) (mkStdGen seed)
evaluateMockNN part (VTuple a (VTuple b (VInt seed))) | a == VInt 1 = evalRand (spikingMockNN part b) (mkStdGen seed)

randomMockNN :: RandomGen g => PartitionPlan -> Rand g IRValue
--randomMockNN part | trace ("randomMockNN: " ++ show part) False = undefined
randomMockNN part@(Discretes _ _) = do
  let planSize = getSize part
  uniformRands <- randomList planSize
  let sumRands = sum uniformRands
  let normalized = map (/ sumRands) uniformRands
  return $ constructVList (map VFloat normalized)
randomMockNN (EitherPlan planL planR) = do
  selector <- getRandom
  leftMock <- randomMockNN planL
  let VList lMockL = leftMock
  rightMock <- randomMockNN planR
  let VList rMockL = rightMock
  let res = VFloat selector : toList lMockL ++ toList rMockL
  return (constructVList res)
randomMockNN (TuplePlan planF planS) = do
  fstMock <- randomMockNN planF
  let VList fMockL = fstMock
  sndMock <- randomMockNN planS
  let VList sMockL = sndMock
  let res = toList fMockL ++ toList sMockL
  return (constructVList res)
randomMockNN Continuous = do
  mu <- getRandom
  sigmaRaw <- getRandom
  return $ constructVList [VFloat mu, VFloat (abs sigmaRaw + 0.1)]
randomMockNN (ADTPlan _ constrs) = do
  let cntConstrs = length constrs
  selectors <- randomList cntConstrs
  let selectorsNorm = map (/ sum selectors) selectors
  mockedFieldLists <- concatMapM (mapM randomMockNN . snd) constrs
  let mockedFields = concatMap (\(VList l) -> toList l) mockedFieldLists
  let res = map VFloat selectorsNorm ++ mockedFields
  return (constructVList res)

spikingMockNN :: RandomGen g => PartitionPlan -> IRValue -> Rand g IRValue
--spikingMockNN part val | trace ("spinkingNN: " ++ show part ++ " Value: " ++ show val) False = undefined
spikingMockNN (Discretes _ tgs) v = do
  let idx = case tgs of
              MultiDiscretes eLst -> fromMaybe (error "Spinking element cannot be produced by NN") (elemIndex v (map valueToIR eLst))
              t -> error $ "Mock NN currently not supports the return type: " ++ show t
  let size = case tgs of
              MultiDiscretes eLst -> length eLst
              t -> error $ "Mock NN currently not supports the return type: " ++ show t
  -- The coice of 0.1 is completely arbitrary. The algorithm used here is not good, but sufficient for now.
  -- Problem: The maximum value of the noise does not scale with the amount of possible values.
  -- The more values possible, the less prominent the spike will be
  noise <- randomList size <&> map (*0.1)
  let sumNoise = sum noise
  let spike = [if i == idx then 1 else 0 | i <- [0..size - 1]]
  return $ constructVList (map (\(n, s) -> VFloat ((n + s) / (1 + sumNoise))) (zip noise spike))  -- Noise + spike normalized
spikingMockNN Continuous (VFloat x) = do
  noise <- getRandom <&> (* 0.05)
  return $ constructVList [VFloat (x + noise), VFloat (0.1 + abs noise)]
spikingMockNN (TuplePlan planF planS) (VTuple fVal sVal) = do
  fMock <- spikingMockNN planF fVal
  let VList fMockL = fMock
  sMock <- spikingMockNN planS sVal
  let VList sMockL = sMock
  return $ constructVList (toList fMockL ++ toList sMockL)
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
spikingMockNN (ADTPlan _ constrs) (VList lst) = do
  let VInt constrSelect:fieldSpikes = toList lst

  let cntConstrs = length constrs
  selectors <- randomList cntConstrs
  let spikingSelectors = replaceAt (map (* 0.2) selectors) constrSelect 1.0
  let selectorsNorm = map (/ sum spikingSelectors) spikingSelectors
  let selectorsLst = map VFloat selectorsNorm

  let constrFactory (cPlans, cIdx) = if cIdx == constrSelect then zipWithM spikingMockNN cPlans fieldSpikes else mapM randomMockNN cPlans
  mockedFieldLists <- concatMapM constrFactory (zip (map snd constrs) [0..(cntConstrs - 1)])
  let mockedFields = concatMap (\(VList l) -> toList l) mockedFieldLists
  return $ constructVList (selectorsLst ++ mockedFields)

randomList :: (RandomGen g, Random a) => Int -> Rand g [a]
randomList 0 = return []
randomList size = do
  x <- getRandom
  xs <- randomList (size - 1)
  return (x:xs)

symbolEnvName :: String
symbolEnvName = "sym"
-- The interpreter does not inherently know how to handle neural networs.
-- We create entries in the environment so that they look like functions.
-- We declare here which entry in the enviroment the symbol is set to
-- so we can read them when jumping to the NN
neuralRTypeToEnv :: NeuralDecl -> (String, IRExpr)
neuralRTypeToEnv (name, _, _) = (name, IRLambda symbolEnvName (IRVar (name ++ "_mock")))