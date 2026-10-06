module MockNN
  ( evaluateMockNN
  , evaluateMockNNFor
  , shapedMockLogits
  , flattenMockInput
  , mockInputFor
  , symbolEnvName
  , neuralRTypeToEnv
  ) where

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
import Data.Foldable (Foldable(toList))
import Utils

-- Expected Syntax:
-- Random Mock NN:
--    (0, seed)
-- Spinking Mock NN:
--    (1, (spikeAt, seed))
-- Literal Mock NN (the given vector is returned verbatim, no noise):
--    (2, [logit0, logit1, ...])
evaluateMockNN :: PartitionPlan -> IRValue -> IRValue
--evaluateMockNN part val | trace ("evalMockNN: " ++ show part ++ " Value: " ++ show val) False = undefined
evaluateMockNN part (VTuple a (VInt seed)) | a == VInt 0 = evalRand (randomMockNN part) (mkStdGen seed)
evaluateMockNN part (VTuple a (VTuple b (VInt seed))) | a == VInt 1 = evalRand (spikingMockNN part b) (mkStdGen seed)
evaluateMockNN part (VTuple a lst@(VList vals)) | a == VInt 2 =
  if length (toList vals) == getSize part
    then lst
    else error $ "Literal mock NN vector has length " ++ show (length (toList vals))
              ++ ", but the partition plan needs " ++ show (getSize part)
evaluateMockNN _ v = error $ "Mock NN parameter " ++ show v ++ " is not one of the three\n"
                          ++ "supported forms: (0, seed) random, (1, (spikeAt, seed)) spiking,\n"
                          ++ "or (2, [logit0, ...]) literal."

-- | The mock network for a declaration whose input has type @inputTy@ (task
-- tensor-type-shaped-neural-inputs).
--
-- A @Symbol@ input is an opaque handle, so the handle itself carries the mock's
-- mode: the envelope protocol of 'evaluateMockNN'. Every other input (a @Float@,
-- a @Tensor[s] t@, a tuple of those) is real data the program may have
-- computed, so the mock is a fixed function of it instead -- 'shapedMockLogits'.
evaluateMockNNFor :: RType -> PartitionPlan -> IRValue -> IRValue
evaluateMockNNFor TSymbol plan v = evaluateMockNN plan v
evaluateMockNNFor inputTy plan v =
  constructVList (map VFloat (shapedMockLogits inputTy (getSize plan) v))

-- | The shaped-input mock: the input flattened in its packing order
-- ('SPLL.AutoNeural.inputSlots': element-major, tuple fields left to right,
-- tensor elements row-major), then truncated to the plan's @n@ logits, or padded
-- with @1.0@ when the input is shorter. It is a fixed affine map (a projection
-- plus a constant), so an exact density can be pinned against it: a
-- @Float -> Float@ network reads @x@ as its mean and @1.0@ as its sigma, and a
-- @(Float, Float) -> Float@ one reads @(mu, sigma)@ off its input in layout order.
shapedMockLogits :: RType -> Int -> IRValue -> [Double]
shapedMockLogits inputTy n v = take n (flattenMockInput inputTy v ++ repeat 1.0)

-- | Flatten a shaped input value in 'inputSlots' order. A value of the wrong
-- shape is an error naming the expected type: the mock is the interpreter's only
-- network, so a malformed input here is a program or harness bug.
flattenMockInput :: RType -> IRValue -> [Double]
flattenMockInput ty v = case (ty, v) of
  (Tuple a b, VTuple x y) -> flattenMockInput a x ++ flattenMockInput b y
  (TTensor sh e, VTensor sh' xs)
    | sh == sh' -> concatMap (scalar e) xs
  (_, _) | ty `elem` [TFloat, TInt, TBool] -> scalar ty v
  _ -> mismatch
  where
    scalar TFloat (VFloat x) = [x]
    scalar TInt   (VInt i)   = [fromIntegral i]
    scalar TBool  (VBool b)  = [if b then 1 else 0]
    scalar TSymbol _         = error ("Mock NN: a shaped input of type " ++ prettyRType ty
                                      ++ " holds a Symbol, which the mock cannot read as a number")
    scalar _ _               = mismatch
    mismatch = error ("Mock NN: input " ++ show v ++ " does not have the declared input type "
                      ++ prettyRType ty)

-- | A correctly shaped mock input that makes 'shapedMockLogits' return the given
-- logits: the logits packed in 'inputSlots' order, the rest of the input zero.
-- This is how a test written against a @Symbol@ network's verbatim-logit
-- envelope runs unchanged against the same network retyped to take a tensor.
-- Refused when the input has fewer slots than there are logits, or when a slot a
-- logit lands in is not a @Float@.
mockInputFor :: RType -> [Double] -> IRValue
mockInputFor inputTy logits
  | inputWidth inputTy < length logits =
      error ("Mock NN: an input of type " ++ prettyRType inputTy ++ " has " ++ show (inputWidth inputTy)
             ++ " slots, too few to carry " ++ show (length logits) ++ " logits")
  | otherwise = fst (go inputTy (logits ++ repeat 0))
  where
    go (Tuple a b) xs = let (va, xs1) = go a xs
                            (vb, xs2) = go b xs1
                        in (VTuple va vb, xs2)
    go (TTensor sh TFloat) xs = let (here, rest) = splitAt (shapeNumel sh) xs
                                in (VTensor sh (map VFloat here), rest)
    go TFloat (x : rest) = (VFloat x, rest)
    go t _ = error ("Mock NN: cannot synthesize a mock input slot of type " ++ prettyRType t
                    ++ " (only Float slots can carry logits)")

-- | Every mock-NN result is the flat logit vector its partition plan sizes.
-- Naming the invariant reports a violation here, with the offending value,
-- instead of as a bare pattern-match panic at each unpacking site.
mockLogits :: IRValue -> [IRValue]
mockLogits (VList l) = toList l
mockLogits v = error ("Mock NN produced a non-vector result: " ++ show v)

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
  rightMock <- randomMockNN planR
  let res = VFloat selector : mockLogits leftMock ++ mockLogits rightMock
  return (constructVList res)
randomMockNN (TuplePlan planF planS) = do
  fstMock <- randomMockNN planF
  sndMock <- randomMockNN planS
  let res = mockLogits fstMock ++ mockLogits sndMock
  return (constructVList res)
randomMockNN Continuous = do
  mu <- getRandom
  sigmaRaw <- getRandom
  return $ constructVList [VFloat mu, VFloat (abs sigmaRaw + 0.1)]
randomMockNN (ADTPlan _ constrs) = do
  let cntConstrs = adtFlagSlots constrs
  selectors <- randomList cntConstrs
  let selectorsNorm = map (/ sum selectors) selectors
  mockedFieldLists <- concatMapM (mapM randomMockNN . snd) constrs
  let mockedFields = concatMap mockLogits mockedFieldLists
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
  sMock <- spikingMockNN planS sVal
  return $ constructVList (mockLogits fMock ++ mockLogits sMock)
spikingMockNN (EitherPlan planL planR) (VEither v) = do
  case v of
        Left l -> do
          selector <- getRandomR (0.8, 1.0) :: RandomGen g => Rand g Double
          leftMock <- spikingMockNN planL l
          rightMock <- randomMockNN planR
          let res = VFloat selector : mockLogits leftMock ++ mockLogits rightMock
          return (constructVList res)
        Right r -> do
          selector <- getRandomR (0.0, 0.2) :: RandomGen g => Rand g Double
          leftMock <- randomMockNN planL
          rightMock <- spikingMockNN planR r
          let res = VFloat selector : mockLogits leftMock ++ mockLogits rightMock
          return (constructVList res)
spikingMockNN (ADTPlan _ constrs) (VList lst) = do
  let (constrSelect, fieldSpikes) = case toList lst of
        VInt i : rest -> (i, rest)
        other -> error ("Spiking mock NN for an ADT needs a value list headed by the\n"
                     ++ "constructor index, got: " ++ show other)

  let cntConstrs = length constrs
  -- a lone constructor has no flag slot ('adtFlagSlots'), so nothing to spike
  selectorsLst <- if adtFlagSlots constrs == 0 then return [] else do
    selectors <- randomList cntConstrs
    let spikingSelectors = replaceAt (map (* 0.2) selectors) constrSelect 1.0
    let selectorsNorm = map (/ sum spikingSelectors) spikingSelectors
    return (map VFloat selectorsNorm)

  let constrFactory (cPlans, cIdx) = if cIdx == constrSelect then zipWithM spikingMockNN cPlans fieldSpikes else mapM randomMockNN cPlans
  mockedFieldLists <- concatMapM constrFactory (zip (map snd constrs) [0..(cntConstrs - 1)])
  let mockedFields = concatMap mockLogits mockedFieldLists
  return $ constructVList (selectorsLst ++ mockedFields)
spikingMockNN plan v = error $ "Mock NN cannot spike value " ++ show v
                            ++ " against partition plan " ++ show plan
                            ++ ": the value's shape does not match the plan's."

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