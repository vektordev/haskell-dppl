module MockNN
  ( evaluateMockNN
  , evaluateMockNNFor
  , shapedMockLogits
  , planAwareMockLogits
  , MockSlot (..)
  , planAwareMockSlots
  , planHasTensor
  , flattenMockInput
  , mockInputFor
  , mockNeuralOracle
  , programMockOracle
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.AutoNeural
import SPLL.Typing.RType
import SPLL.IR.Neural (NeuralOracle, NeuralPrimitive(..), neuralOracle)

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
evaluateMockNNFor inputTy plan v
  | planHasTensor plan = constructVList (map VFloat (planAwareMockLogits inputTy plan v))
  | otherwise = constructVList (map VFloat (shapedMockLogits inputTy (getSize plan) v))

-- | Does a plan hold a tensor anywhere? A shaped network whose output does is
-- mocked plan-aware ('planAwareMockLogits') rather than by the projection.
planHasTensor :: PartitionPlan -> Bool
planHasTensor plan = case plan of
  TensorPlan _ _ -> True
  TuplePlan a b  -> planHasTensor a || planHasTensor b
  EitherPlan a b -> planHasTensor a || planHasTensor b
  ADTPlan _ cs   -> any (any planHasTensor . snd) cs
  _              -> False

-- | Where one logit of the plan-aware mock comes from: an input slot (by flat
-- 'SPLL.AutoNeural.inputSlots' position; @0.0@ past the input's end) or a
-- constant.
data MockSlot = FromInput Int | MockConst Double
  deriving (Show, Eq)

-- | The plan-aware mock's logits for a plan, as a recipe over the input
-- (decision D-mock (a) of task tensor-gaussian-heads-rd-diffusion). Walking
-- the plan in layout order, the @k@-th Gaussian leaf (a tensor element
-- included) reads its mu from input slot @k@ and has sigma 'mockSigma'; every
-- discrete region is uniform (each Either flag 0.5, each enumeration and
-- constructor flag set @1/n@). So @(Tensor[d] Float, Float) -> Tensor[d] Float@
-- is @N(x, s^2 I)@, a random walk whose trajectory density has a closed form,
-- and a @Float -> Tensor[d] Float@ read at @0.0@ is @N(0, s^2 I)@.
--
-- The projection mock ('shapedMockLogits') stays for every plan without a
-- tensor: the scalar-head pins of the shaped-input slice are written against
-- it, and it reads (mu, sigma) off a @(Float, Float)@ input, which this one
-- does not.
planAwareMockSlots :: PartitionPlan -> [MockSlot]
planAwareMockSlots = fst . go 0
  where
    go k plan = case plan of
      Continuous -> ([FromInput k, MockConst mockSigma], k + 1)
      TensorPlan sh p -> goMany k (replicate (shapeNumel sh) p)
      TuplePlan a b -> goMany k [a, b]
      EitherPlan a b -> let (s, k') = goMany k [a, b] in (MockConst 0.5 : s, k')
      Discretes _ _ -> let n = getSize plan in (replicate n (MockConst (1 / fromIntegral n)), k)
      ADTPlan _ cs ->
        let nf = adtFlagSlots cs
            (s, k') = goMany k (concatMap snd cs)
        in (replicate nf (MockConst (1 / fromIntegral nf)) ++ s, k')
    goMany k [] = ([], k)
    goMany k (p : ps) = let (s, k1) = go k p
                            (rest, k2) = goMany k1 ps
                        in (s ++ rest, k2)

-- | The plan-aware mock's sigma, @1/sqrt(2 pi)@: a Gaussian element's density
-- at its mean is then exactly 1, so a trajectory's density stays of order 1 in
-- any dimension, where sigma 1 gives @(2 pi)^(-d T / 2)@ -- below the corpus's
-- absolute tolerance already at @d = 4@, @T = 3@. A deviation @delta@ costs a
-- factor @exp(-pi delta^2)@.
mockSigma :: Double
mockSigma = 1 / sqrt (2 * pi)

-- | 'planAwareMockSlots' evaluated on an input value.
planAwareMockLogits :: RType -> PartitionPlan -> IRValue -> [Double]
planAwareMockLogits inputTy plan v = map pick (planAwareMockSlots plan)
  where
    flat = flattenMockInput inputTy v
    pick (FromInput i) = if i < length flat then flat !! i else 0.0
    pick (MockConst c) = c

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
randomMockNN (TensorPlan sh p) = do
  elems <- mapM (const (randomMockNN p)) [1 .. shapeNumel sh]
  return (constructVList (concatMap mockLogits elems))
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
spikingMockNN (TensorPlan sh p) (VTensor sh' xs) | sh == sh' = do
  elems <- mapM (spikingMockNN p) xs
  return (constructVList (concatMap mockLogits elems))
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

-- | The interpreter's neural oracle for a program's declarations
-- ("SPLL.IR.Neural"): each network is the mock 'evaluateMockNNFor' picks for
-- its input type, over the partition plan of its target type (the
-- declaration's @of@ clause, else the registry's entry for the type, else the
-- derived plan).
--
-- A declaration that is not @input -> target@ errors when its network is
-- called, not when the oracle is built; validation rejects it before here.
mockNeuralOracle :: [ADTDecl] -> [(RType, MultiValue)] -> [NeuralDecl] -> NeuralOracle
mockNeuralOracle adtDecls registry decls = neuralOracle (map entry decls)
  where
    entry (name, rt, tag) = (name, NeuralPrimitive
      { neuralSignature = neuralIRSignature rt
      , neuralEval = evaluateMockNNFor (inputTy name rt) (plan name rt tag) })
    plan name rt tag =
      let target = fromMaybe (malformed name rt) (neuralValueType rt)
      in makePartitionPlan adtDecls target (resolvePartitionAnnotation registry target tag)
    inputTy name rt = fromMaybe (malformed name rt) (neuralInputType rt)
    malformed name rt = error ("Neural network '" ++ name ++ "' is declared as " ++ show rt
                               ++ "; a read-logits declaration must have type input -> <output type>")

-- | 'mockNeuralOracle' over a program's own declarations and registry.
programMockOracle :: Program -> NeuralOracle
programMockOracle p = mockNeuralOracle (adts p) (writeLogitsDecls p) (neurals p)
