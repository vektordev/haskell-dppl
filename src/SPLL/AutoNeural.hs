module SPLL.AutoNeural(
  makeAutoNeural
) where

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import PrettyPrint

-- basic strucutre:
--  get the partition plan.
--  Let's call the actual network name_getSize.
--  Call the NN to receive a vector.
--  index into vector and interpret as distribution.
--  provide sampling and inference.

--implicit assumption: Neural Decl accepts a "TSymbol"-typed thing.
makeAutoNeural :: CompilerConfig -> NeuralDecl -> [(String, IRExpr)]
makeAutoNeural conf (name, (TArrow TSymbol target), tag) =
  [(name ++ "_" ++ show (getSize plan) ++ "_gen" , IRLambda symbol $ makeGen  plan name),
   (name ++ "_" ++ show (getSize plan) ++ "_prob", IRLambda symbol $ makeProb conf plan name)]
    where plan = makePartitionPlan target tag

data PartitionPlan = TuplePlan PartitionPlan PartitionPlan
                   | EitherPlan PartitionPlan PartitionPlan
                   | Discretes RType Tag
                   | Continuous -- Mu, Sigma

vector :: String
vector = "l_x_neural_out"

symbol :: String
symbol = "l_x_neural_in"

makeProb :: CompilerConfig -> PartitionPlan -> String -> IRExpr
makeProb conf plan nn_name = IRLambda "sample" $ IRLetIn vector (IREvalNN nn_name (IRVar "l_x_neural_in")) (IRTCons m (IRTCons dim bc))
  where 
    (m, dim, bc) = (makeProbRec plan 0 (IRVar "sample"))
    sndRet = if countBranches conf then IRTCons dim bc else dim

makeProbRec :: PartitionPlan -> Int -> IRExpr -> (IRExpr, IRExpr, IRExpr)
makeProbRec (Discretes rty tag) ix sample = (p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRIndex (IRVar vector) sample
makeProbRec Continuous ix sample = (p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRDensity IRNormal (IROp OpSub
          (IROp OpDiv sample (IRIndex (IRVar vector) (IRConst (VInt $ ix + 1))))
          (IRIndex (IRVar vector) (IRConst (VInt ix))))
--Not entirely sure how to combine elements in the next case. For now:
--  probabilities of the two tuple elements are multiplied.
--  dims should be added.
--  branch counts of both sides should be added.
makeProbRec (TuplePlan a b) ix sample = (IROp OpMult pa pb, IROp OpPlus dima dimb, IROp OpPlus bca bcb)
  where
    (pa, dima, bca) = makeProbRec a ix (IRTFst sample)
    (pb, dimb, bcb) = makeProbRec b (ix + getSize a) (IRTSnd sample)
makeProbRec (EitherPlan a b) ix sample = undefined -- TODO: Waiting for sum types.


makeGen :: PartitionPlan -> String ->  IRExpr
makeGen plan nn_name = IRLetIn vector (IREvalNN nn_name (IRVar "l_x_neural_in")) (makeGenRec plan 0)

makeGenRec :: PartitionPlan -> Int -> IRExpr
makeGenRec (TuplePlan a b) ix = IRTCons (makeGenRec a ix) (makeGenRec b (ix + getSize a)) 
makeGenRec (EitherPlan a b) ix = undefined -- TODO: Waiting for sum types.
makeGenRec (Discretes rty tag) ix = lottery (tagToValues tag) ix
makeGenRec Continuous ix = IROp OpPlus
  (IROp OpMult (IRSample IRNormal) (IRIndex (IRVar vector) (IRConst (VInt $ ix + 1))))
  (IRIndex (IRVar vector) (IRConst (VInt ix)))

totalWeight nValues startIx = foldl (\rest ix -> IROp OpPlus rest (vecAt ix)) (IRConst (VInt 0)) [startIx.. startIx + nValues-1]

vecAt :: Int -> IRExpr
vecAt ix = (IRIndex (IRVar vector) (IRConst (VInt ix)))

-- could probably be simplified by memoizing the total weights, or assuming normalization.
lottery :: [IRValue] -> Int -> IRExpr
lottery [value] _ = IRConst value
lottery values startIx = IRIf
  (IROp OpGreaterThan (IRSample IRUniform) (wtfirst))
  (IRConst (head values))
  (lottery (tail values) (startIx + 1))
    where
      nValues = length values
      wtfirst = IROp OpDiv (vecAt startIx) (totalWeight nValues startIx)

getSize :: PartitionPlan -> Int
getSize (TuplePlan a b) = getSize a + getSize b
getSize (EitherPlan a b) = getSize a + getSize b + 1
getSize (Discretes _ (EnumList vals)) = length vals
getSize (Discretes _ (EnumRange (from, to))) = getSizeRange from to
getSize Continuous = 2

getSizeRange :: Value -> Value -> Int
-- + 1's because we're inclusive on both ends.
getSizeRange (VInt from) (VInt to) = (abs (from - to)) + 1
getSizeRange (VBool x) (VBool y) = (if x == y then 0 else 1) + 1

expandRange :: IRValue -> IRValue -> [IRValue]
expandRange (VInt singular) (VInt singular2) | singular == singular2 = [VInt singular]
expandRange (VInt from) (VInt to) = VInt from : (expandRange (VInt (from+1)) (VInt to))
expandRange (VBool x) (VBool y) = if x == y then [VBool x] else [VBool x, VBool y]
--TODO: Test invariant: expanded range length equal to getSizeRange

isDiscrete :: RType -> Bool
isDiscrete TBool = True
isDiscrete TInt = True
isDiscrete (ListOf ty) = isDiscrete ty
isDiscrete (Tuple ty1 ty2) = isDiscrete ty1 && isDiscrete ty2
isDiscrete other = False

makePartitionPlan :: RType -> Maybe Tag -> PartitionPlan
makePartitionPlan (Tuple a b) tag = TuplePlan (makePartitionPlan a tag1) (makePartitionPlan b tag2)
    where
      (tag1, tag2) = splitTag tag
--TODO: Add either.
makePartitionPlan ty (Just tag) | isDiscrete ty = Discretes ty tag -- TODO: Validate that tag is sane for this.
makePartitionPlan ty (Nothing) | isDiscrete ty = error "no enumeration range supplied for discrete value in AutoNeural."
makePartitionPlan TFloat Nothing = Continuous
makePartitionPlan TFloat a = error ("enum range supplied to continuous value in AutoNeural:" ++ show a)
makePartitionPlan x y = error ("erroneous combination of type and tag in AutoNeural." ++ show x ++ show y)

--split a tag over tuples into a tuple of tags.
splitTag :: Maybe Tag -> (Maybe Tag, Maybe Tag)
splitTag Nothing = (Nothing, Nothing)
splitTag (Just (EnumRange (v1, v2))) = (Just $ EnumRange (fst $ tupleFromValue v1, fst $ tupleFromValue v2), Just $ EnumRange (snd $ tupleFromValue v1, snd $ tupleFromValue v2))
-- TODO: Error if set of values is not a cartesian product? Sounds like it'd break under independence assumptions.
splitTag (Just (EnumList values)) = (Just $ EnumList $ map (fst . tupleFromValue) values, Just $ EnumList $ map (snd . tupleFromValue) values)

tagToValues :: Tag -> [IRValue]
tagToValues (EnumList vals) = map valueToIR vals
tagToValues (EnumRange (v1, v2)) = expandRange (valueToIR v1) (valueToIR v2)

tupleFromValue :: Value -> (Value, Value)
tupleFromValue (VTuple a b) = (a,b)
tupelFromValue _non_tuple = error "supplied non-tuple value to tuple-shaped NN type."

testConf = CompilerConfig {topKThreshold=Nothing, countBranches=False, verbose=2, optimizerLevel=2}

test = do
  let irdefs = makeAutoNeural testConf ("readMNist", TArrow TSymbol TInt, Just $ EnumRange ((VInt 0), (VInt 9)))
  putStrLn (pPrintIREnv irdefs)

test2 = do
  let irdefs = makeAutoNeural testConf ("regressFloat", TArrow TSymbol TFloat, Nothing)
  putStrLn (pPrintIREnv irdefs)

--TODO: Needs MAR semantics for the VAny.
--test3 = do
--  let irdefs = makeAutoNeural ("mixedTuple", TArrow TSymbol (Tuple TFloat TInt), Just $ EnumRange ((VTuple VAny (VInt 3)),(VTuple VAny (VInt 5))))
--  putStrLn (pPrintIREnv irdefs)

test4 = do
  let irdefs = makeAutoNeural testConf ("tuple", TArrow TSymbol (Tuple TInt TInt), Just $ EnumRange ((VTuple (VInt 7) (VInt 3)), (VTuple (VInt 9) (VInt 5))))
  putStrLn (pPrintIREnv irdefs)

test5 = do
  let irdefs = makeAutoNeural testConf ("tuple", TArrow TSymbol (Tuple TInt TInt), Just $ EnumList [(VTuple (VInt 7) (VInt 3)), (VTuple (VInt 9) (VInt 5))])
  putStrLn (pPrintIREnv irdefs)

