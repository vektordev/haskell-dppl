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
--  Call to receive a vector.
--  index into vector and interpret as distribution.
--  provide sampling and inference.

--implicit assumption: Neural Decl accepts a "TSymbol"-typed thing.
makeAutoNeural :: NeuralDecl -> [(String, IRExpr)]
makeAutoNeural (name, (TArrow TSymbol target), tag) =
  [(name ++ "_" ++ show (getSize plan) ++ "_gen" , makeGen  plan name),
   (name ++ "_" ++ show (getSize plan) ++ "_prob", makeProb plan name)]
    where plan = makePartitionPlan target tag

data PartitionPlan = TuplePlan PartitionPlan PartitionPlan
                   | EitherPlan PartitionPlan PartitionPlan
                   | Discretes RType Tag
                   | Continuous -- Mu, Sigma

vector :: String
vector = "l_x_neural_out"

makeProb :: PartitionPlan -> String -> IRExpr
makeProb plan nn_name = IRLambda "sample" $ IRLetIn vector (IRVar nn_name) (IRTCons m (IRTCons dim bc))
  where (m, dim, bc) = (makeProbRec plan 0)


--TODO: Add "decorators" here for Dimcounting? Probably don't need branch counting though.
makeProbRec :: PartitionPlan -> Int -> (IRExpr, IRExpr, IRExpr)
makeProbRec (Discretes rty tag) ix = (p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRIndex (IRVar vector) (IRVar "sample")

--FIXME: Use IREvalNN here maybe?
makeGen :: PartitionPlan -> String ->  IRExpr
makeGen plan nn_name = IRLetIn vector (IRVar nn_name) (makeGenRec plan 0)

makeGenRec :: PartitionPlan -> Int -> IRExpr
makeGenRec (TuplePlan a b) ix = IRTCons (makeGenRec a ix) (makeGenRec b (ix + getSize a)) 
makeGenRec (EitherPlan a b) ix = undefined
makeGenRec (Discretes rty tag) ix = lottery (tagToValues tag) ix
makeGenRec Continuous ix = IROp OpPlus
  (IROp OpMult (IRSample IRNormal) (IRIndex (IRVar vector) (IRConst (VInt $ ix + 1))))
  (IRIndex (IRVar vector) (IRConst (VInt ix)))

totalWeight nValues startIx = foldl (\rest ix -> IROp OpPlus rest (vecAt ix)) (IRConst (VInt 0)) [startIx.. startIx + nValues-1]

vecAt :: Int -> IRExpr
vecAt ix = (IRIndex (IRVar vector) (IRConst (VInt ix)))

-- could probably be simplified by memoizing the total weights.
--lottery :: [IRValue] ->
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

makePartitionPlan :: RType -> Tag -> PartitionPlan
makePartitionPlan (Tuple a b) tag = TuplePlan (makePartitionPlan a tag1) (makePartitionPlan b tag2)
    where
      (tag1, tag2) = splitTag tag
--TODO: Add either.
makePartitionPlan ty tag | isDiscrete ty = Discretes ty tag -- TODO: Validate that tag is sane for this.
makePartitionPlan TFloat tag = Continuous -- TODO: sanity check the tag?

--split a tag over tuples into a tuple of tags.
splitTag :: Tag -> (Tag, Tag)
splitTag (EnumRange (v1, v2)) = (EnumRange (fst $ tupleFromValue v1, fst $ tupleFromValue v2), EnumRange (snd $ tupleFromValue v1, snd $ tupleFromValue v2))
-- TODO: Error if set of values is not a cartesian product? Sounds like it'd break under independence assumptions.
splitTag (EnumList values) = (EnumList $ map (fst . tupleFromValue) values, EnumList $ map (snd . tupleFromValue) values)

tagToValues :: Tag -> [IRValue]
tagToValues (EnumList vals) = map valueToIR vals
tagToValues (EnumRange (v1, v2)) = expandRange (valueToIR v1) (valueToIR v2)

tupleFromValue :: Value -> (Value, Value)
tupleFromValue (VTuple a b) = (a,b)
tupelFromValue _non_tuple = error "supplied non-tuple value to tuple-shaped NN type."


test = do
  let irdefs = makeAutoNeural ("readMNist", TArrow TSymbol TInt, EnumRange ((VInt 0), (VInt 9)))
  putStrLn (pPrintIREnv irdefs)


