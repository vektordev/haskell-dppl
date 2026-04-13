module SPLL.AutoNeural(
  makeAutoNeural
, makeForwardDecl
, makePartitionPlan
, makeEncodeRec
, PartitionPlan (..)
, getSize
, planIndexOf
) where

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.Lang.Lang
import PrettyPrint
import StandardLibrary

import Debug.Trace
import Data.List (find, elemIndex)
import Utils
import Data.Maybe (fromJust)

-- basic strucutre:
--  get the partition plan.
--  Let's call the actual network name_getSize.
--  Call the NN to receive a vector.
--  index into vector and interpret as distribution.
--  provide sampling and inference.

--implicit assumption: Neural Decl accepts a "TSymbol"-typed thing.
makeAutoNeural :: [ADTDecl] -> CompilerConfig -> NeuralDecl -> IRFunGroup
makeAutoNeural adts conf (name, (TArrow TSymbol target), tag) =
  IRFunGroup (name ++ "_auto")
    (Just (IRLambda symbol $ makeGen adts plan name, "Wrapper for the neural network function"))
    (Just (IRLambda symbol $ makeProb adts conf plan name, "Inference function for neural network function"))
    Nothing
    (Just (IRLambda symbol $ makeEncode adts conf plan name, "Encoding function for NN2 input"))
    (show plan)
    where plan = makePartitionPlan adts target tag
makeAutoNeural adts conf (name, rt, _) = error $ "Invalid neural declaration for " ++ name ++ ": Neural networks must be function TSymbol -> a"

--TODO: Output this into the output file somehow.
-- yields a forward declaration of a neural network:
-- includes a string representation of the partition plan, including constraints about outputted logits.
makeForwardDecl :: [ADTDecl] -> NeuralDecl -> String
makeForwardDecl adts (name, (TArrow TSymbol target), tag) = "neural Network " ++ name ++ " :: (" ++ show target ++ ")\n  with layout: " ++ plan_string plan ++ ",\n  dimensionality=" ++ show (getSize plan) ++ ".\n"
  where
    plan = makePartitionPlan adts target tag
    plan_string (TuplePlan first second) = plan_string first ++ " x " ++ plan_string second
    plan_string (EitherPlan left right) = "[1](0..1)" ++ plan_string left ++ " + " ++ plan_string right
    plan_string p@(Discretes ty tag) = "[" ++ show (getSize p) ++ "](softmax'ed)"
    plan_string Continuous = "[1],[1](>0)"


data PartitionPlan = TuplePlan PartitionPlan PartitionPlan -- Logit layout: first, then second.
                   | EitherPlan PartitionPlan PartitionPlan -- Logit layout: flag, then left, then right
                   | Discretes RType MultiValue -- Logit layout: Enumerated values in order of "tagToValues"
                   | ADTPlan String [(String, [PartitionPlan])] -- Logit layout: Flag for each constructor, then each field of each constructor
                   | Continuous -- Logit layout: Mu, Sigma
                   deriving Show

vector :: String
vector = "l_x_neural_out"

symbol :: String
symbol = "l_x_neural_in"

makeProb :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> String -> IRExpr
makeProb adts conf plan nn_name = IRLambda "sample" $ IRLetIn vector (IRApply (IRVar nn_name) (IRVar "l_x_neural_in")) (IRTCons m sndRet)
  where
    (m, dim, bc) = (makeProbRec adts plan 0 (IRVar "sample"))
    sndRet = IRTCons dim bc

-- Takes a Tag from a Discretes type and a sample, and builds code that returns the index of the sample in the tag.
-- step 1: turn the tag into a list of values.
-- step 2: Use IRApply "indexOf" to find the index of the value in the list
indexOf :: MultiValue -> IRExpr -> IRExpr
indexOf (MultiDiscretes vals) sample = invokeStandardFunction stdIndexOf [sample, IRConst (constructVList (map valueToIR vals))]


makeProbRec :: [ADTDecl] -> PartitionPlan -> Int -> IRExpr -> (IRExpr, IRExpr, IRExpr)
makeProbRec adts (Discretes rty tag) ix sample = (noAny sample p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRIndex (IRVar vector) (IROp OpPlus (indexOf tag sample) (IRConst (VInt ix)))
makeProbRec adts Continuous ix sample = (noAny sample p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRDensity IRNormal (IROp OpSub
          (IROp OpDiv sample (IRIndex (IRVar vector) (IRConst (VInt $ ix + 1))))
          (IRIndex (IRVar vector) (IRConst (VInt ix))))
--Not entirely sure how to combine elements in the next case. For now:
--  probabilities of the two tuple elements are multiplied.
--  dims should be added.
--  branch counts of both sides should be added.
makeProbRec adts (TuplePlan a b) ix sample = (noAny sample (IROp OpMult pa pb), noAny0 sample (IROp OpPlus dima dimb), noAny0 sample (IROp OpPlus bca bcb))
  where
    (pa, dima, bca) = makeProbRec adts a ix (IRTFst sample)
    (pb, dimb, bcb) = makeProbRec adts b (ix + getSize a) (IRTSnd sample)
makeProbRec adts (EitherPlan a b) ix sample = (noAny sample
  (IRIf (IRIsLeft sample)
    (IROp OpMult pIsLeft aP)
    (IROp OpMult pIsRight bP)),
  -- Is choosing the bc here correct, or should they be added? 
  noAny0 sample (IRIf (IRIsLeft sample) aDim bDim), noAny0 sample (IRIf (IRIsLeft sample) aBc bBc))
  where
    (aP, aDim, aBc) = makeProbRec adts a (ix + 1) (IRFromLeft sample)
    (bP, bDim, bBc) = makeProbRec adts b (ix + 1 + getSize a) (IRFromRight sample)
    pIsLeft = IRIndex (IRVar vector) (IRConst (VInt ix))
    pIsRight = IROp OpSub (IRConst $ VFloat 1) pIsLeft
makeProbRec adts (ADTPlan adtName plans) ix sample = (noAny sample p, noAny0 sample dim, noAny0 sample bc)
  where
    Just adt = find ((== adtName) . dataName) adts
    constrsInPlan = filter ((`elem` map fst plans) . fst) (constructors adt)
    constrsWithPlan = mapToTup (fromJust . (`lookup` plans) . fst) constrsInPlan
    constrsWithPlanAndIx = mapAppendTup constrsWithPlan constrIx
    constrsWithPlanAndIxAndFlag = mapAppendTup3 constrsWithPlanAndIx flagProbs
    constrIx = scanl (+) (ix + length plans) (map totalSize plans)
    constrGuard constr constrFlag v = IRIf (IRApply (IRVar ("is" ++ fst constr)) sample) (IROp OpMult constrFlag v) (IRConst $ VFloat 0)
    constrProbFields constr cPlan cIx constrFlag = mapTup3 (constrGuard constr constrFlag) (makeProbADTConstr adts cPlan constr cIx sample)
    constrProbsFields = map (uncurry4 constrProbFields) constrsWithPlanAndIxAndFlag
    opPlus3 (a1, b1, c1) (a2, b2, c2) = (IROp OpPlus a1 a2, IROp OpPlus b1 b2, IROp OpPlus c1 c2)
    (p, dim, bc) = foldr opPlus3 (IRConst $ VFloat 0, IRConst $ VFloat 0, IRConst $ VFloat 0) constrProbsFields
    flagIx = [ix .. ix + length plans]
    flagProbs = map (\fIx -> IRIndex (IRVar vector) (IRConst (VInt fIx))) flagIx


makeProbADTConstr :: [ADTDecl] -> [PartitionPlan] -> ADTConstructorDecl -> Int -> IRExpr -> (IRExpr, IRExpr, IRExpr)
makeProbADTConstr adts plans (cName, fields) ix sample = foldr multProbs prob1 fieldsProb
  where
    prob1 = (IRConst (VFloat 1), IRConst (VFloat 0), IRConst (VFloat 0))
    multProbs (p0, d0, bc0) (p1, d1, bc1) = (IROp OpMult p0 p1, IROp OpPlus d0 d1, IROp OpPlus bc0 bc1)
    fieldIx = scanl (+) ix (map getSize plans)
    fieldsProb = map (\(plan, pIx, fName) -> makeProbRec adts plan pIx (IRApply (IRVar fName) sample)) (zip3 plans fieldIx (map fst fields))


makeGen :: [ADTDecl] -> PartitionPlan -> String ->  IRExpr
makeGen adts plan nn_name = IRLetIn vector (IRApply (IRVar nn_name) (IRVar "l_x_neural_in")) (makeGenRec adts plan 0)

makeGenRec :: [ADTDecl] -> PartitionPlan -> Int -> IRExpr
makeGenRec adts (TuplePlan a b) ix = IRTCons (makeGenRec adts a ix) (makeGenRec adts b (ix + getSize a))
makeGenRec adts (EitherPlan a b) ix = IRIf
  (IROp OpLessThan (IRSample IRUniform) (IRIndex (IRVar vector) (IRConst (VInt ix))))
    (IRLeft $ makeGenRec adts a (ix + 1))
    (IRRight $ makeGenRec adts b (ix + 1 + getSize a))
makeGenRec adts (Discretes rty (MultiDiscretes vals)) ix = lottery (map valueToIR vals) ix
makeGenRec adts Continuous ix = IROp OpPlus
  (IROp OpMult (IRSample IRNormal) (IRIndex (IRVar vector) (IRConst (VInt $ ix + 1))))
  (IRIndex (IRVar vector) (IRConst (VInt ix)))
makeGenRec adts (ADTPlan adtName plans) ix = constructorLottery adts plans ix (ix + length (constructors adt))
  where
    Just adt = find ((== adtName) . dataName) adts

makeGenADTConstr :: [ADTDecl] -> [PartitionPlan] -> String -> Int -> IRExpr
makeGenADTConstr adts plans name ix = foldl IRApply (IRVar name) gens
  where
    ixForField = scanl (+) 0 (map (getSize) plans) -- Comulative sums over number of fields
    gens = map (uncurry (makeGenRec adts)) (zip plans ixForField)

totalWeight :: Int -> Int -> IRExpr
totalWeight nValues startIx = foldl (\rest ix -> IROp OpPlus rest (vecAt ix)) (IRConst (VInt 0)) [startIx.. startIx + nValues-1]

totalSize :: (String, [PartitionPlan]) -> Int
totalSize ps = sum (map getSize (snd ps))

vecAt :: Int -> IRExpr
vecAt ix = (IRIndex (IRVar vector) (IRConst (VInt ix)))

-- could probably be simplified by memoizing the total weights, or assuming normalization.
lottery :: [IRValue] -> Int -> IRExpr
lottery [value] _ = IRConst value
lottery values startIx = IRIf
  (IROp OpLessThan (IRSample IRUniform) (wtfirst))
  (IRConst (head values))
  (lottery (tail values) (startIx + 1))
    where
      nValues = length values
      wtfirst = IROp OpDiv (vecAt startIx) (totalWeight nValues startIx)

constructorLottery :: [ADTDecl] -> [(String, [PartitionPlan])] -> Int -> Int -> IRExpr
constructorLottery adts [] flagIx valueIx = IRError "No element was sampled. There was an error calculating weights!"
constructorLottery adts (plan:plans) flagIx valueIx = IRIf (IROp OpLessThan (IRSample IRUniform) (wtfirst))
  (makeGenADTConstr adts (snd plan) (fst plan) valueIx)
  (constructorLottery adts plans (flagIx + 1) (valueIx + totalSize plan))
  where
    wtfirst = IROp OpDiv (vecAt flagIx) (totalWeight (length plans + 1) flagIx)

getSize :: PartitionPlan -> Int
getSize (TuplePlan a b) = getSize a + getSize b
getSize (EitherPlan a b) = getSize a + getSize b + 1
getSize (Discretes _ (MultiDiscretes vals)) = length vals
getSize (ADTPlan _ plans) = sum (map (sum . map getSize . snd) plans) + length plans
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

makePartitionPlan :: [ADTDecl] -> RType -> Maybe MultiValue -> PartitionPlan
makePartitionPlan adts (Tuple a b) tag = TuplePlan (makePartitionPlan adts a tag1) (makePartitionPlan adts b tag2)
    where
      tag1 = (\(MultiTuple t1 _) -> t1) <$> tag
      tag2 = (\(MultiTuple _ t2) -> t2) <$> tag
makePartitionPlan adts (TEither l r) (Just (MultiEither lVal rVal)) = EitherPlan (makePartitionPlan adts l (Just lVal)) (makePartitionPlan adts r (Just rVal))
makePartitionPlan adts (TADT name) (Just (MultiADT cVals)) = ADTPlan name (map (\(cn, fields) -> (cn, map (uncurry (makePartitionPlan adts)) fields)) fieldMultiVals)
  where
    Just adt = find ((== name) . dataName) adts
    constrs = constructors adt
    fieldRTypes = map (\(c, fs) -> (c, map snd fs)) constrs
    fieldMultiVals = map (\(mCn, mVals) -> let Just c = lookup mCn fieldRTypes in (mCn, (zip c (map Just mVals)))) cVals

makePartitionPlan adts ty (Just tag) | isDiscrete ty = Discretes ty tag -- TODO: Validate that tag is sane for this.
makePartitionPlan adts ty (Nothing) | isDiscrete ty = error "no enumeration range supplied for discrete value in AutoNeural."
makePartitionPlan adts TFloat Nothing = Continuous
makePartitionPlan adts TFloat a = error ("enum range supplied to continuous value in AutoNeural:" ++ show a)
makePartitionPlan adts x y = error ("erroneous combination of type and tag in AutoNeural: " ++ show x ++ show y)

--split a tag over tuples into a tuple of tags.
splitTag :: Maybe Tag -> (Maybe Tag, Maybe Tag)
splitTag Nothing = (Nothing, Nothing)
splitTag (Just (DiscreteValues (MultiTuple a b))) = (Just (DiscreteValues a), Just (DiscreteValues b))
-- TODO: Error if set of values is not a cartesian product? Sounds like it'd break under independence assumptions.

tupleFromValue :: Value -> (Value, Value)
tupleFromValue (VTuple a b) = (a,b)
tupelFromValue _non_tuple = error "supplied non-tuple value to tuple-shaped NN type."

makeEncodeRec :: [ADTDecl] -> PartitionPlan -> Int -> IRExpr -> IRExpr
makeEncodeRec adts (Discretes rty (MultiDiscretes vals)) ix sample =
  foldr IRCons (IRConst (VList EmptyList)) [IRIndex (IRVar vector) (IRConst (VInt (ix + i))) | i <- [0 .. length vals - 1]]
makeEncodeRec adts (TuplePlan a b) ix sample =
  invokeStandardFunction stdListConcat
    [ makeEncodeRec adts a ix (IRTFst sample)
    , makeEncodeRec adts b (ix + getSize a) (IRTSnd sample)
    ]
makeEncodeRec adts Continuous ix sample =
  IRError "Continuous encoding requires IsNormal tag — not yet implemented (see 00_bidirectional-autoNeural.md)"
makeEncodeRec adts (EitherPlan _ _) ix sample =
  IRError "EitherPlan encoding requires MAR semantics — not yet implemented (see mar-sum-types-observe.md)"
makeEncodeRec adts (ADTPlan _ _) ix sample =
  IRError "ADTPlan encoding requires MAR semantics — not yet implemented (see mar-sum-types-observe.md)"

makeEncode :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> String -> IRExpr
makeEncode adts conf plan nn_name = IRLambda "sample" $
  IRLetIn vector (IRApply (IRVar nn_name) (IRVar "l_x_neural_in")) $
    makeEncodeRec adts plan 0 (IRVar "sample")

-- Find the flat logit-vector index for a given value within a plan.
-- For TuplePlan, searches the left sub-plan first, then the right at offset getSize a.
planIndexOf :: PartitionPlan -> IRValue -> Int
planIndexOf plan v = case planIndexOfMaybe plan v of
  Just i  -> i
  Nothing -> error $ "planIndexOf: value not found in plan"

planIndexOfMaybe :: PartitionPlan -> IRValue -> Maybe Int
planIndexOfMaybe (Discretes _ (MultiDiscretes vals)) v = elemIndex v (map valueToIR vals)
planIndexOfMaybe (TuplePlan a b) v =
  case planIndexOfMaybe a v of
    Just i  -> Just i
    Nothing -> (getSize a +) <$> planIndexOfMaybe b v
planIndexOfMaybe _ _ = Nothing

noAny :: IRExpr -> IRExpr -> IRExpr
noAny sample = IRIf (IRUnaryOp OpIsAny sample) (IRConst $ VFloat 1)

noAny0 :: IRExpr -> IRExpr -> IRExpr
noAny0 sample = IRIf (IRUnaryOp OpIsAny sample) (IRConst $ VFloat 0)

--TODO: Needs MAR semantics for the VAny.
--test3 = do
--  let irdefs = makeAutoNeural ("mixedTuple", TArrow TSymbol (Tuple TFloat TInt), Just $ EnumRange ((VTuple VAny (VInt 3)),(VTuple VAny (VInt 5))))
--  putStrLn (pPrintIREnv irdefs)
