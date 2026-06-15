module SPLL.AutoNeural(
  makeAutoNeural
, makeForwardDecl
, makePartitionPlan
, resolvePartitionAnnotation
, PartitionPlan (..)
, getSize
, planIndexOf
, validateEncodeGaussian
, makeTopLevelEncodeFun
) where

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.Lang.Lang
import StandardLibrary

import Data.List (find, elemIndex, isPrefixOf)
import Utils
import Data.Maybe (fromJust, isJust)
import Control.Applicative ((<|>))

-- basic strucutre:
--  get the partition plan.
--  Let's call the actual network name_getSize.
--  Call the NN to receive a vector.
--  index into vector and interpret as distribution.
--  provide sampling and inference.

-- Support bidirectional neural declarations:
-- Decoder: (Symbol -> RType) — generates sampling, probability, and encoding functions
-- Encoder: (RType -> Symbol) — generates an encoding function that reconstructs logits
--
-- paramNames: outer parameter names of the SPLL 'main' binding (e.g. ["sym"] for
-- `main sym = ...`, [] for `main = ...`).  Encode mirrors this arity.
--
-- registry: the standalone PartitionPlan annotation registry (Program.encodeDecls).
-- An entry for this declaration's target/source type takes precedence over the
-- declaration's own "of" clause -- see 'resolvePartitionAnnotation'.
makeAutoNeural :: [ADTDecl] -> CompilerConfig -> String -> [String] -> [(RType, MultiValue)] -> NeuralDecl -> IRFunGroup
makeAutoNeural adts conf spllFnName paramNames registry (name, declType, tag) =
  case declType of
    TArrow TSymbol target ->
      -- Decoder case: Symbol -> target
      makeDecoderFunGroup adts conf spllFnName name target (resolvePartitionAnnotation registry target tag) paramNames
    TArrow source TSymbol ->
      -- Encoder case: source -> Symbol
      makeEncoderFunGroup adts conf name source (resolvePartitionAnnotation registry source tag)
    _ -> error $ "Invalid neural declaration for " ++ name ++ ": Neural networks must have Symbol on exactly one side of the arrow"

-- | Resolve the MultiValue annotation for a PartitionPlan target/source type: an
-- explicit registry entry (SPLL.Lang.Types.encodeDecls, populated from "neural encode ::
-- T of M" declarations and from every NeuralDecl's own "of" clause as sugar) wins over
-- the tag passed in directly. 'makePartitionPlan' falls back to 'autoDeriveMultiValue'
-- when this resolves to 'Nothing'.
resolvePartitionAnnotation :: [(RType, MultiValue)] -> RType -> Maybe MultiValue -> Maybe MultiValue
resolvePartitionAnnotation registry ty tag = lookup ty registry <|> tag

-- Decoder: Symbol -> target. Generates sampling, probability, and encoding functions.
-- encode mirrors main's outer parameter list (paramNames); it does NOT take a sym or
-- sample argument — it derives the logit vector from the compiled SPLL inference functions.
makeDecoderFunGroup :: [ADTDecl] -> CompilerConfig -> String -> String -> RType -> Maybe MultiValue -> [String] -> IRFunGroup
makeDecoderFunGroup adts conf spllFnName name target tag paramNames =
  IRFunGroup (name ++ "_auto")
    (Just (IRLambda symbol $ makeGen adts plan name, "Wrapper for the neural network function"))
    (Just (makeProb adts conf plan, "Inference function for neural network function"))
    Nothing
    (Just (makeEncode adts conf plan probFnName normalFnName paramNames, "Encoding function for NN2 input"))
    Nothing
    (show plan)
    where plan = makePartitionPlan adts target tag
          probFnName = spllFnName ++ "_prob"
          normalFnName = spllFnName ++ "_normal"

-- Encoder: source -> Symbol. Generates only an encoding function.
makeEncoderFunGroup :: [ADTDecl] -> CompilerConfig -> String -> RType -> Maybe MultiValue -> IRFunGroup
makeEncoderFunGroup adts conf name source tag =
  IRFunGroup name
    Nothing
    Nothing
    Nothing
    (Just (IRLambda "sample" $ makeEncodeTopLevel adts "" "" plan 0 [IRVar "sample"], "Encoding function that reconstructs logits from source type"))
    Nothing
    (show plan)
    where plan = makePartitionPlan adts source tag

--TODO: Output this into the output file somehow.
-- yields a forward declaration of a neural network:
-- includes a string representation of the partition plan, including constraints about outputted logits.
makeForwardDecl :: [ADTDecl] -> [(RType, MultiValue)] -> NeuralDecl -> String
makeForwardDecl adts registry (name, declType, tag) =
  case declType of
    TArrow TSymbol target ->
      "neural Decoder " ++ name ++ " :: (Symbol -> " ++ show target ++ ")\n  with layout: " ++ plan_string plan ++ ",\n  dimensionality=" ++ show (getSize plan) ++ ".\n"
      where
        plan = makePartitionPlan adts target (resolvePartitionAnnotation registry target tag)
    TArrow source TSymbol ->
      "neural Encoder " ++ name ++ " :: (" ++ show source ++ " -> Symbol)\n  with layout: " ++ plan_string plan ++ ",\n  dimensionality=" ++ show (getSize plan) ++ ".\n"
      where
        plan = makePartitionPlan adts source (resolvePartitionAnnotation registry source tag)
    _ -> "neural Declaration " ++ name ++ " :: " ++ show declType ++ " (invalid: Symbol must be on exactly one side)\n"
  where
    plan_string (TuplePlan first second) = plan_string first ++ " x " ++ plan_string second
    plan_string (EitherPlan left right) = "[1](0..1)" ++ plan_string left ++ " + " ++ plan_string right
    plan_string p@(Discretes ty tag) = "[" ++ show (getSize p) ++ "](softmax'ed)"
    plan_string Continuous = "[1],[1](>0)"
    plan_string (ADTPlan _ _) = "[complex ADT layout]"


data PartitionPlan = TuplePlan PartitionPlan PartitionPlan -- Logit layout: first, then second.
                   | EitherPlan PartitionPlan PartitionPlan -- Logit layout: flag, then left, then right
                   | Discretes RType MultiValue -- Logit layout: Enumerated values in order of "tagToValues"
                   | ADTPlan String [(String, [PartitionPlan])] -- Logit layout: Flag for each constructor, then each field of each constructor
                   | Continuous -- Logit layout: Mu, Sigma
                   deriving (Show, Eq)

vector :: String
vector = "l_x_neural_out"

symbol :: String
symbol = "l_x_neural_in"

makeProb :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> IRExpr
makeProb adts conf plan = IRLambda vector (IRLambda "sample" (IRTCons m sndRet))
  where
    (m, dim, bc) = makeProbRec adts plan 0 (IRVar "sample")
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
-- The accumulator seed must be a float: vecAt indexes the (float) neural output
-- vector, so summing onto a VInt 0 is a type error the interpreter rejects at -O0
-- (the optimizer's `0 + x` identity rule happens to delete it at higher -O levels).
totalWeight nValues startIx = foldl (\rest ix -> IROp OpPlus rest (vecAt ix)) (IRConst (VFloat 0)) [startIx.. startIx + nValues-1]

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

isDiscrete :: RType -> Bool
isDiscrete TBool = True
isDiscrete TInt = True
isDiscrete (ListOf ty) = isDiscrete ty
isDiscrete (Tuple ty1 ty2) = isDiscrete ty1 && isDiscrete ty2
isDiscrete other = False

-- | Build the logit-vector layout for an RType paired with an (optional) MultiValue
-- enumeration annotation.
--
-- 'Nothing' and the "_" placeholder (MultiAuto) are auto-derived from the RType where
-- possible (Bool, Float, Tuple/Either/non-recursive ADT of such types); Int and Symbol
-- cannot be auto-derived (unbounded domain) and require an explicit enumeration.
makePartitionPlan :: [ADTDecl] -> RType -> Maybe MultiValue -> PartitionPlan
makePartitionPlan adts ty Nothing = case autoDeriveMultiValue adts ty of
  Right mv -> makePartitionPlan adts ty (Just mv)
  Left err -> error ("AutoNeural: " ++ err ++ " (for neural output type " ++ show ty ++ ")")
makePartitionPlan adts ty (Just MultiAuto) = makePartitionPlan adts ty Nothing
makePartitionPlan adts (Tuple a b) (Just (MultiTuple tag1 tag2)) = TuplePlan (makePartitionPlan adts a (Just tag1)) (makePartitionPlan adts b (Just tag2))
makePartitionPlan adts (TEither l r) (Just (MultiEither lVal rVal)) = EitherPlan (makePartitionPlan adts l (Just lVal)) (makePartitionPlan adts r (Just rVal))
makePartitionPlan adts (TADT name) (Just (MultiADT cVals)) = ADTPlan name (map (\(cn, fields) -> (cn, map (uncurry (makePartitionPlan adts)) fields)) fieldMultiVals)
  where
    Just adt = find ((== name) . dataName) adts
    constrs = constructors adt
    fieldRTypes = map (\(c, fs) -> (c, map snd fs)) constrs
    fieldMultiVals = map (\(mCn, mVals) -> let Just c = lookup mCn fieldRTypes in (mCn, (zip c (map Just mVals)))) cVals
makePartitionPlan adts ty@(Tuple {}) (Just tag) = error ("MultiValue annotation for tuple type " ++ show ty ++ " must be a matching tuple, e.g. (..., ...), but got: " ++ show tag)
makePartitionPlan adts ty@(TEither {}) (Just tag) = error ("MultiValue annotation for Either type " ++ show ty ++ " must be a matching Either, e.g. (... | ...), but got: " ++ show tag)
makePartitionPlan adts ty@(TADT _) (Just tag) = error ("MultiValue annotation for ADT type " ++ show ty ++ " must be a matching ADT, e.g. {...}, but got: " ++ show tag)
makePartitionPlan adts ty (Just tag@(MultiDiscretes _)) | isDiscrete ty = Discretes ty tag
makePartitionPlan adts TFloat (Just MultiContinuous) = Continuous
makePartitionPlan adts ty (Just tag) | isDiscrete ty = error ("MultiValue annotation for discrete type " ++ show ty ++ " must be an explicit enumeration (e.g. [0,1,2]), but got: " ++ show tag)
makePartitionPlan adts TFloat (Just tag) = error ("enum range supplied to continuous (Float) value in AutoNeural: " ++ show tag ++ ". Use 'Real' or '_' for a continuous value instead.")
makePartitionPlan adts x y = error ("erroneous combination of type and tag in AutoNeural: " ++ show x ++ " / " ++ show y)

--split a tag over tuples into a tuple of tags.
splitTag :: Maybe Tag -> (Maybe Tag, Maybe Tag)
splitTag Nothing = (Nothing, Nothing)
splitTag (Just (DiscreteValues (MultiTuple a b))) = (Just (DiscreteValues a), Just (DiscreteValues b))
-- TODO: Error if set of values is not a cartesian product? Sounds like it'd break under independence assumptions.

tupleFromValue :: Value -> (Value, Value)
tupleFromValue (VTuple a b) = (a,b)
tupelFromValue _non_tuple = error "supplied non-tuple value to tuple-shaped NN type."

-- | Encode the inner slots for one arm of an EitherPlan.
-- wrap: constructs the full sample value (e.g. VEither . Left) for probFnName calls.
-- armProb: IRExpr evaluating to P(arm VAny), used to normalise to conditional probability.
-- For Discretes inner plans, emits P(arm v) / P(arm VAny) for each v.
-- For complex plans, falls back to zeros (length-correct stub).
makeEncodeEitherArm :: String -> [IRExpr] -> PartitionPlan -> (IRValue -> IRValue) -> IRExpr -> IRExpr
makeEncodeEitherArm probFnName outerArgs (Discretes _ (MultiDiscretes vals)) wrap armProb =
  foldr IRCons (IRConst (VList EmptyList))
    [ IROp OpDiv
        (IRTFst (foldl IRApply (IRApply (IRVar probFnName) (IRConst (wrap (valueToIR v)))) outerArgs))
        armProb
    | v <- vals ]
makeEncodeEitherArm probFnName outerArgs plan wrap armProb =
  -- Complex inner plan: fall back to zeros (length-correct stub).
  foldr IRCons (IRConst (VList EmptyList))
    [ IRConst (VFloat 0) | _ <- [0 .. getSize plan - 1] ]

-- Top-level encode dispatch.
--
-- outerArgs: IRExprs for the outer lambda parameters already in scope (e.g. [IRVar "sym"]
-- for `main sym = ...`; [] for `main = expr`).  These are forwarded as trailing arguments
-- to the compiled SPLL inference functions (prob, normal).
--
-- * Discretes: calls probFnName(wrap v)(outerArgs...) for each enumerated v.  wrap
--   constructs the full sample value for the marginal query; at the outermost level it is
--   id, inside a TuplePlan first component it is (\v -> VTuple v VAny), etc.
--   Falls back to raw logit slots only when probFnName is empty (encoder case).
--
-- * Continuous: calls normalFnName(outerArgs...) → (mu, sigma).
--
-- * TuplePlan / EitherPlan: recurses with composed wrap functions so sub-plan prob calls
--   correctly query the marginal distribution of each component.
--
-- * ADTPlan: stub — emits zeros of the correct length.
makeEncodeTopLevel :: [ADTDecl] -> String -> String -> PartitionPlan -> Int -> [IRExpr] -> IRExpr
makeEncodeTopLevel = makeEncodeTopLevelW id

makeEncodeTopLevelW :: (IRValue -> IRValue) -> [ADTDecl] -> String -> String -> PartitionPlan -> Int -> [IRExpr] -> IRExpr
makeEncodeTopLevelW wrap adts probFnName normalFnName (Discretes rty (MultiDiscretes vals)) ix outerArgs =
  if null probFnName
  then -- No prob function available (encoder case): fall back to raw logit slots.
    foldr IRCons (IRConst (VList EmptyList))
      [IRIndex (IRVar vector) (IRConst (VInt (ix + i))) | i <- [0 .. length vals - 1]]
  else
    foldr IRCons (IRConst (VList EmptyList))
      [ IRTFst (foldl IRApply (IRApply (IRVar probFnName) (IRConst (wrap (valueToIR v)))) outerArgs)
      | v <- vals ]
makeEncodeTopLevelW wrap adts probFnName normalFnName Continuous ix outerArgs =
  -- Call normalFnName(outerArgs...) → IRTCons mu sigma, then emit [mu, sigma].
  let normalResult = foldl IRApply (IRVar normalFnName) outerArgs
  in foldr IRCons (IRConst (VList EmptyList))
       [ IRTFst normalResult
       , IRTSnd normalResult
       ]
makeEncodeTopLevelW wrap adts probFnName normalFnName (TuplePlan a b) ix outerArgs =
  -- Compose wrap with the tuple projection so sub-plan prob calls are marginal queries:
  -- first component: probFn (wrap (VTuple v VAny)), second: probFn (wrap (VTuple VAny v)).
  let fstNormalFn = if null normalFnName then "" else normalFnName ++ "_fst"
      sndNormalFn = if null normalFnName then "" else normalFnName ++ "_snd"
      fstWrap v = wrap (VTuple v VAny)
      sndWrap v = wrap (VTuple VAny v)
  in invokeStandardFunction stdListConcat
    [ makeEncodeTopLevelW fstWrap adts probFnName fstNormalFn a ix outerArgs
    , makeEncodeTopLevelW sndWrap adts probFnName sndNormalFn b (ix + getSize a) outerArgs
    ]
makeEncodeTopLevelW wrap adts probFnName normalFnName plan@(EitherPlan a b) ix outerArgs
  | null probFnName =
      foldr IRCons (IRConst (VList EmptyList))
        [ IRConst (VFloat 0) | _ <- [0 .. getSize plan - 1] ]
  | otherwise =
      let callProb s = foldl IRApply (IRApply (IRVar probFnName) (IRConst s)) outerArgs
          pLeftAny  = IRTFst (callProb (wrap (VEither (Left VAny))))
          pRightAny = IRTFst (callProb (wrap (VEither (Right VAny))))
          flagSlot  = IRCons pLeftAny (IRConst (VList EmptyList))
          leftWrap v  = wrap (VEither (Left v))
          rightWrap v = wrap (VEither (Right v))
          leftEnc   = makeEncodeEitherArm probFnName outerArgs a leftWrap pLeftAny
          rightEnc  = makeEncodeEitherArm probFnName outerArgs b rightWrap pRightAny
      in invokeStandardFunction stdListConcat
           [ flagSlot
           , invokeStandardFunction stdListConcat [leftEnc, rightEnc] ]
makeEncodeTopLevelW wrap adts probFnName normalFnName plan@(ADTPlan adtName plans) ix outerArgs
  | null probFnName =
      foldr IRCons (IRConst (VList EmptyList))
        [ IRConst (VFloat 0) | _ <- [0 .. getSize plan - 1] ]
  | otherwise =
      let callProb s = foldl IRApply (IRApply (IRVar probFnName) (IRConst s)) outerArgs
          concatLists = foldr (\x acc -> invokeStandardFunction stdListConcat [x, acc]) (IRConst (VList EmptyList))
          constrAnyVal (cName, fieldPlans) = VADT cName (replicate (length fieldPlans) VAny)
          constrFlagProb cp = IRTFst (callProb (wrap (constrAnyVal cp)))
          flagSlots = foldr IRCons (IRConst (VList EmptyList)) [ constrFlagProb cp | cp <- plans ]
          encodeConstrFields (cName, fieldPlans) pConstrAny =
            let anyArgs  = replicate (length fieldPlans) VAny
                replaceAt j v args = take j args ++ [v] ++ drop (j+1) args
                fieldWrap j v = wrap (VADT cName (replaceAt j v anyArgs))
                encodeField j fp = makeEncodeEitherArm probFnName outerArgs fp (fieldWrap j) pConstrAny
            in concatLists [ encodeField j fp | (j, fp) <- zip [0..] fieldPlans ]
          constrFieldEncodings = [ encodeConstrFields cp (constrFlagProb cp) | cp <- plans ]
      in concatLists (flagSlots : constrFieldEncodings)

-- Build the encode function body, wrapped in one lambda per outer parameter of main.
-- encode(p1)(p2)... derives the logit vector from compiled SPLL inference functions
-- (main_prob, main_normal) — it does NOT call the NN or accept a sample argument.
makeEncode :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> String -> String -> [String] -> IRExpr
makeEncode adts conf plan probFnName normalFnName paramNames =
  foldr IRLambda body paramNames
  where
    outerArgs = map IRVar paramNames
    body = makeEncodeTopLevel adts probFnName normalFnName plan 0 outerArgs

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
planIndexOfMaybe (EitherPlan a _) (VEither (Left v))  = (1 +)             <$> planIndexOfMaybe a v
planIndexOfMaybe (EitherPlan a b) (VEither (Right v)) = (1 + getSize a +) <$> planIndexOfMaybe b v
planIndexOfMaybe _ _ = Nothing

noAny :: IRExpr -> IRExpr -> IRExpr
noAny sample = IRIf (IRUnaryOp OpIsAny sample) (IRConst $ VFloat 1)

noAny0 :: IRExpr -> IRExpr -> IRExpr
noAny0 sample = IRIf (IRUnaryOp OpIsAny sample) (IRConst $ VFloat 0)

------------------------------------------------------------------------
-- Encode-mode Gaussian validation.
--
-- A `Continuous` slot in a decoder's plan is encoded by querying the SPLL program's
-- normal-parameter function (`main_normal`, or `main_normal_fst`/`_snd` for tuple
-- components) — see `makeEncodeTopLevelW`.  That function only exists when the
-- corresponding output node is Gaussian (PType `PNormal`/`PLogNormal`); for a non-Gaussian
-- continuous output (a mixture produced by `if`, a product of random variables, etc.) the
-- IRCompiler does not generate it.  Encoding such an output would otherwise dangle on a
-- missing function reference at runtime.  This check turns that into a clean, attributed
-- compile error pointing at `collapse` (task encode-07).
--
-- The check is encode-specific: a non-Gaussian continuous program is perfectly valid for
-- probability/generate/integrate inference, so this must not be folded into the shared
-- `compile` path.
validateEncodeGaussian :: [ADTDecl] -> [(RType, MultiValue)] -> [NeuralDecl] -> IREnv -> Either CompilerError ()
validateEncodeGaussian adts registry neuralDecls env = mapM_ checkDecl decoderDecls
  where
    -- Only decoder declarations (Symbol -> target) build a query-based encode function.
    decoderDecls = [ (name, target, tag) | (name, TArrow TSymbol target, tag) <- neuralDecls ]
    available = availableNormalFns env
    checkDecl (name, target, tag) =
      let plan     = makePartitionPlan adts target (resolvePartitionAnnotation registry target tag)
          required = requiredNormalFns "main_normal" plan
          missing  = filter (`notElem` available) required
      in if null missing then Right () else Left (encodeGaussianError name)
    encodeGaussianError name =
      "encode: neural declaration '" ++ name ++ "' has a continuous output that is not "
      ++ "Gaussian (PNormal/PLogNormal) — e.g. a mixture produced by `if`, or a product of "
      ++ "random variables. A non-Gaussian continuous slot cannot be encoded; insert an "
      ++ "explicit `collapse` at the offending node (see task encode-07)."

-- | Normal-parameter function names that `encode` references for the Continuous slots of a
-- plan.  Mirrors the name threading in `makeEncodeTopLevelW` (top-level `main_normal`,
-- tuple components suffixed `_fst`/`_snd`).  Either/ADT arms are currently zero-stubbed and
-- reference no normal function, so they contribute no requirement.
requiredNormalFns :: String -> PartitionPlan -> [String]
requiredNormalFns nf Continuous       = [nf]
requiredNormalFns nf (TuplePlan a b)  = requiredNormalFns (nf ++ "_fst") a
                                     ++ requiredNormalFns (nf ++ "_snd") b
requiredNormalFns _  (Discretes _ _)  = []
requiredNormalFns _  (EitherPlan _ _) = []
requiredNormalFns _  (ADTPlan _ _)    = []

-- | Normal-parameter function names actually present in the compiled environment.  Mirrors
-- the registration in `reduceIREnv`: `_component_<name>` groups register under `<name>`,
-- every other group's normal function registers under `<groupName>_normal`.
availableNormalFns :: IREnv -> [String]
availableNormalFns (IREnv groups _ _) =
  [ normalName g | g <- groups, isJust (normalFun g) ]
  where
    normalName g
      | "_component_" `isPrefixOf` groupName g = drop (length "_component_") (groupName g)
      | otherwise                              = groupName g ++ "_normal"

-- MAR semantics for EitherPlan encoding are implemented in makeEncodeTopLevelW/makeEncodeEitherArm.

------------------------------------------------------------------------
-- main's own encode function (auto-derive slice of PartitionPlan decoupling).
--
-- `makeEncode`'s logic only needs a PartitionPlan for some RType plus the program's
-- `main_prob`/`main_normal` functions; it does not need a `neural :: Symbol -> target`
-- declaration -- that's merely the current trigger.  This builds an encode function for a
-- top-level binding (`main`) directly from its own output RType, with no neural declaration
-- involved, whenever that type is representable as a logit vector.  See task
-- encode-main-auto-derived / design encode-partitionplan-decoupling.
--
-- This is purely additive: it returns Nothing (never an error) when
--   * the type is neither in the encodeDecls registry nor auto-derivable -- i.e. it
--     involves Int, Symbol, or a recursive ADT (these need an explicit annotation that the
--     auto-derive-only slice does not supply), or
--   * a Continuous slot would reference a `main_normal` function that wasn't generated
--     because the output isn't Gaussian -- the same requiredNormalFns/availableNormalFns
--     check `validateEncodeGaussian` applies to decoder declarations, or
--   * a discrete/Either/ADT slot would reference an absent `main_prob` function.
makeTopLevelEncodeFun :: [ADTDecl] -> CompilerConfig -> [(RType, MultiValue)]
                      -> RType        -- ^ the binding's (return) RType
                      -> [String]     -- ^ outer parameter names of main
                      -> Bool         -- ^ whether main's prob function was generated
                      -> [IRFunGroup] -- ^ groups carrying main's normal functions (base + tuple components)
                      -> Maybe IRFunDecl
makeTopLevelEncodeFun adts conf registry rty paramNames probAvailable normalGroups
  | not buildable       = Nothing
  | normalsOk && probOk = Just (makeEncode adts conf plan probFnName normalFnName paramNames, doc)
  | otherwise           = Nothing
  where
    probFnName   = "main_prob"
    normalFnName = "main_normal"
    tag          = resolvePartitionAnnotation registry rty Nothing
    buildable    = case tag of
                     Just _  -> True   -- explicit registry entry
                     Nothing -> case autoDeriveMultiValue adts rty of
                                  Right _ -> True
                                  Left _  -> False
    plan         = makePartitionPlan adts rty tag
    available    = availableNormalFns (IREnv normalGroups [] [])
    normalsOk    = all (`elem` available) (requiredNormalFns normalFnName plan)
    probOk       = not (planUsesProb plan) || probAvailable
    doc          = "Encoding function for main's own output type"

-- | Whether an encode plan references the program's prob function: true for any discrete /
-- Either / ADT slot, false for a pure-Continuous plan (which queries only the normal
-- function).
planUsesProb :: PartitionPlan -> Bool
planUsesProb Continuous       = False
planUsesProb (TuplePlan a b)  = planUsesProb a || planUsesProb b
planUsesProb (Discretes _ _)  = True
planUsesProb (EitherPlan _ _) = True
planUsesProb (ADTPlan _ _)    = True
