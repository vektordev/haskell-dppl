module SPLL.AutoNeural(
  makeAutoNeural
, makeForwardDecl
, planLayoutString
, makePartitionPlan
, resolvePartitionAnnotation
, PartitionPlan (..)
, makeProb
, getSize
, planIndexOf
, validateWriteLogitsGaussian
, makeTopLevelWriteLogitsFun
, neuralReadLogitsSuffix
) where

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType
import SPLL.Lang.Lang
import StandardLibrary

import Data.List (find, elemIndex, isPrefixOf, intercalate)
import Utils
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe, maybeToList)
import Control.Applicative ((<|>))

-- basic strucutre:
--  get the partition plan.
--  Let's call the actual network name_getSize.
--  Call the NN to receive a vector.
--  index into vector and interpret as distribution.
--  provide sampling and inference.

-- Neural declarations forward-declare a read-logits network (Symbol -> RType): NN1, which
-- SPLL reads. Each builds an `<name>_auto` IRFunGroup with sampling and probability/density
-- readers. It hosts NO writeLogits function: the logit-vector bridge ("turn an SPLL output
-- value into logits") belongs to whichever SPLL *function* produces that value, keyed to
-- that function's own prob/normal (see 'makeTopLevelWriteLogitsFun' / task
-- encode-per-function-endpoints).  The reverse (source -> Symbol) shape has been removed; it
-- is rejected at validation.
--
-- registry: the standalone PartitionPlan annotation registry (Program.writeLogitsDecls).
-- An entry for this declaration's target type takes precedence over the declaration's own
-- "of" clause -- see 'resolvePartitionAnnotation'.
makeAutoNeural :: [ADTDecl] -> CompilerConfig -> [(RType, MultiValue)] -> NeuralDecl -> IRFunGroup
makeAutoNeural adtDecls conf registry decl@(name, declType, tag) =
  case declType of
    TArrow TSymbol target ->
      -- Read-logits case: Symbol -> target. The forward-decl string (NN1's required output
      -- layout) rides along as the group's doc so codegen emits it beside the readers.
      makeReadLogitsFunGroup adtDecls conf name target (resolvePartitionAnnotation registry target tag) (makeForwardDecl adtDecls registry decl)
    _ -> error $ "Invalid neural declaration for " ++ name ++ ": Neural networks must have Symbol on the left of the arrow (Symbol -> target)"

-- | Resolve the MultiValue annotation for a PartitionPlan target/source type: an
-- explicit registry entry (SPLL.Lang.Types.writeLogitsDecls, populated from "neural
-- writeLogits :: T of M" declarations and from every NeuralDecl's own "of" clause as sugar)
-- wins over the tag passed in directly. 'makePartitionPlan' falls back to
-- 'autoDeriveMultiValue' when this resolves to 'Nothing'.
resolvePartitionAnnotation :: [(RType, MultiValue)] -> RType -> Maybe MultiValue -> Maybe MultiValue
resolvePartitionAnnotation registry ty tag = lookup ty registry <|> tag

-- | The naming convention 'makeReadLogitsFunGroup' uses to mark a read-logits network's own
-- 'IRFunGroup' (as opposed to the value-producing SPLL function that reads
-- it): its group name is the network's declared name with this suffix
-- appended.
neuralReadLogitsSuffix :: String
neuralReadLogitsSuffix = "_auto"

-- Read-logits: Symbol -> target. Generates sampling and probability reader functions for NN1.
-- It hosts no writeLogits function (that lives on the value-producing SPLL function).
-- fwdDecl is the human-readable forward declaration (NN1's required output layout); it is
-- stored as the group's doc so codegen emits it as a header comment beside the readers.
makeReadLogitsFunGroup :: [ADTDecl] -> CompilerConfig -> String -> RType -> Maybe MultiValue -> String -> IRFunGroup
makeReadLogitsFunGroup adtDecls conf name target tag fwdDecl =
  IRFunGroup (name ++ neuralReadLogitsSuffix)
    (Just (IRLambda symbol $ makeGen adtDecls plan name, "Wrapper for the neural network function"))
    (Just (makeProb adtDecls conf plan, "Inference function for neural network function"))
    Nothing
    Nothing
    Nothing
    fwdDecl
    -- The read-logits network's own query domain is its target type's (M3). Every such
    -- group's prob also takes the symbol, so the batched backend's arity rule
    -- keeps dense mode off them for now; recording it here is the truthful
    -- answer rather than a placeholder.
    (listToMaybe $ filter multiValueIsFinite (maybeToList tag ++ [mv | Right mv <- [autoDeriveMultiValue adtDecls target]]))
    where plan = makePartitionPlan adtDecls target tag

-- | Forward declaration of a neural network (NN1): a human-readable description of the
-- read-logits network's required logit-vector output layout.  Emitted by codegen via the
-- group's doc (see 'makeReadLogitsFunGroup').  The reverse (source -> Symbol) shape has been
-- removed, so only the read-logits shape is rendered.
makeForwardDecl :: [ADTDecl] -> [(RType, MultiValue)] -> NeuralDecl -> String
makeForwardDecl adtDecls registry (name, declType, tag) =
  case declType of
    TArrow TSymbol target ->
      "neural ReadLogits " ++ name ++ " :: (Symbol -> " ++ show target ++ "); NN1 required output "
        ++ planLayoutString (makePartitionPlan adtDecls target (resolvePartitionAnnotation registry target tag))
    _ -> "neural Declaration " ++ name ++ " :: " ++ show declType ++ " (invalid: a neural network must be Symbol -> target)"

-- | A human-readable, multi-line *table* describing a PartitionPlan's flat logit-vector
-- layout.  One row per leaf slot, with columns: index-range / constraint / semantic note.
-- The note carries the structural path (fst/snd, Either L/R, ctor/field) down to the leaf's
-- meaning, so every row names both its real logit slot(s) and what they encode.  Documents
-- both the read-logits network's forward-declaration (NN1's required output, via
-- 'makeForwardDecl') and each endpoint's writeLogits function (NN2's input, via the
-- writeLogits doc).  Multi-line output is safe: codegen comments every line of a doc
-- (see CodeGenPyTorch/CodeGenJulia).
planLayoutString :: PartitionPlan -> String
planLayoutString plan =
  intercalate "\n" (heading : tableLine headerRow : tableLine sepRow : map tableLine rows)
  where
    heading       = "PartitionPlan layout (" ++ show (getSize plan) ++ " logits)"
    (rows, _)     = planRows 0 "" plan
    headerRow     = ("idx", "constraint", "meaning")
    fst3 (a,_,_)  = a
    snd3 (_,b,_)  = b
    w1            = maximum (map (length . fst3) (headerRow : rows))
    w2            = maximum (map (length . snd3) (headerRow : rows))
    sepRow        = (replicate w1 '-', replicate w2 '-', replicate (length "meaning") '-')
    pad w s       = s ++ replicate (max 0 (w - length s)) ' '
    tableLine (a, b, c) = pad w1 a ++ "  " ++ pad w2 b ++ "  " ++ c

    -- Append a child segment to a semantic path, "" being the root.
    sub p seg = if null p then seg else p ++ " / " ++ seg

    -- 'planRows ix path p' lays 'p' out starting at flat logit index 'ix', tagging each row
    -- with the breadcrumb 'path'. Indices match makeProbRec/makeGenRec exactly. Returns the
    -- rows and the next free index (ix + getSize p).
    planRows :: Int -> String -> PartitionPlan -> ([(String, String, String)], Int)
    planRows ix path (TuplePlan a b) =
      let (ra, ix1) = planRows ix  (sub path "fst") a
          (rb, ix2) = planRows ix1 (sub path "snd") b
      in (ra ++ rb, ix2)
    planRows ix path (EitherPlan l r) =
      let flagRow   = (show ix, "0..1", sub path "Either flag = P(left)")
          (rl, ix1) = planRows (ix + 1) (sub path "L") l
          (rr, ix2) = planRows ix1      (sub path "R") r
      in (flagRow : rl ++ rr, ix2)
    planRows ix path p@(Discretes rty tag) =
      let n    = getSize p
          desc = case tag of
                   MultiDiscretes vals -> "enum " ++ show rty ++ " " ++ showVals vals
                   _                   -> "enum " ++ show rty
      in ([(rangeStr ix n, "softmax", sub path desc)], ix + n)
    planRows ix path Continuous =
      ([ (show ix,       "free", sub path "Gaussian mu")
       , (show (ix + 1), "> 0",  sub path "Gaussian sigma") ], ix + 2)
    planRows ix path (ADTPlan name constrs) =
      let nFlags  = length constrs
          flagRow = (rangeStr ix nFlags, "softmax",
                     sub path (name ++ " ctor flags: " ++ intercalate "|" (map fst constrs)))
          renderConstr (acc, cix) (cName, fields) =
            let (frs, cix') = renderFields cix (sub path cName) fields
            in (acc ++ frs, cix')
          (constrRows, ixEnd) = foldl renderConstr ([], ix + nFlags) constrs
      in (flagRow : constrRows, ixEnd)

    -- a constructor's fields are laid out sequentially, each its own breadcrumb segment.
    renderFields ix _    [] = ([], ix)
    renderFields ix path fields =
      foldl (\(acc, cix) (j, f) ->
               let (rs, cix') = planRows cix (sub path ("f" ++ show j)) f
               in (acc ++ rs, cix'))
            ([], ix) (zip [0 :: Int ..] fields)

    showVals vals =
      let strs = map showLeafVal vals
      in if length strs <= 6
           then "{" ++ intercalate "," strs ++ "}"
           else "{" ++ intercalate "," (take 5 strs) ++ ",... +" ++ show (length strs - 5) ++ "}"
    showLeafVal (VBool b)  = show b
    showLeafVal (VInt i)   = show i
    showLeafVal (VFloat f) = show f
    showLeafVal v          = show v

    rangeStr ix n = if n <= 1 then show ix else show ix ++ ".." ++ show (ix + n - 1)


-- | The @data@ declaration a plan names. Plans are built against the same
-- declaration list they are later walked with, so a miss is a mismatched
-- environment rather than anything the SPLL program can express.
lookupADTDecl :: String -> [ADTDecl] -> ADTDecl
lookupADTDecl name adtDecls = fromMaybe
  (error ("AutoNeural: no `data` declaration for ADT '" ++ name ++ "'"))
  (find ((== name) . dataName) adtDecls)

-- | 'makePartitionPlan' is the only producer of 'Discretes', and it only builds
-- one from an explicit enumeration. Any other tag in that slot means a plan was
-- assembled by hand and its logit layout is undefined.
discretesTagError :: String -> RType -> MultiValue -> a
discretesTagError fn ty tag = error
  (fn ++ ": Discretes plan for " ++ show ty ++ " carries " ++ show tag
      ++ " instead of an explicit enumeration")

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

-- The read-logits network's reader assembles its result tuple by hand rather than through
-- IRCompiler's PResult algebra, so the impossibility flag (design
-- inference-result-side-channels) has to be supplied here too -- callers unpack
-- all four fields. There is no guard or indicator to take the fact from: the
-- value is a product of logit reads. What can be said soundly is that a
-- vanishing *mass* means no slot was selected, i.e. an impossible sample, while
-- a vanishing density is just a small density -- so the flag is derived from
-- the value only on the dim-0 side. Both dim and the probability are let-bound
-- (dim is a constant for every non-mixed plan and folds away).
makeProb :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> IRExpr
makeProb adtDecls _conf plan = IRLambda vector (IRLambda "sample"
  (IRLetIn probVar m (IRLetIn dimVar dim
    (IRConstruct TgTuple [IRVar probVar, IRConstruct TgTuple [IRVar dimVar, IRConstruct TgTuple [bc, imposs]]]))))
  where
    (m, dim, bc) = makeProbRec adtDecls plan 0 (IRVar "sample")
    probVar = "l_dec_p"
    dimVar  = "l_dec_dim"
    imposs  = IRIf (IROp OpEq (IRVar dimVar) (IRConst (VFloat 0)))
                   (IROp OpEq (IRVar probVar) (IRConst (VFloat 0)))
                   (IRConst (VBool False))

-- Takes a Tag from a Discretes type and a sample, and builds code that returns the index of the sample in the tag.
-- step 1: turn the tag into a list of values.
-- step 2: Use IRApply "indexOf" to find the index of the value in the list
indexOf :: MultiValue -> IRExpr -> IRExpr
indexOf (MultiDiscretes vals) sample = invokeStandardFunction stdIndexOf [sample, IRConst (constructVList (map valueToIR vals))]
indexOf tag _ = error ("indexOf: expected an explicit enumeration, got " ++ show tag)


makeProbRec :: [ADTDecl] -> PartitionPlan -> Int -> IRExpr -> (IRExpr, IRExpr, IRExpr)
makeProbRec _adtDecls (Discretes _rty tag) ix sample = (noAny sample p, IRConst $ VFloat 0, IRConst (VFloat 0))
  where
    p = IRBuiltin BListIndex [IRVar vector, IROp OpPlus (indexOf tag sample) (IRConst (VInt ix))]
makeProbRec _adtDecls Continuous ix sample = (noAny sample p, noAny0 sample (IRConst $ VFloat 1), IRConst (VFloat 0))
  where
    -- density of μ + σ·z at x: φ((x − μ)/σ)/σ, with μ = vec[ix], σ = vec[ix+1]
    sigma = IRBuiltin BListIndex [IRVar vector, IRConst (VInt $ ix + 1)]
    mu = IRBuiltin BListIndex [IRVar vector, IRConst (VInt ix)]
    p = IROp OpDiv
          (IRDensity IRNormal Linear (IROp OpDiv (IROp OpSub sample mu) sigma))
          sigma
--Not entirely sure how to combine elements in the next case. For now:
--  probabilities of the two tuple elements are multiplied.
--  dims should be added.
--  branch counts of both sides should be added.
makeProbRec adtDecls (TuplePlan a b) ix sample = (noAny sample (IROp OpMult pa pb), noAny0 sample (IROp OpPlus dima dimb), noAny0 sample (IROp OpPlus bca bcb))
  where
    (pa, dima, bca) = makeProbRec adtDecls a ix (IRDestruct AcFst sample)
    (pb, dimb, bcb) = makeProbRec adtDecls b (ix + getSize a) (IRDestruct AcSnd sample)
makeProbRec adtDecls (EitherPlan a b) ix sample = (noAny sample
  (IRIf (IRDestruct AcIsLeft sample)
    (IROp OpMult pIsLeft aP)
    (IROp OpMult pIsRight bP)),
  -- Is choosing the bc here correct, or should they be added?
  noAny0 sample (IRIf (IRDestruct AcIsLeft sample) aDim bDim), noAny0 sample (IRIf (IRDestruct AcIsLeft sample) aBc bBc))
  where
    (aP, aDim, aBc) = makeProbRec adtDecls a (ix + 1) (IRDestruct AcFromLeft sample)
    (bP, bDim, bBc) = makeProbRec adtDecls b (ix + 1 + getSize a) (IRDestruct AcFromRight sample)
    pIsLeft = IRBuiltin BListIndex [IRVar vector, IRConst (VInt ix)]
    pIsRight = IROp OpSub (IRConst $ VFloat 1) pIsLeft
makeProbRec adtDecls (ADTPlan adtName plans) ix sample = (noAny sample p, noAny0 sample dim, noAny0 sample bc)
  where
    adt = lookupADTDecl adtName adtDecls
    constrsInPlan = filter ((`elem` map fst plans) . fst) (constructors adt)
    constrsWithPlan = mapToTup (fromJust . (`lookup` plans) . fst) constrsInPlan
    constrsWithPlanAndIx = mapAppendTup constrsWithPlan constrIx
    constrsWithPlanAndIxAndFlag = mapAppendTup3 constrsWithPlanAndIx flagProbs
    constrIx = scanl (+) (ix + length plans) (map totalSize plans)
    constrGuard constr constrFlag v = IRIf (IRApply (IRVar ("is" ++ fst constr)) sample) (IROp OpMult constrFlag v) (IRConst $ VFloat 0)
    constrProbFields constr cPlan cIx constrFlag = mapTup3 (constrGuard constr constrFlag) (makeProbADTConstr adtDecls cPlan constr cIx sample)
    constrProbsFields = map (uncurry4 constrProbFields) constrsWithPlanAndIxAndFlag
    opPlus3 (a1, b1, c1) (a2, b2, c2) = (IROp OpPlus a1 a2, IROp OpPlus b1 b2, IROp OpPlus c1 c2)
    (p, dim, bc) = foldr opPlus3 (IRConst $ VFloat 0, IRConst $ VFloat 0, IRConst $ VFloat 0) constrProbsFields
    flagIx = [ix .. ix + length plans]
    flagProbs = map (\fIx -> IRBuiltin BListIndex [IRVar vector, IRConst (VInt fIx)]) flagIx


makeProbADTConstr :: [ADTDecl] -> [PartitionPlan] -> ADTConstructorDecl -> Int -> IRExpr -> (IRExpr, IRExpr, IRExpr)
makeProbADTConstr adtDecls plans (_cName, fields) ix sample = foldr multProbs prob1 fieldsProb
  where
    prob1 = (IRConst (VFloat 1), IRConst (VFloat 0), IRConst (VFloat 0))
    multProbs (p0, d0, bc0) (p1, d1, bc1) = (IROp OpMult p0 p1, IROp OpPlus d0 d1, IROp OpPlus bc0 bc1)
    fieldIx = scanl (+) ix (map getSize plans)
    fieldsProb = map (\(plan, pIx, fName) -> makeProbRec adtDecls plan pIx (IRApply (IRVar fName) sample)) (zip3 plans fieldIx (map fst fields))


makeGen :: [ADTDecl] -> PartitionPlan -> String ->  IRExpr
makeGen adtDecls plan nn_name = IRLetIn vector (IRApply (IRVar nn_name) (IRVar "l_x_neural_in")) (makeGenRec adtDecls plan 0)

makeGenRec :: [ADTDecl] -> PartitionPlan -> Int -> IRExpr
makeGenRec adtDecls (TuplePlan a b) ix = IRConstruct TgTuple [makeGenRec adtDecls a ix, makeGenRec adtDecls b (ix + getSize a)]
makeGenRec adtDecls (EitherPlan a b) ix = IRIf
  (IROp OpLessThan (IRSample IRUniform) (IRBuiltin BListIndex [IRVar vector, IRConst (VInt ix)]))
    (IRConstruct TgLeft [makeGenRec adtDecls a (ix + 1)])
    (IRConstruct TgRight [makeGenRec adtDecls b (ix + 1 + getSize a)])
makeGenRec _adtDecls (Discretes _rty (MultiDiscretes vals)) ix = lottery (map valueToIR vals) ix
makeGenRec _adtDecls Continuous ix = IROp OpPlus
  (IROp OpMult (IRSample IRNormal) (IRBuiltin BListIndex [IRVar vector, IRConst (VInt $ ix + 1)]))
  (IRBuiltin BListIndex [IRVar vector, IRConst (VInt ix)])
-- Flags occupy one slot per constructor *present in the plan* (length plans), then the
-- fields follow -- matching getSize and makeProbRec.  A depth-limited recursive ADT prunes
-- constructors at its deepest level, so `length plans` can be smaller than the full
-- `constructors adt`; the value region must start right after the flags that actually exist.
makeGenRec adtDecls (ADTPlan _ plans) ix = constructorLottery adtDecls plans ix (ix + length plans)
makeGenRec _adtDecls (Discretes ty tag) _ = discretesTagError "makeGenRec" ty tag

makeGenADTConstr :: [ADTDecl] -> [PartitionPlan] -> String -> Int -> IRExpr
makeGenADTConstr adtDecls plans name ix = foldl IRApply (IRVar name) gens
  where
    ixForField = scanl (+) ix (map (getSize) plans) -- Cumulative field offsets from this constructor's base index
    gens = map (uncurry (makeGenRec adtDecls)) (zip plans ixForField)

totalWeight :: Int -> Int -> IRExpr
-- The accumulator seed must be a float: vecAt indexes the (float) neural output
-- vector, so summing onto a VInt 0 is a type error the interpreter rejects at -O0
-- (the optimizer's `0 + x` identity rule happens to delete it at higher -O levels).
totalWeight nValues startIx = foldl (\rest ix -> IROp OpPlus rest (vecAt ix)) (IRConst (VFloat 0)) [startIx.. startIx + nValues-1]

totalSize :: (String, [PartitionPlan]) -> Int
totalSize ps = sum (map getSize (snd ps))

vecAt :: Int -> IRExpr
vecAt ix = IRBuiltin BListIndex [IRVar vector, IRConst (VInt ix)]

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
constructorLottery _adtDecls [] _flagIx _valueIx = IRError "No element was sampled. There was an error calculating weights!"
constructorLottery adtDecls (plan:plans) flagIx valueIx = IRIf (IROp OpLessThan (IRSample IRUniform) (wtfirst))
  (makeGenADTConstr adtDecls (snd plan) (fst plan) valueIx)
  (constructorLottery adtDecls plans (flagIx + 1) (valueIx + totalSize plan))
  where
    wtfirst = IROp OpDiv (vecAt flagIx) (totalWeight (length plans + 1) flagIx)

getSize :: PartitionPlan -> Int
getSize (TuplePlan a b) = getSize a + getSize b
getSize (EitherPlan a b) = getSize a + getSize b + 1
getSize (Discretes _ (MultiDiscretes vals)) = length vals
getSize (Discretes ty tag) = discretesTagError "getSize" ty tag
getSize (ADTPlan _ plans) = sum (map (sum . map getSize . snd) plans) + length plans
getSize Continuous = 2

isDiscrete :: RType -> Bool
isDiscrete TBool = True
isDiscrete TInt = True
isDiscrete (ListOf ty) = isDiscrete ty
isDiscrete (Tuple ty1 ty2) = isDiscrete ty1 && isDiscrete ty2
isDiscrete _other = False

-- | Build the logit-vector layout for an RType paired with an (optional) MultiValue
-- enumeration annotation.
--
-- 'Nothing' and the "_" placeholder (MultiAuto) are auto-derived from the RType where
-- possible (Bool, Float, Tuple/Either/non-recursive ADT of such types); Int and Symbol
-- cannot be auto-derived (unbounded domain) and require an explicit enumeration.
makePartitionPlan :: [ADTDecl] -> RType -> Maybe MultiValue -> PartitionPlan
makePartitionPlan adtDecls ty Nothing = case autoDeriveMultiValue adtDecls ty of
  Right mv -> makePartitionPlan adtDecls ty (Just mv)
  Left err -> error ("AutoNeural: " ++ err ++ " (for neural output type " ++ show ty ++ ")")
makePartitionPlan adtDecls ty (Just MultiAuto) = makePartitionPlan adtDecls ty Nothing
makePartitionPlan adtDecls (Tuple a b) (Just (MultiTuple tag1 tag2)) = TuplePlan (makePartitionPlan adtDecls a (Just tag1)) (makePartitionPlan adtDecls b (Just tag2))
makePartitionPlan adtDecls (TEither l r) (Just (MultiEither lVal rVal)) = EitherPlan (makePartitionPlan adtDecls l (Just lVal)) (makePartitionPlan adtDecls r (Just rVal))
makePartitionPlan adtDecls (TADT name) (Just (MultiADT cVals)) = ADTPlan name (map (\(cn, fields) -> (cn, map (uncurry (makePartitionPlan adtDecls)) fields)) fieldMultiVals)
  where
    adt = lookupADTDecl name adtDecls
    constrs = constructors adt
    fieldRTypes = map (\(c, fs) -> (c, map snd fs)) constrs
    -- An annotation may cover a subset of the constructors (a depth-limited
    -- recursive type prunes some), but never one the `data` declaration lacks.
    constrFieldRTypes mCn = fromMaybe
      (error ("MultiValue annotation for ADT '" ++ name ++ "' names constructor '"
              ++ mCn ++ "', which that type does not declare"))
      (lookup mCn fieldRTypes)
    fieldMultiVals = map (\(mCn, mVals) -> (mCn, zip (constrFieldRTypes mCn) (map Just mVals))) cVals
makePartitionPlan _adtDecls ty@(Tuple {}) (Just tag) = error ("MultiValue annotation for tuple type " ++ show ty ++ " must be a matching tuple, e.g. (..., ...), but got: " ++ show tag)
makePartitionPlan _adtDecls ty@(TEither {}) (Just tag) = error ("MultiValue annotation for Either type " ++ show ty ++ " must be a matching Either, e.g. (... | ...), but got: " ++ show tag)
makePartitionPlan _adtDecls ty@(TADT _) (Just tag) = error ("MultiValue annotation for ADT type " ++ show ty ++ " must be a matching ADT, e.g. {...}, but got: " ++ show tag)
makePartitionPlan _adtDecls ty (Just tag@(MultiDiscretes _)) | isDiscrete ty = Discretes ty tag
makePartitionPlan _adtDecls TFloat (Just MultiContinuous) = Continuous
makePartitionPlan _adtDecls ty (Just tag) | isDiscrete ty = error ("MultiValue annotation for discrete type " ++ show ty ++ " must be an explicit enumeration (e.g. [0,1,2]), but got: " ++ show tag)
makePartitionPlan _adtDecls TFloat (Just tag) = error ("enum range supplied to continuous (Float) value in AutoNeural: " ++ show tag ++ ". Use 'Real' or '_' for a continuous value instead.")
makePartitionPlan _adtDecls x y = error ("erroneous combination of type and tag in AutoNeural: " ++ show x ++ " / " ++ show y)

-- Encode dispatch: lay one plan (sub-)tree out into its slice of the flat logit vector.
--
-- Every slot is a *marginal query* against the host function's own prob function.  Two
-- parameters carry the context that makes such a query correct at an arbitrary depth:
--
-- * @wrap@ rebuilds the full sample value from a value at this position, filling every
--   other position with 'VAny' -- identity at the root, @\v -> VTuple v VAny@ inside a
--   tuple's first component, @\v -> VADT "Obj" [v, VAny]@ inside an ADT field, and so on.
--   Composing it on the way down is what keeps a nested slot a marginal rather than a
--   point query.
--
-- * @norm@ is the conditioning normaliser.  It is 'Nothing' at the root, where slots are
--   absolute probabilities.  Inside an Either/ADT arm it is @Just p@ with @p = P(arm)@,
--   and every slot below divides by it -- so a constructor's flag slot holds P(ctor) while
--   its field slots hold P(field value | ctor).  That categorical-times-conditional
--   factorisation is exactly what 'makeProbRec' reads back, which is why the two must
--   agree on it.
--
-- Slot counts per case match 'getSize' exactly (an EitherPlan contributes ONE flag slot,
-- P(Left), since P(Right) is its complement; an ADTPlan contributes one per constructor).
--
-- outerArgs: IRExprs for the outer lambda parameters already in scope (e.g. [IRVar "sym"]
-- for `main sym = ...`; [] for `main = expr`).  These are forwarded as trailing arguments
-- to the compiled SPLL inference functions (prob, normal).
--
-- This one walker serves both the root and the arms.  It used to be two -- a full
-- top-level dispatch plus a `makeWriteLogitsEitherArm` that handled only Discretes arms and
-- zero-stubbed every composite one, so an ADT field of any non-Discretes plan (a nested
-- enum ADT, a tuple, an Either) was written as zeros while still occupying its slots.  Keeping
-- them separate is what let the arm walker fall behind; hence the single function.
makeWriteLogitsPlan :: (IRValue -> IRValue)  -- ^ wrap: rebuild the full sample value for a marginal query
               -> String                -- ^ prob function name
               -> String                -- ^ normal function name for this position
               -> Maybe IRExpr          -- ^ arm normaliser: P(enclosing arm), or Nothing at the root
               -> PartitionPlan
               -> [IRExpr]              -- ^ outer parameters in scope
               -> IRExpr
makeWriteLogitsPlan wrap probFnName normalFnName norm plan outerArgs = case plan of
  Discretes _ (MultiDiscretes vals) ->
    irList [ slot (marginal (wrap (valueToIR v))) | v <- vals ]

  Continuous ->
    -- Call normalFnName(outerArgs...) → a (mu, sigma) tuple, then emit [mu, sigma].
    -- 'norm' is necessarily Nothing here: a continuous leaf inside an arm would need an
    -- arm-conditional (mu, sigma) that the IRCompiler does not generate, and
    -- 'requiredNormalFns' names it so 'makeTopLevelWriteLogitsFun'/'validateWriteLogitsGaussian'
    -- refuse the whole writeLogits build before reaching this point.
    let normalResult = foldl IRApply (IRVar normalFnName) outerArgs
    in irList [IRDestruct AcFst normalResult, IRDestruct AcSnd normalResult]

  TuplePlan a b -> concatLists
    [ rec (\v -> wrap (VTuple v VAny)) (normalFnName ++ "_fst") norm a
    , rec (\v -> wrap (VTuple VAny v)) (normalFnName ++ "_snd") norm b
    ]

  -- One flag slot, P(Left); each arm's own slots are conditional on that arm, so they
  -- normalise by the arm probability rather than by the enclosing 'norm'.
  EitherPlan a b ->
    let pLeftAny  = marginal (wrap (VEither (Left  VAny)))
        pRightAny = marginal (wrap (VEither (Right VAny)))
    in concatLists
         [ irList [slot pLeftAny]
         , rec (wrap . VEither . Left)  (normalFnName ++ "_left")  (Just pLeftAny)  a
         , rec (wrap . VEither . Right) (normalFnName ++ "_right") (Just pRightAny) b
         ]

  -- One flag slot per constructor, then each constructor's field block.  Field slots are
  -- conditional on their constructor (see EitherPlan above).  The normal-function names
  -- mirror 'requiredNormalFns' so its refusal check and this emission cannot disagree.
  ADTPlan _ ctors ->
    let ctorAnyVal (cName, fps) = wrap (VADT cName (replicate (length fps) VAny))
        pCtorAny = marginal . ctorAnyVal
        replaceAtLocal j v args = take j args ++ [v] ++ drop (j + 1) args
        fieldWrap cName n j v = wrap (VADT cName (replaceAtLocal j v (replicate n VAny)))
        ctorFields cp@(cName, fps) = concatLists
          [ rec (fieldWrap cName (length fps) j)
                (normalFnName ++ "_" ++ cName ++ "_" ++ show j)
                (Just (pCtorAny cp)) fp
          | (j, fp) <- zip [0 :: Int ..] fps ]
    in concatLists (irList [ slot (pCtorAny cp) | cp <- ctors ] : map ctorFields ctors)

  Discretes ty tag -> discretesTagError "makeWriteLogitsPlan" ty tag
  where
    rec w nf n p = makeWriteLogitsPlan w probFnName nf n p outerArgs
    irList       = foldr (\x acc -> IRConstruct TgCons [x, acc]) emptyList
    emptyList    = IRConst (VList EmptyList)
    marginal s   = IRDestruct AcFst (foldl IRApply (IRApply (IRVar probFnName) (IRConst s)) outerArgs)
    slot p       = maybe p (IROp OpDiv p) norm

    -- Statically-empty segments are dropped before folding rather than concatenated
    -- with: a fieldless constructor contributes one, and every nesting level would
    -- otherwise add an identity `listConcat(x, [])` to the emitted vector expression.
    concatLists xs = case filter (not . isEmptyList) xs of
      []  -> emptyList
      ys  -> foldr1 (\x acc -> invokeStandardFunction stdListConcat [x, acc]) ys
    isEmptyList (IRConst (VList EmptyList)) = True
    isEmptyList _                           = False

-- Build the writeLogits function body, wrapped in one lambda per outer parameter of main.
-- writeLogits(p1)(p2)... derives the logit vector from compiled SPLL inference functions
-- (main_prob, main_normal) — it does NOT call the NN or accept a sample argument.
makeWriteLogits :: [ADTDecl] -> CompilerConfig -> PartitionPlan -> String -> String -> [String] -> IRExpr
makeWriteLogits _adtDecls _conf plan probFnName normalFnName paramNames =
  foldr IRLambda body paramNames
  where
    outerArgs = map IRVar paramNames
    body = makeWriteLogitsPlan id probFnName normalFnName Nothing plan outerArgs

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
-- WriteLogits-mode Gaussian validation.
--
-- A `Continuous` slot in a read-logits network's plan is written by querying the SPLL
-- program's normal-parameter function (`main_normal`, or `main_normal_fst`/`_snd` for tuple
-- components) — see `makeWriteLogitsPlan`.  That function only exists when the
-- corresponding output node is Gaussian (PType `PNormal`/`PLogNormal`); for a non-Gaussian
-- continuous output (a mixture produced by `if`, a product of random variables, etc.) the
-- IRCompiler does not generate it.  Writing such an output would otherwise dangle on a
-- missing function reference at runtime.  This check turns that into a clean, attributed
-- compile error pointing at `collapse` (task encode-07).
--
-- The check is writeLogits-specific: a non-Gaussian continuous program is perfectly valid for
-- probability/generate/integrate inference, so this must not be folded into the shared
-- `compile` path.
validateWriteLogitsGaussian :: [ADTDecl] -> [(RType, MultiValue)] -> [NeuralDecl] -> IREnv -> Either CompilerError ()
validateWriteLogitsGaussian adtDecls registry neuralDecls env = mapM_ checkDecl readLogitsDecls
  where
    -- Only read-logits declarations (Symbol -> target) build a query-based writeLogits function.
    readLogitsDecls = [ (name, target, tag) | (name, TArrow TSymbol target, tag) <- neuralDecls ]
    available = availableNormalFns env
    checkDecl (name, target, tag) =
      let plan     = makePartitionPlan adtDecls target (resolvePartitionAnnotation registry target tag)
          required = requiredNormalFns "main_normal" plan
          missing  = filter (`notElem` available) required
      in if null missing then Right () else Left (writeLogitsGaussianError name)
    writeLogitsGaussianError name =
      "writeLogits: neural declaration '" ++ name ++ "' has a continuous output slot that cannot "
      ++ "be written. Either it is not Gaussian (a mixture produced by `if`, a product of "
      ++ "random variables), or it is a continuous arm inside an Either/ADT — the latter is "
      ++ "not yet supported (its arm-conditional (mu, sigma) is not generated), so it is "
      ++ "refused rather than silently zero-stubbed."

-- | Normal-parameter function names that `writeLogits` references for the Continuous slots of a
-- plan.  Mirrors the name threading in `makeWriteLogitsPlan` (top-level `main_normal`,
-- tuple components suffixed `_fst`/`_snd`).
--
-- Either/ADT arms recurse too: a continuous leaf inside an arm names an arm-conditional
-- normal function (`_left`/`_right`, `_<ctor>_<field>`) that the IRCompiler does not yet
-- generate.  By surfacing that leaf as a required-but-absent normal function,
-- `makeTopLevelWriteLogitsFun`'s `normalsOk` check refuses to build such a writeLogits function
-- (and `validateWriteLogitsGaussian` refuses to run it) rather than silently emitting a zero for
-- the arm's `(mu, sigma)`.  A fully-discrete arm contributes no requirement, so a discrete
-- Either/ADT of any nesting depth stays buildable — `makeWriteLogitsPlan` writes those arms
-- for real, and this list is exactly the continuous residue it cannot.
--
-- The names generated here must match `makeWriteLogitsPlan`'s `normalFnName` threading case for
-- case; they are a single scheme spelled in two places, one deciding refusal and one
-- deciding emission.
requiredNormalFns :: String -> PartitionPlan -> [String]
requiredNormalFns nf Continuous        = [nf]
requiredNormalFns nf (TuplePlan a b)   = requiredNormalFns (nf ++ "_fst") a
                                      ++ requiredNormalFns (nf ++ "_snd") b
requiredNormalFns nf (EitherPlan a b)  = requiredNormalFns (nf ++ "_left") a
                                      ++ requiredNormalFns (nf ++ "_right") b
requiredNormalFns nf (ADTPlan _ ctors) =
  concat [ requiredNormalFns (nf ++ "_" ++ cName ++ "_" ++ show j) fp
         | (cName, fps) <- ctors, (j, fp) <- zip [0 :: Int ..] fps ]
requiredNormalFns _  (Discretes _ _)   = []

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

-- MAR semantics for EitherPlan writing are implemented in makeWriteLogitsPlan.

------------------------------------------------------------------------
-- A top-level function's own writeLogits function (auto-derive slice of PartitionPlan decoupling).
--
-- `makeWriteLogits`'s logic only needs a PartitionPlan for some RType plus that function's
-- `<fn>_prob`/`<fn>_normal` functions; it does not need a `neural :: Symbol -> target`
-- declaration -- that's merely a historical trigger.  This builds a writeLogits function for any
-- logit-representable top-level binding directly from its own output RType, querying that
-- function's own prob/normal functions, with no neural declaration involved.  `main` is just
-- the `fn == "main"` case.  See tasks encode-main-auto-derived / encode-per-function-endpoints
-- and design encode-partitionplan-decoupling.
--
-- This is purely additive: it returns Nothing (never an error) when
--   * the type is neither in the writeLogitsDecls registry nor auto-derivable -- i.e. it
--     involves Int, Symbol, or a recursive ADT (these need an explicit annotation that the
--     auto-derive-only slice does not supply), or
--   * a Continuous slot would reference a `main_normal` function that wasn't generated
--     because the output isn't Gaussian -- the same requiredNormalFns/availableNormalFns
--     check `validateWriteLogitsGaussian` applies to read-logits declarations, or
--   * a discrete/Either/ADT slot would reference an absent `main_prob` function.
makeTopLevelWriteLogitsFun :: [ADTDecl] -> CompilerConfig -> [(RType, MultiValue)]
                      -> String       -- ^ host function name (e.g. "main", "isRed")
                      -> RType        -- ^ the binding's (return) RType
                      -> [String]     -- ^ outer parameter names of the host function
                      -> Bool         -- ^ whether the host's prob function was generated
                      -> [IRFunGroup] -- ^ groups carrying the host's normal functions (base + tuple components)
                      -> Maybe IRFunDecl
makeTopLevelWriteLogitsFun adtDecls conf registry fnName rty paramNames probAvailable normalGroups
  | not buildable       = Nothing
  | normalsOk && probOk = Just (makeWriteLogits adtDecls conf plan probFnName normalFnName paramNames, doc)
  | otherwise           = Nothing
  where
    probFnName   = fnName ++ "_prob"
    normalFnName = fnName ++ "_normal"
    tag          = resolvePartitionAnnotation registry rty Nothing
    buildable    = case tag of
                     Just _  -> True   -- explicit registry entry
                     Nothing -> case autoDeriveMultiValue adtDecls rty of
                                  Right _ -> True
                                  Left _  -> False
    plan         = makePartitionPlan adtDecls rty tag
    available    = availableNormalFns (IREnv normalGroups [] [])
    normalsOk    = all (`elem` available) (requiredNormalFns normalFnName plan)
    probOk       = not (planUsesProb plan) || probAvailable
    doc          = "WriteLogits function for " ++ fnName ++ "'s own output type; " ++ planLayoutString plan

-- | Whether a writeLogits plan references the program's prob function: true for any discrete /
-- Either / ADT slot, false for a pure-Continuous plan (which queries only the normal
-- function).
planUsesProb :: PartitionPlan -> Bool
planUsesProb Continuous       = False
planUsesProb (TuplePlan a b)  = planUsesProb a || planUsesProb b
planUsesProb (Discretes _ _)  = True
planUsesProb (EitherPlan _ _) = True
planUsesProb (ADTPlan _ _)    = True
