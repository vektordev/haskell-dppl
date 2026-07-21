module SPLL.IROptimizer (
  optimizeEnv
, failConversion
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.Functor ( (<&>) )
import Data.Number.Erf (erf)
import Data.Bits (xor)
import Data.List (maximumBy, foldl', findIndex, partition)
import Data.Ord (comparing)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (State, evalState, get, put)
import SPLL.Lang.Lang (floatApproxEqThresh)


optimizeEnv :: CompilerConfig -> IREnv -> IREnv
optimizeEnv conf (IREnv funcs adts consts) = IREnv (map (\(IRFunGroup name gen prob integ encode normal doc) -> IRFunGroup name (gen <&> pp) (prob <&> pp) (integ <&> pp) (encode <&> pp) (normal <&> pp) doc) funcs) adts consts
  where pp (expr, doc) = (postProcess conf expr, doc)

postProcess :: CompilerConfig -> IRExpr -> IRExpr
--postProcess = id
postProcess conf = fixedPointIteration (optimize conf)

isValue :: IRExpr -> Bool
isValue (IRConst _) = True
isValue _ = False

unval :: IRExpr -> IRValue
unval (IRConst val) = val
unval _ = error "tried to unval a non-val"

--strip all top-level lambdas and collect the bound names.
--unwrapTLLambdas :: Expr t a -> ([Varname], Expr t a)
--unwrapTLLambdas (Lambda _ name subExpr) = (name : innerNames, unwrappedExpr)
--  where (innerNames, unwrappedExpr) = unwrapTLLambdas subExpr
--unwrapTLLambdas expr = ([], expr)


fixedPointIteration :: (Eq a, Show a) => (a -> a) -> a -> a
fixedPointIteration f x = if fx == x then x else fixedPointIteration f fx
  where fx = f x

optimize :: CompilerConfig -> IRExpr -> IRExpr
-- CSE runs as a whole-expression pass (not per-node via irMap) so it can hand out
-- globally-unique binding names; running it per node lets the same name be reused
-- at different nesting levels, which produces shadowing bugs.
optimize conf = commonSubexprStage . irMap (applyConstStage . assiciativityStage . letInStage . constantDistrStage . simplifyStage . indexStage . distributeConditionals . lambdaApplicationStage . pruneAnyCkecksStage)
  where
    oLvl = optimizerLevel conf
    commonSubexprStage = if oLvl >= 2 then optimizeCommonSubexpr else id
    applyConstStage = if oLvl >= 2 then applyConstant else id
    assiciativityStage = if oLvl >= 2 then optimizeAssociativity else id
    letInStage = if oLvl >= 2 then optimizeLetIns else id
    constantDistrStage = if oLvl >= 2 then evalConstantDistr else id
    simplifyStage = if oLvl >= 1 then simplify else id
    indexStage = if oLvl >= 1 then indexmagic else id
    distributeConditionals = if oLvl >= 2 then distributeIf else id
    lambdaApplicationStage = if oLvl >= 2 then applyToLetIn else id
    pruneAnyCkecksStage = if pruneAnyChecks conf then pruneAnyCkecksExpr else id

indexmagic :: IRExpr -> IRExpr
-- if calling Apply ("indexOf") elem [0..], replace with elem
indexmagic (IRApply (IRApply (IRVar "indexOf") elem) (IRConst (VList list))) | isNaturals (toList list) = elem
  where
    isNaturals lst = and (zipWith (==) [0..] (map toNatural lst))
    toNatural (VInt x) = x
    toNatural _ = -1 -- not a natural number, should fail the above.
indexmagic x = x

-- A tuple of conditionals sharing one condition can be hoisted into a single
-- conditional over tuples, e.g. (if c then x else y, if c then z else w) becomes
-- if c then (x, z) else (y, w).  Generalised to any nesting of IRTCons: whenever
-- every leaf of the tuple tree is an IRIf with the same condition, pull that
-- condition out and split the tree into a then-tree and an else-tree.
distributeIf :: IRExpr -> IRExpr
distributeIf e@(IRTCons _ _)
  | allLeavesShareCond = IRIf cond (mapTupleLeaves ifThen e) (mapTupleLeaves ifElse e)
  where
    leaves = tupleTreeLeaves e
    conds = [c | IRIf c _ _ <- leaves]
    allLeavesShareCond = length conds == length leaves && all (== head conds) (tail conds)
    cond = head conds
    ifThen (IRIf _ t _) = t
    ifThen x = x
    ifElse (IRIf _ _ el) = el
    ifElse x = x
distributeIf x = x

-- | The leaves of a tree of nested IRTCons (everything that is not itself an IRTCons).
tupleTreeLeaves :: IRExpr -> [IRExpr]
tupleTreeLeaves (IRTCons a b) = tupleTreeLeaves a ++ tupleTreeLeaves b
tupleTreeLeaves x = [x]

-- | Rebuild a tree of nested IRTCons, applying f to each leaf.
mapTupleLeaves :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
mapTupleLeaves f (IRTCons a b) = IRTCons (mapTupleLeaves f a) (mapTupleLeaves f b)
mapTupleLeaves f x = f x

--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators

-- | Simplify terms that apply a constant to a lambda expression
-- if we build a lambda expression and immediately apply a constant, replace mentions of the lambda'd variable with the constant.
applyConstant :: IRExpr -> IRExpr
applyConstant (IRApply (IRLambda varname inExpr) v@(IRConst _)) = replaceAll (IRVar varname) v inExpr
applyConstant x = x

optimizeAssociativity :: IRExpr -> IRExpr
-- Associative Addition
optimizeAssociativity (IROp OpPlus leftV (IROp OpPlus rightV1 rightV2))
  | isValue leftV && isValue rightV1 = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV) (unval rightV1))) rightV2   -- a + (b + c) = (a + b) + c
  | isValue leftV && isValue rightV2 = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV) (unval rightV2))) rightV1   -- a + (b + c) = b + (a + c)
optimizeAssociativity (IROp OpPlus (IROp OpPlus leftV1 leftV2) rightV )
  | isValue leftV1 && isValue rightV = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV1) (unval rightV))) leftV2   -- a + (b + c) = (a + b) + c
  | isValue leftV2 && isValue rightV = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV2) (unval rightV))) leftV1   -- a + (b + c) = b + (a + c)
-- Associative Multiplication
optimizeAssociativity (IROp OpMult leftV (IROp OpMult rightV1 rightV2))
  | isValue leftV && isValue rightV1 = IROp OpMult (IRConst (forceOp OpMult (unval leftV) (unval rightV1))) rightV2   -- a * (b * c) = (a * b) * c
  | isValue leftV && isValue rightV2 = IROp OpMult (IRConst (forceOp OpMult (unval leftV) (unval rightV2))) rightV1   -- a * (b * c) = (a * c) * b
optimizeAssociativity (IROp OpMult (IROp OpMult leftV1 leftV2) rightV )
  | isValue leftV1 && isValue rightV = IROp OpMult (IRConst (forceOp OpMult (unval leftV1) (unval rightV))) leftV2   -- a + (b + c) = (a + b) + c
  | isValue leftV2 && isValue rightV = IROp OpMult (IRConst (forceOp OpMult (unval leftV2) (unval rightV))) leftV1   -- a + (b + c) = b + (a + c)
optimizeAssociativity x = x

optimizeLetIns :: IRExpr -> IRExpr
optimizeLetIns (IRLetIn name val scope)
  -- Only IRConst is safe to duplicate unconditionally. A bare IRVar can name a
  -- nullary generator (e.g. coin_gen) whose evaluation samples randomness, so
  -- inlining it into multiple uses re-draws the sample (see ir-effectful-var-purity).
  -- Multi-use non-const bindings stay as a let; single use is still inlined below.
  | isValue val = replaceAll (IRVar name) val scope
  | countUses name scope == 1 && not (usedInEnumSumBodyInvariant name val scope) = replaceAll (IRVar name) val scope
  | countUses name scope == 0 = scope
optimizeLetIns ex = ex

-- | True if `var` is used inside an IREnumSum body in `scope` AND `val` does not
-- reference any loop variable of those IREnumSums.  Such a binding is
-- loop-invariant and should be hoisted rather than inlined into the loop body.
usedInEnumSumBodyInvariant :: String -> IRExpr -> IRExpr -> Bool
usedInEnumSumBodyInvariant var val scope =
  usedInEnumSumBody var scope &&
  all (\loopVar -> countUses loopVar val == 0) (enumSumBoundVars scope)

-- | True if `var` appears free inside at least one IREnumSum body in `expr`.
usedInEnumSumBody :: String -> IRExpr -> Bool
usedInEnumSumBody var (IREnumSum _ _ body) = countUses var body > 0
usedInEnumSumBody var expr = any (usedInEnumSumBody var) (getIRSubExprs expr)

-- | Collect all variables bound by IREnumSum nodes in an expression.
enumSumBoundVars :: IRExpr -> [String]
enumSumBoundVars (IREnumSum n _ body) = n : enumSumBoundVars body
enumSumBoundVars expr = concatMap enumSumBoundVars (getIRSubExprs expr)

evalConstantDistr :: IRExpr -> IRExpr
evalConstantDistr (IRDensity IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x)))
evalConstantDistr (IRCumulative IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1/2) * (1 + erf (x/sqrt (2)))))
evalConstantDistr (IRDensity IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x >= 0 && x <= 1 then 1 else 0))
evalConstantDistr (IRCumulative IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x < 0 then 0 else if x > 1 then 1 else x))
evalConstantDistr x = x

simplify :: IRExpr -> IRExpr
simplify (IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | isValue leftV || isValue rightV = softForceLogic op leftV rightV
simplify (IRUnaryOp OpIsAny x) = forceAnyCheck x
simplify (IRUnaryOp op val) | isValue val = IRConst $ forceUnaryOp op (unval val)
simplify (IRIf _ left right) | left == right = left
simplify x@(IRIf cond left right) =
  if isValue cond
    then if unval cond == VBool True
      then left
      else right
    else x
simplify x@(IRCons left right) =
  if isValue left && isValue right
    then let (VList tl) = unval right in IRConst (VList (ListCont (unval left) tl))
    else x 
simplify (IRHead (IRCons a _)) = a
simplify (IRTail (IRCons _ b)) = b
simplify (IRTFst (IRTCons a _)) = a
simplify (IRTSnd (IRTCons _ b)) = b
--simplify (IRHead (IRConst (VList (ListCont a _)))) = IRConst a
--simplify (IRTail (IRConst (VList (ListCont _ a)))) = IRConst (VList a)
simplify x = x

countUses :: String -> IRExpr -> Int
countUses var (IRVar a) | a == var = 1
countUses var expr = sum (map (countUses var) (getIRSubExprs expr))

replaceAll :: IRExpr -> IRExpr -> IRExpr -> IRExpr
replaceAll find replaceWith = irMap (replace find replaceWith)

replace :: Eq p => p -> p -> p -> p
replace find replace' expr = if find == expr then replace' else expr

failConversion :: Expr -> IRExpr
failConversion = error "Cannot convert VClosure"

softForceLogic :: Operand -> IRExpr -> IRExpr -> IRExpr
--logic operands: or and and
softForceLogic OpOr (IRConst (VBool True)) _ = IRConst (VBool True)
softForceLogic OpOr _ (IRConst (VBool True)) = IRConst (VBool True)
softForceLogic OpOr (IRConst (VBool False)) right = right
softForceLogic OpOr left (IRConst (VBool False)) = left
softForceLogic OpAnd (IRConst (VBool True)) right = right
softForceLogic OpAnd left (IRConst (VBool True)) = left
softForceLogic OpAnd (IRConst (VBool False)) _ = IRConst (VBool False)
softForceLogic OpAnd _ (IRConst (VBool False)) = IRConst (VBool False)
softForceLogic OpEq (IRCons _ _) (IRConst (VList EmptyList)) = IRConst $ VBool False
softForceLogic OpEq (IRConst (VList EmptyList)) (IRCons _ _)  = IRConst $ VBool False
-- numeric arithmetic, shared between Int and Float via isNumZero / isNumOne.
-- The matched zero/one constant is reused so the result keeps the operand's type.
softForceLogic OpPlus (IRConst z) right | isNumZero z = right
softForceLogic OpPlus left (IRConst z) | isNumZero z = left
softForceLogic OpMult z@(IRConst zv) _ | isNumZero zv = z
softForceLogic OpMult _ z@(IRConst zv) | isNumZero zv = z
softForceLogic OpMult (IRConst o) right | isNumOne o = right
softForceLogic OpMult left (IRConst o) | isNumOne o = left
softForceLogic OpDiv left (IRConst o) | isNumOne o = left
softForceLogic OpDiv _ (IRConst z) | isNumZero z = error "tried to divide by zero in softForceArithmetic"
softForceLogic OpDiv z@(IRConst zv) _ | isNumZero zv = z
softForceLogic OpSub left (IRConst z) | isNumZero z = left
softForceLogic op left right = IROp op left right     -- Nothing can be done

-- | A numeric zero, regardless of Int/Float.
isNumZero :: IRValue -> Bool
isNumZero (VInt 0) = True
isNumZero (VFloat 0) = True
isNumZero _ = False

-- | A numeric one, regardless of Int/Float.
isNumOne :: IRValue -> Bool
isNumOne (VInt 1) = True
isNumOne (VFloat 1) = True
isNumOne _ = False

forceOp :: Operand -> IRValue -> IRValue -> IRValue
forceOp OpEq (VList AnyList) (VList _) = VBool True
forceOp OpEq (VList _) (VList AnyList) = VBool True
forceOp OpEq (VList EmptyList) (VList EmptyList) = VBool True
forceOp OpEq (VList (ListCont VAny _)) (VList (ListCont _ _)) = VBool True
forceOp OpEq (VList (ListCont _ _)) (VList (ListCont VAny _)) = VBool True
forceOp OpEq (VList (ListCont _ as)) (VList (ListCont _ bs)) = forceOp OpEq (VList as) (VList bs)
forceOp OpEq (VList _) (VList _) = VBool False
forceOp OpEq a b = VBool $ a == b
forceOp OpApprox (VFloat x) (VFloat y) = VBool $ abs (x - y) <= floatApproxEqThresh
forceOp OpMult (VInt x) (VInt y) = VInt (x*y)
forceOp OpMult (VFloat x) (VFloat y) = VFloat (x*y)
forceOp OpPlus (VInt x) (VInt y) = VInt (x+y)
forceOp OpPlus (VFloat x) (VFloat y) = VFloat (x+y)
forceOp OpDiv (VInt _) (VInt _) = error "tried to do integer division in forceOp"
forceOp OpDiv (VFloat x) (VFloat y) = VFloat (x/y)
forceOp OpSub (VInt x) (VInt y) = VInt (x-y)
forceOp OpSub (VFloat x) (VFloat y) = VFloat (x-y)
forceOp OpOr (VBool x) (VBool y) = VBool (x || y)
forceOp OpGreaterThan (VInt x) (VInt y) = VBool (x > y)
forceOp OpGreaterThan (VFloat x) (VFloat y) = VBool (x > y)
forceOp OpLessThan (VInt x) (VInt y) = VBool (x < y)
forceOp OpLessThan (VFloat x) (VFloat y) = VBool (x < y)
forceOp OpAnd (VBool x) (VBool y) = VBool (x && y)
-- Operations on ANYs should not happen. This is simplifying unreachable code paths, that should be optimized away later
forceOp _ VAny _ = VAny
forceOp _ _ VAny = VAny
forceOp a b c = error $ "Error during forceOp optimizer: " ++ show a ++ " " ++ show b ++ " " ++ show c

forceUnaryOp :: UnaryOperand -> IRValue -> IRValue
forceUnaryOp OpAbs (VFloat x) = VFloat (abs x)
forceUnaryOp OpAbs (VInt x) = VInt (abs x)
forceUnaryOp OpNeg (VFloat x) = VFloat (-x)
forceUnaryOp OpNeg (VInt x) = VInt (-x)
forceUnaryOp OpSign (VFloat x) = VFloat (signum x)
forceUnaryOp OpSign (VInt x) = VInt (signum x)
forceUnaryOp OpNot (VBool x) = VBool (not x)
forceUnaryOp OpExp (VFloat x) = VFloat (exp x)
forceUnaryOp OpLog (VFloat x) = VFloat (log x)
forceUnaryOp _ _ = error "Error during forceUnaryOp optimizer"


--TODO

forceAnyCheck :: IRExpr -> IRExpr
forceAnyCheck x | isValue x = IRConst $ VBool (unval x == VAny || unval x == VList AnyList)
forceAnyCheck (IRCons _ _) = IRConst $ VBool False  -- Lists can never be any
forceAnyCheck (IRTCons _ _) = IRConst $ VBool False -- Tuples can never be any
forceAnyCheck (IRLeft _) = IRConst $ VBool False -- Eithers can never be any
forceAnyCheck (IRRight _) = IRConst $ VBool False -- Eithers can never be any
forceAnyCheck x = IRUnaryOp OpIsAny x
-- Maybe more, I am not quite sure

-- Common-subexpression elimination.
--
-- This is a whole-expression pass (run outside @irMap@): it threads a single
-- counter so every binding it introduces gets a globally-unique name.  Running it
-- per node instead would let the same @cse_N@ name be chosen at two different
-- nesting levels, which shadows and corrupts a binding of a different type.
--
-- A candidate is only hoisted when doing so is provably semantics-preserving,
-- which requires three conditions:
--
--   * pure — it contains no IRSample (see 'annSamples'), so sharing a single
--     value for it cannot collapse distinct random draws;
--   * capture-safe — none of its free variables are bound anywhere inside the
--     node, so lifting it to a let at the top of the node keeps every variable
--     in scope;
--   * unconditionally evaluated — it occurs at least twice in the node's
--     "unconditional skeleton" (positions reached on every evaluation, i.e. not
--     inside an IRIf branch, IREnumSum body, or lambda body).  Because IRLetIn is
--     strict in both the interpreter and generated code, this guarantees the
--     hoisted binding is forced exactly when one of its original occurrences
--     would have been, so no extra evaluation is introduced.
--
-- Cost model: a skeleton is scanned only at "scan roots" (the top expression
-- and each conditional entry point: if-branches, lambda and enum-sum bodies),
-- not at every node.  An interior node's skeleton is a sublist of its scan
-- root's, so it cannot contain a repeat the root scan did not already see —
-- except a candidate the root refused only for capture reasons, whose binder
-- the descent can move below; only such still-repeated candidates warrant a
-- same-region re-scan, and only along child subtrees whose skeleton still
-- repeats one of them ('descendBlocked').  Repeats are counted by structural
-- hash ('annotateIR', verified with exact equality inside each bucket),
-- replacing the pairwise subexpression comparisons that, together with the
-- historical per-node re-scans, made this pass roughly cubic in the length of
-- world-sum spines (see task iroptimizer-superlinear-scaling).
optimizeCommonSubexpr :: IRExpr -> IRExpr
optimizeCommonSubexpr topExpr = evalState (scan (annotateIR topExpr)) 0
  where
    -- Names already present anywhere in the expression (e.g. from a previous
    -- fixed-point iteration); fresh names must avoid these too.
    reserved = allNamesIR topExpr
    fresh :: State Int String
    fresh = do
      i <- get
      put (i + 1)
      let n = "cse_" ++ show i
      if n `Set.member` reserved then fresh else return n
    -- Extract every hoistable repeat of this node's skeleton, then continue
    -- at the scan roots below it.  The annotation is built once for the whole
    -- expression and reused down the walk; only an actual extraction, which
    -- rewrites the node, forces a re-annotation of that subtree.
    scan :: AnnIR -> State Int IRExpr
    scan a = do
      (a', blockedKeys) <- extractHere a
      if Set.null blockedKeys
        then descendToScanRoots a'
        else descendBlocked blockedKeys a'
    descendToScanRoots :: AnnIR -> State Int IRExpr
    descendToScanRoots a = case annExpr a of
      IRIf{}          | [c, t, el] <- annKids a -> IRIf <$> descendToScanRoots c <*> scan t <*> scan el
      IRLambda n _    | [b] <- annKids a -> IRLambda n <$> scan b
      IREnumSum n v _ | [b] <- annKids a -> IREnumSum n v <$> scan b
      e -> do
        kids <- mapM descendToScanRoots (annKids a)
        return (setIRSubExprs e kids)
    -- Like descendToScanRoots, but through a region whose scan left capture-
    -- blocked repeats: a same-region child is re-scanned only if some blocked
    -- candidate still occurs >=2 times in the child's own skeleton (only there
    -- can the descent free it for extraction below its binder); all other
    -- children cannot host a same-region extraction and take the cheap walk.
    descendBlocked :: Set.Set (Int, Int) -> AnnIR -> State Int IRExpr
    descendBlocked keys a = case annExpr a of
      IRIf{}          | [c, t, el] <- annKids a -> IRIf <$> route c <*> scan t <*> scan el
      IRLambda n _    | [b] <- annKids a -> IRLambda n <$> scan b
      IREnumSum n v _ | [b] <- annKids a -> IREnumSum n v <$> scan b
      e -> do
        kids <- mapM route (annKids a)
        return (setIRSubExprs e kids)
      where
        -- once no key repeats in a child's skeleton, none can repeat deeper in
        -- the same region (skeletons only shrink), so the walk needs no
        -- further key counting
        route c | keysRepeatedIn keys c = scan c
                | otherwise = descendToScanRoots c
    extractHere :: AnnIR -> State Int (AnnIR, Set.Set (Int, Int))
    extractHere a = case bestCommonSubexpr a of
      (Nothing, blockedKeys) -> return (a, blockedKeys)
      (Just sub, _) -> do
        name <- fresh
        -- swap the occurrences inside the existing annotation instead of
        -- re-annotating the whole subtree: re-annotation per extraction made
        -- extraction chains quadratic in region size
        let body = annReplace sub (annotateIR (IRVar name)) a
        extractHere (mkAnnIR (IRLetIn name (annExpr sub) (annExpr body)) [sub, body])

-- | True if any of the given (hash, size) keys occurs at least twice in the
-- node's unconditional skeleton.
keysRepeatedIn :: Set.Set (Int, Int) -> AnnIR -> Bool
keysRepeatedIn keys ann = any (>= (2 :: Int)) (Map.elems counts)
  where
    counts = Map.fromListWith (+)
      [ (k, 1) | a <- unconditionalAnns ann
               , let k = (annHash a, annSize a)
               , k `Set.member` keys ]

-- | Subtree annotated with memoized structural facts, so repeats can be
-- counted by hash instead of pairwise tree comparison.
data AnnIR = AnnIR
  { annExpr    :: IRExpr
  , annKids    :: [AnnIR]
  , annHash    :: !Int
  , annSize    :: !Int      -- leaf count
  , annSamples :: !Bool     -- contains a random draw (an IRSample)
    --FIXME: a function call to a sampling function does itself also sample.
  , annBound   :: Set.Set String  -- names bound by binders anywhere in the subtree
  }

annotateIR :: IRExpr -> AnnIR
annotateIR e = mkAnnIR e (map annotateIR (getIRSubExprs e))

-- | Annotate a node whose children are already annotated.
mkAnnIR :: IRExpr -> [AnnIR] -> AnnIR
mkAnnIR e kids = AnnIR e kids h sz smp bnd
  where
    h = foldl' hashMix (headHash e) (map annHash kids)
    sz = if null kids then 1 else sum (map annSize kids)
    smp = case e of
      IRSample _ -> True
      _          -> any annSamples kids
    kidsBound = Set.unions (map annBound kids)
    bnd = case e of
      IRLetIn n _ _   -> Set.insert n kidsBound
      IRLambda n _    -> Set.insert n kidsBound
      IREnumSum n _ _ -> Set.insert n kidsBound
      _               -> kidsBound

-- | Replace every subtree structurally equal to `sub` by `rep`, rebuilding
-- annotations only along changed paths and sharing untouched subtrees.
-- Occurrences cannot nest (a strict subtree is smaller than its host), so a
-- match is not descended into — same result as the historical whole-tree
-- replaceAll with a fresh re-annotation, without its quadratic cost.
annReplace :: AnnIR -> AnnIR -> AnnIR -> AnnIR
annReplace sub rep a0 = maybe a0 id (go a0)
  where
    go a
      | annSize a < annSize sub = Nothing
      | annHash a == annHash sub && annSize a == annSize sub
        && annExpr a == annExpr sub = Just rep
      | otherwise =
          let changes = map go (annKids a)
          in if all (== Nothing) (map (fmap (const ())) changes)
               then Nothing
               else let kids' = zipWith (\old new -> maybe old id new) (annKids a) changes
                    in Just (mkAnnIR (setIRSubExprs (annExpr a) (map annExpr kids')) kids')

hashMix :: Int -> Int -> Int
hashMix a b = (a * 16777619) `xor` b

hashStr :: String -> Int
hashStr = foldl' (\a c -> hashMix a (fromEnum c)) 5381

-- | Hash of a node's constructor and non-child payload.
headHash :: IRExpr -> Int
headHash e = case e of
  IRIf{}            -> 1
  IROp op _ _       -> hashMix 2 (hashStr (show op))
  IRUnaryOp op _    -> hashMix 3 (hashStr (show op))
  IRTheta _ i       -> hashMix 4 i
  IRSubtree _ i     -> hashMix 5 i
  IRConst v         -> hashMix 6 (hashStr (show v))
  IRCons{}          -> 7
  IRElementOf{}     -> 8
  IRTCons{}         -> 9
  IRHead{}          -> 10
  IRTail{}          -> 11
  IRMap{}           -> 12
  IRTFst{}          -> 13
  IRTSnd{}          -> 14
  IRLeft{}          -> 15
  IRRight{}         -> 16
  IRFromLeft{}      -> 17
  IRFromRight{}     -> 18
  IRIsLeft{}        -> 19
  IRIsRight{}       -> 20
  IRDensity d _     -> hashMix 21 (hashStr (show d))
  IRCumulative d _  -> hashMix 22 (hashStr (show d))
  IRSample d        -> hashMix 23 (hashStr (show d))
  IRLetIn n _ _     -> hashMix 24 (hashStr n)
  IRVar n           -> hashMix 25 (hashStr n)
  IRLambda n _      -> hashMix 26 (hashStr n)
  IRApply{}         -> 27
  IREnumSum n v _   -> hashMix (hashMix 28 (hashStr n)) (hashStr (show v))
  IRIsPossible v _  -> hashMix 29 (hashStr (show v))
  IRIndex{}         -> 30
  IRError s         -> hashMix 31 (hashStr s)
  IRConformsTo t _  -> hashMix 32 (hashStr (show t))

-- | The largest hoistable common subexpression of a node (candidates are in
-- first-occurrence order and ties break like the historical
-- @maximumBy . nub@, i.e. towards the last equal maximum), plus the
-- (hash, size) keys of repeated pure candidates that were refused only for
-- capture reasons (and may become extractable further down).
bestCommonSubexpr :: AnnIR -> (Maybe AnnIR, Set.Set (Int, Int))
bestCommonSubexpr ann =
  ( if null candidates then Nothing else Just (maximumBy (comparing annSize) candidates)
  , Set.fromList [ (annHash a, annSize a) | a <- blocked ] )
  where
    skeleton = unconditionalAnns ann
    bound = annBound ann
    repeated = [ a | (a, n) <- tallyAnns skeleton
                   , n >= 2
                   , annSize a > 1
                   , not (annSamples a) ]
    (candidates, blocked) = partition captureSafe repeated
    captureSafe a = not (any (`Set.member` bound) (freeVarsIR (annExpr a)))

-- | Subexpressions reached on every evaluation of the node.  We descend through
-- ordinary nodes but stop at the branches of an IRIf, the body of an IREnumSum,
-- and the body of a lambda, since those are only conditionally, repeatedly, or
-- never evaluated.
unconditionalAnns :: AnnIR -> [AnnIR]
unconditionalAnns a0 = go a0 []
  where
    go a acc = a : case annExpr a of
      IRIf{}      -> case annKids a of { (c:_) -> go c acc; [] -> acc }
      IRLambda{}  -> acc
      IREnumSum{} -> acc
      _           -> foldr go acc (annKids a)

-- | Exact occurrence counts of the distinct subexpressions in the list, in
-- order of first occurrence.  Entries are bucketed by (hash, size) and
-- resolved by exact equality within a bucket, so a hash collision can cost
-- time but never miscount.  (A miscount of 1 as >=2 would extract a
-- single-use binding that optimizeLetIns inlines right back, making the
-- optimizer fixpoint oscillate.)
tallyAnns :: [AnnIR] -> [(AnnIR, Int)]
tallyAnns anns = [ (a, countAt key idx) | (key, idx, a) <- reverse order ]
  where
    (finalCounts, order) = foldl' step (Map.empty, []) anns
    countAt key idx = snd (Map.findWithDefault [] key finalCounts !! idx)
    step (m, ord) a =
      let key = (annHash a, annSize a)
          bucket = Map.findWithDefault [] key m
      in case findIndex ((== annExpr a) . fst) bucket of
           Just i  -> (Map.insert key (bumpAt i bucket) m, ord)
           Nothing -> (Map.insert key (bucket ++ [(annExpr a, 1)]) m, (key, length bucket, a) : ord)
    bumpAt i xs = [ if j == i then (x, n + 1) else (x, n) | (j, (x, n)) <- zip [0 ..] xs ]

-- | Rebuild a node from a fresh list of children (inverse of 'getIRSubExprs').
setIRSubExprs :: IRExpr -> [IRExpr] -> IRExpr
setIRSubExprs (IRIf{}) [a, b, c] = IRIf a b c
setIRSubExprs (IROp op _ _) [a, b] = IROp op a b
setIRSubExprs (IRUnaryOp op _) [a] = IRUnaryOp op a
setIRSubExprs (IRTheta _ i) [a] = IRTheta a i
setIRSubExprs (IRSubtree _ i) [a] = IRSubtree a i
setIRSubExprs (IRCons{}) [a, b] = IRCons a b
setIRSubExprs (IRTCons{}) [a, b] = IRTCons a b
setIRSubExprs (IRHead{}) [a] = IRHead a
setIRSubExprs (IRTail{}) [a] = IRTail a
setIRSubExprs (IRMap{}) [a, b] = IRMap a b
setIRSubExprs (IRElementOf{}) [a, b] = IRElementOf a b
setIRSubExprs (IRTFst{}) [a] = IRTFst a
setIRSubExprs (IRTSnd{}) [a] = IRTSnd a
setIRSubExprs (IRLeft{}) [a] = IRLeft a
setIRSubExprs (IRRight{}) [a] = IRRight a
setIRSubExprs (IRFromLeft{}) [a] = IRFromLeft a
setIRSubExprs (IRFromRight{}) [a] = IRFromRight a
setIRSubExprs (IRIsLeft{}) [a] = IRIsLeft a
setIRSubExprs (IRIsRight{}) [a] = IRIsRight a
setIRSubExprs (IRIsPossible val _) [a] = IRIsPossible val a
setIRSubExprs (IRDensity d _) [a] = IRDensity d a
setIRSubExprs (IRCumulative d _) [a] = IRCumulative d a
setIRSubExprs (IRLetIn n _ _) [a, b] = IRLetIn n a b
setIRSubExprs (IRLambda n _) [a] = IRLambda n a
setIRSubExprs (IRApply{}) [a, b] = IRApply a b
setIRSubExprs (IREnumSum n val _) [a] = IREnumSum n val a
setIRSubExprs (IRIndex{}) [a, b] = IRIndex a b
setIRSubExprs (IRConformsTo t _) [a] = IRConformsTo t a
setIRSubExprs e [] = e  -- leaves: IRConst, IRSample, IRVar, IRError
setIRSubExprs e kids = error ("setIRSubExprs: arity mismatch for " ++ irPrintFlat e ++ " with " ++ show (length kids) ++ " children")

-- | Free variables of an IR expression.
freeVarsIR :: IRExpr -> [String]
freeVarsIR (IRVar v) = [v]
freeVarsIR (IRLetIn n decl body) = freeVarsIR decl ++ filter (/= n) (freeVarsIR body)
freeVarsIR (IRLambda n body) = filter (/= n) (freeVarsIR body)
freeVarsIR (IREnumSum n _ body) = filter (/= n) (freeVarsIR body)
freeVarsIR e = concatMap freeVarsIR (getIRSubExprs e)

-- | Every variable name occurring anywhere in the expression, as a variable
-- occurrence or as a binder — i.e. the union of free and bound variables,
-- computed scope-blind in one pass (the per-binder filtering of 'freeVarsIR'
-- makes free-then-bound quadratic on deep let chains).
allNamesIR :: IRExpr -> Set.Set String
allNamesIR = go Set.empty
  where
    go acc e = case e of
      IRVar n         -> Set.insert n acc
      IRLetIn n _ _   -> foldl' go (Set.insert n acc) (getIRSubExprs e)
      IRLambda n _    -> foldl' go (Set.insert n acc) (getIRSubExprs e)
      IREnumSum n _ _ -> foldl' go (Set.insert n acc) (getIRSubExprs e)
      _               -> foldl' go acc (getIRSubExprs e)

-- | Replace an application of a lambda to a non-value argument by a let binding:
-- @(\x -> body) arg@ becomes @let x = arg in body@.  This is the capture-safe
-- form of lambda elimination; 'applyConstant' handles constant arguments by
-- inlining them directly, and 'optimizeLetIns' cleans up the resulting binding.
applyToLetIn :: IRExpr -> IRExpr
applyToLetIn (IRApply (IRLambda varname inExpr) v) | not (isValue v) = IRLetIn varname v inExpr
applyToLetIn x = x

pruneAnyCkecksExpr :: IRExpr -> IRExpr
pruneAnyCkecksExpr (IRUnaryOp OpIsAny _) = IRConst $ VBool False
pruneAnyCkecksExpr x = x

