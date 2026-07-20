module SPLL.IROptimizer (
  optimizeEnv
, failConversion
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.Functor ( (<&>) )
import Data.Number.Erf (erf)
import Data.List (maximumBy)
import Data.Ord (comparing)
import Data.Foldable (toList)
import Control.Monad.State (State, evalState, get, put)
import qualified Data.Map.Strict as Map
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

exprSize :: IRExpr -> Int
exprSize expr | null (getIRSubExprs expr) = 1
exprSize expr = sum (map exprSize (getIRSubExprs expr))

-- | True if the expression contains a random draw.  Sharing such an expression
-- via CSE would collapse independent draws into one, so they are never extracted.
--FIXME: a function call to a sampling function does itself also sample.
samples :: IRExpr -> Bool
samples (IRSample _) = True
samples x = any samples (getIRSubExprs x)

-- Common-subexpression elimination.
--
-- This is a whole-expression pass (run outside @irMap@): it threads a single
-- counter so every binding it introduces gets a globally-unique name.  Running it
-- per node instead would let the same @cse_N@ name be chosen at two different
-- nesting levels, which shadows and corrupts a binding of a different type.
--
-- At each node we extract repeated subexpressions one at a time, wrapping the
-- node in an IRLetIn, then recurse into the children of the result.  A candidate
-- is only hoisted when doing so is provably semantics-preserving, which requires
-- three conditions:
--
--   * pure — it contains no IRSample (see 'samples'), so sharing a single value
--     for it cannot collapse distinct random draws;
--   * capture-safe — none of its free variables are bound anywhere inside the
--     node, so lifting it to a let at the top of the node keeps every variable
--     in scope;
--   * unconditionally evaluated — it occurs at least twice in the node's
--     "unconditional skeleton" (positions reached on every evaluation, i.e. not
--     inside an IRIf branch, IREnumSum body, or lambda body).  Because IRLetIn is
--     strict in both the interpreter and generated code, this guarantees the
--     hoisted binding is forced exactly when one of its original occurrences
--     would have been, so no extra evaluation is introduced.
optimizeCommonSubexpr :: IRExpr -> IRExpr
optimizeCommonSubexpr topExpr = evalState (cseWalk topExpr) 0
  where
    -- Names already present anywhere in the expression (e.g. from a previous
    -- fixed-point iteration); fresh names must avoid these too.
    reserved = freeVarsIR topExpr ++ boundVarsIR topExpr
    fresh :: State Int String
    fresh = do
      i <- get
      put (i + 1)
      let n = "cse_" ++ show i
      if n `elem` reserved then fresh else return n
    -- | Fully resolve a node's own unconditional region (via 'extractHere'),
    -- then descend -- WITHOUT re-scanning the parts of that same region again
    -- (see 'descendRegion').
    cseWalk :: IRExpr -> State Int IRExpr
    cseWalk e = extractHere e >>= descendRegion
    -- | Descend through a node whose enclosing unconditional region has
    -- already been fully scanned by an ancestor's 'extractHere' call. Since
    -- 'unconditionalSubexprs' descends transparently through every
    -- constructor except IRIf's branches, IRLambda's body and IREnumSum's
    -- body, any subexpression reachable through those transparent
    -- constructors was already a member of the ancestor's skeleton -- so any
    -- duplicate within it was already found and hoisted from there.
    -- Re-running 'extractHere' on every one of those transparent descendants
    -- (the original per-node 'cseWalk' recursion) is therefore pure
    -- redundant work: for a long transparent chain of length k (e.g. the
    -- k-way IROp sum built by 'measurePlanWorlds' for a plan-enumeration
    -- program) it turned a single O(k) region scan into an O(k^2) one, since
    -- every position along the chain re-scanned the entire remaining
    -- suffix. 'descendRegion' instead only calls 'extractHere' again once it
    -- reaches an actual region boundary, matching 'unconditionalSubexprs'
    -- exactly so no candidate is missed and none is scanned twice.
    descendRegion :: IRExpr -> State Int IRExpr
    descendRegion e = case e of
      IRIf c t f -> do
        c' <- descendRegion c
        t' <- cseWalk t
        f' <- cseWalk f
        return (IRIf c' t' f')
      IRLambda n body -> IRLambda n <$> cseWalk body
      IREnumSum n val body -> IREnumSum n val <$> cseWalk body
      _ -> do
        kids <- mapM descendRegion (getIRSubExprs e)
        return (setIRSubExprs e kids)
    extractHere :: IRExpr -> State Int IRExpr
    extractHere e = case bestCommonSubexpr e of
      Nothing  -> return e
      Just sub -> do
        name <- fresh
        extractHere (IRLetIn name sub (replaceAll sub (IRVar name) e))

-- | The largest hoistable common subexpression of a node, if any.
--
-- Candidate detection is grouped by 'show' key in a Map rather than the
-- naive O(m^2) "nub + count via filter (==s) skeleton" (m = skeleton size):
-- on the large IR trees plan-guided enumeration and set-witness compilation
-- can produce, the pairwise-equality version dominated total compile time
-- (each '==' on a subtree is itself O(subtree size), so the nub/filter scan
-- was effectively O(m^2 * avg subtree size)). Grouping by a 'show'-derived
-- key is O(m log m * avg subtree size) -- one string-render and Map
-- insertion per skeleton element instead of a full pairwise scan.
bestCommonSubexpr :: IRExpr -> Maybe IRExpr
bestCommonSubexpr expr
  | Map.null repeated = Nothing
  | otherwise = Just (maximumBy (comparing exprSize) (Map.elems repeated))
  where
    skeleton = unconditionalSubexprs expr
    bound = boundVarsIR expr
    eligible = [ s | s <- skeleton
                    , exprSize s > 1
                    , not (samples s)
                    , not (any (`elem` bound) (freeVarsIR s)) ]
    counts = Map.fromListWith (+) [ (show s, 1 :: Int) | s <- eligible ]
    firstOccurrence = Map.fromListWith (\_ old -> old) [ (show s, s) | s <- eligible ]
    repeated = Map.intersectionWith const firstOccurrence (Map.filter (>= 2) counts)

-- | Subexpressions reached on every evaluation of the node.  We descend through
-- ordinary nodes but stop at the branches of an IRIf, the body of an IREnumSum,
-- and the body of a lambda, since those are only conditionally, repeatedly, or
-- never evaluated.
unconditionalSubexprs :: IRExpr -> [IRExpr]
unconditionalSubexprs e = e : case e of
  IRIf cond _ _ -> unconditionalSubexprs cond
  IRLambda _ _  -> []
  IREnumSum{}   -> []
  _             -> concatMap unconditionalSubexprs (getIRSubExprs e)

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

-- | Every variable name bound by some binder anywhere in the expression.
boundVarsIR :: IRExpr -> [String]
boundVarsIR (IRLetIn n decl body) = n : (boundVarsIR decl ++ boundVarsIR body)
boundVarsIR (IRLambda n body) = n : boundVarsIR body
boundVarsIR (IREnumSum n _ body) = n : boundVarsIR body
boundVarsIR e = concatMap boundVarsIR (getIRSubExprs e)

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

