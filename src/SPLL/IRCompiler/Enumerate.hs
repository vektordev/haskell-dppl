-- | Enumerated inference: enumerated bindings, draw stacks, constraint nets,
-- agreement fusion, enumerated sums and 'toIREnumerate'.
module SPLL.IRCompiler.Enumerate (
  enumerateAppliedLambda,
  drawStack,
  factoredDrawStack,
  constraintNet,
  compileConstraintNet,
  latentCellBinders,
  latentCellSum,
  curriedEnumerableCallee,
  leadingEnumerableArgument,
  enumerateCurriedArgument,
  agreementShape,
  enumerateAgreement,
  randomDrawSites
) where

import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Analysis (isEnumerable, headIsConditional)
import SPLL.Typing.PType
import Data.Maybe
import Data.List ((\\), find, elemIndex, nub, intercalate, sort, partition)
import SPLL.Typing.ForwardChaining
import SPLL.Semiring
import Control.Monad (foldM, forM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph (stronglyConnComp, flattenSCC)
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Materialize

-- | Enumerate the application of a conditional/enumerable lambda to a discrete
-- argument. Computes sum over the argument's discrete support of
-- P(arg = value) * P_enum(body | bound = value). Shared by the top-level inference
-- rule and by toIREnumerate, so that nested enumerable `let`s
-- (`let c = .. in let d = .. in ..`) enumerate at every level instead of generating
-- the inner draws forward.
enumerateAppliedLambda :: CompilerMetadata -> Bool -> Expr -> Expr -> IRExpr -> CompilerMonad PResult
enumerateAppliedLambda meta cumulative l v sample =
  enumerateBinding meta l v Nothing (\bodyMeta lBodyExpr -> toIREnumerate bodyMeta cumulative lBodyExpr sample)

-- | 'enumerateAppliedLambda' with the body's compilation handed in: the sum
-- over the argument's support of P(arg = value) times what @body@ returns,
-- given the meta with the bound variable fixed and the lambda's body (renamed
-- if its parameter clashed with a variable the argument reads).
-- 'factoredDrawStack' passes a body of its own, the operands of one
-- independent component, and may pass the argument's measure already
-- tabulated ('drawMeasureTable').
enumerateBinding :: CompilerMetadata -> Expr -> Expr -> Maybe MarginalTable
                 -> (CompilerMetadata -> Expr -> CompilerMonad PResult) -> CompilerMonad PResult
enumerateBinding meta l v preTable compileBody = do
  let lCn = chainName (getTypeInfo l)
  let (_, paramVar, bodyCn, _) = equivalentLambda "enumerateAppliedLambda" (fcData meta) lCn
  let fExprs = map snd (functions (compilingProgram meta))
  -- The loop binds the lambda's parameter around both the body and the
  -- argument's own measure, so an argument mentioning a variable of the same
  -- name -- @h b = ..@ called as @h b@ from inside an enclosing @draw b@ --
  -- would read the loop variable instead: its measure became @b == b@, always
  -- true, and the draw's weight vanished from the sum. Such a parameter is
  -- renamed to a fresh name first (task
  -- rewrite-invariance-net-draw-apply-helper-alias). A name the argument
  -- binds clashes as well: the measure is compiled at the loop variable, so a
  -- binder of the same name inside the argument (@observe .. (\m -> m > 0)@
  -- passed to @f m = ..@) shadows it, and the measure compared the argument's
  -- own value with itself (task callee-body-name-sensitive-across-call).
  (boundVar, lBodyExpr) <-
    if paramVar `Set.member` allNamesExpr v
      then do
        fresh <- mkVariable paramVar
        return (fresh, renameFreeVar paramVar fresh (findExprWithCN fExprs bodyCn))
      else return (paramVar, findExprWithCN fExprs bodyCn)
  let newTypeEnv = (boundVar, (rType (getTypeInfo v), False)):typeEnv meta
  let discreteVVals = head [x | DiscreteValues x <- tags (getTypeInfo v)]
  -- Inside an enclosing enumeration, the argument's measure is tabulated once
  -- per domain value ahead of this loop rather than recomputed in it (task
  -- split-read-field-leaf-rebuilt-per-world). The cells depend on this loop's
  -- variable only through the constant key each is compiled at, so they land
  -- in the enclosing scope, and every enclosing loop whose variable they do
  -- not read hoists them out in turn ('hoistInvariantBindings'). A field read
  -- of a split neural record at enumeration depth @k@ is then measured @2k@
  -- times instead of @2^(k+1) - 2@. At the outermost loop the table would
  -- only rearrange the same @|domain|@ measures, so it is not built there.
  -- Under --batched, 'SPLL.IRLeafTablePass' tabulates a nested neural leaf
  -- after optimization instead, as one gathered table ('nestedDrawTables').
  table <- case preTable of
    Just t -> return (Just t)
    Nothing
      | not (nestedDrawTables meta) -> return Nothing
      | otherwise -> drawMeasureTable meta v
  irTuple <- scoped (do
    pBranch <- case table of
      Just tbl -> return (lookupMarginal meta tbl (IRVar boundVar))
      Nothing  -> (unP . rProb) <$> toIRInference meta False (drawMeasured meta v) (IRVar boundVar)
    -- Inside the loop the bound variable holds one fixed domain value, so it is
    -- recorded as recovered, exactly as 'residueFactor' records a variable fixed
    -- at its witness. Only a body that leaves the enumeration for 'toIRInference'
    -- reads this (the over-budget nested application in 'toIREnumerate'); there
    -- the plan traversal must see the loop variable as fixed, not as an enclosing
    -- random binding shared across factors ('planFactorExternals').
    let bodyMeta = recoverVars [boundVar] meta{ typeEnv=newTypeEnv
                       , fixedLatents = Set.insert (chainName (getTypeInfo v)) (fixedLatents meta)
                       , dimAwareEnum = keepsDims }
    bodyRes <- compileBody bodyMeta lBodyExpr
    return (pBranch, bodyRes))
  enumSumTerms meta dimBound boundVar discreteVVals irTuple
  where
    (keepsDims, dimBound) = enumSumDims meta (rType (getTypeInfo l))

-- | A draw's argument as 'enumerateBinding' measures it: with the enclosing
-- enumerated latents fixed. Inside their loops each holds one value, and a
-- curried helper call such as @contrib u 1@ (u enumerated outside) is only
-- measurable as a call with deterministic arguments once @u@ reads as one.
drawMeasured :: CompilerMetadata -> Expr -> Expr
drawMeasured meta v = reinferRecovered meta (recoveredVars meta) v

-- | Whether 'enumerateBinding' tabulates a draw's measure ahead of its loop:
-- inside an enclosing enumeration, and not under --batched. Nor inside a
-- materialized-marginal leaf ('inTabulatedLeaf'): the leaf's size gates
-- whether its table is built, and the tables here are what --batched leaves
-- out, so with them the two backends would materialize different operands
-- and prune differently under topK (task
-- batched-topk-noisy-if-fold-of-reads-disagrees).
nestedDrawTables :: CompilerMetadata -> Bool
nestedDrawTables meta = not (Set.null (fixedLatents meta)) && not (batched (compilerConfig meta))
                        && not (inTabulatedLeaf meta)

-- | The measure of a draw's argument at each value of its domain, one
-- let-bound cell per value, bound in the current scope ('pointQueryTable',
-- which declines a domain or a measure too large to unroll).
drawMeasureTable :: CompilerMetadata -> Expr -> CompilerMonad (Maybe MarginalTable)
drawMeasureTable meta v =
  pointQueryTable meta (drawMeasured meta v)
    (multiValueToValueList (head [x | DiscreteValues x <- tags (getTypeInfo v)]))

-- | A stack of enumerable @draw@s directly over a field constructor, with its
-- operands split into the groups that share nothing random (task
-- answer-record-shared-fields-enumerated-jointly).
--
-- > draw a1 = .. in draw b1 = .. in draw a2 = .. in draw b2 = .. in
-- > Ans a1 b1 (a1 && b1) a2 b2 (a2 && b2)
--
-- is what 'SPLL.DrawSinking' leaves of a record of answers over one split
-- neural read: @a1@ is read by two operands, so it cannot sink into either,
-- and the stack enumerates every field jointly, @2^(2N)@ worlds at @N@ groups.
-- Given the scope the stack sits in, a draw is an independent sample of the
-- variables its value reads, and a constructor's probability is the product
-- of its fields' ('isFieldConstructor'). So operands that share no draw,
-- transitively through the draws' own values, and no random enclosing local,
-- are independent, and the probability is the product over the groups of
-- each group's own sum over its own draws: @N * 4@ worlds here.
--
-- A group is a component of the graph linking an operand to each stack draw
-- it reads, a draw to each earlier draw its value reads, and anything that
-- reads a random enclosing local to every other reader of it. A local counts
-- as random unless an enclosing enumeration or witness fixed it
-- ('recoveredVars') or every occurrence of it is typed 'Deterministic' (a
-- query argument, @img@ above). Taken only when that yields two groups or
-- more, and declined when a draw is read by no operand at all: such a draw is
-- a factor of its own, which this would have to prove sums to one.
data DrawStack = DrawStack
  { dsBinds :: [(Expr, Expr)]
    -- ^ each draw's lambda and value, outermost first
  , dsCtor  :: (RType, String, [Expr])
    -- ^ the constructor's type, name and operands
  , dsComps :: [([Int], [Int])]
    -- ^ per group, its draws (indices into 'dsBinds', in stack order) and its
    -- operands (indices into the constructor's operands)
  }

drawStack :: CompilerMetadata -> Expr -> Maybe DrawStack
drawStack meta e0 = do
  (binds, (rt, c, ops)) <- peel e0
  if null binds then Nothing else Just ()
  let k = length binds
      stackVars = Set.fromList [ x | (Expr _ (Lambda x _), _) <- binds ]
      bindReads = [ freeVarsExpr v | (_, v) <- binds ]
      opReads = map freeVarsExpr ops
      nodeExprs = map snd binds ++ ops
      nodeReads = bindReads ++ opReads
      linkingOuter i = Set.toList (Set.filter isRandomLocal (randomReads (nodeExprs !! i)
                                     `Set.intersection` (nodeReads !! i)))
      isRandomLocal u = not (u `Set.member` stackVars) && u `notElem` recoveredVars meta
                        && case lookup u (typeEnv meta) of
                             Just (t, False) -> not (isTArrowType t)
                             _ -> False
      bindIdx = Map.fromList [ (x, j) | (j, (Expr _ (Lambda x _), _)) <- zip [0 :: Int ..] binds ]
      outerNames = nub (concatMap linkingOuter [0 .. length nodeExprs - 1])
      outerIdx u = length nodeExprs + fromJust (elemIndex u outerNames)
      edges i = [ j | x <- Set.toList (nodeReads !! i), Just j <- [Map.lookup x bindIdx] ]
                ++ map outerIdx (linkingOuter i)
      directed = [ (i, j) | i <- [0 .. length nodeExprs - 1], j <- edges i ]
      undirected = directed ++ [ (j, i) | (i, j) <- directed ]
      allNodes = [0 .. length nodeExprs + length outerNames - 1]
      graph = [ (n, n, [ j | (i, j) <- undirected, i == n ]) | n <- allNodes ]
      comps = [ (sort [ n | n <- ns, n < k ], sort [ n - k | n <- ns, n >= k, n < k + length ops ])
              | scc <- stronglyConnComp graph, let ns = flattenSCC scc ]
      groups = filter (\(bs, os) -> not (null bs && null os)) comps
  if length (filter (not . null . snd) groups) < 2 then Nothing else Just ()
  if any (null . snd) groups then Nothing else Just ()
  return (DrawStack binds (rt, c, ops) groups)
  where
    peel (Expr _ (Apply l@(Expr _ (Lambda x b)) v))
      | isEnumerableApplication meta l v
      , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
      , calleeBodyInScope meta l
      , isNothing (agreementShape meta l v)
      , not (x `Set.member` freeVarsExpr v)
      , not (isRecoveredVar v) = do
          (rest, ctor) <- peel b
          return ((l, v) : rest, ctor)
    peel (Expr ti (InjF (Named c) ops))
      | isFieldConstructor (adtDecls meta) c = Just ([], (rType ti, c, ops))
    peel _ = Nothing
    isRecoveredVar (Expr _ (Var x)) = x `elem` recoveredVars meta
    isRecoveredVar _ = False
    randomReads ex = Set.fromList [ n | Expr ti (Var n) <- subtreesOf ex, pType ti /= Deterministic ]
    subtreesOf ex = ex : concatMap subtreesOf (getSubExprs ex)

-- | The probability of a 'DrawStack': the product over its groups of each
-- group's sum over its own draws, nested in stack order with
-- 'enumerateBinding' exactly as 'enumerateAppliedLambda' nests them, of the
-- product of its operands' fields. Inside the loops an operand is compiled as
-- 'toIREnumerate' compiles the whole constructor (forward and compare, or
-- handed to inference where it draws fresh randomness); a group without draws
-- is plain inference, as in the field-constructor rule.
factoredDrawStack :: CompilerMetadata -> Bool -> DrawStack -> IRExpr -> CompilerMonad PResult
factoredDrawStack meta cumulative ds sample = do
  let (rt, c, ops) = dsCtor ds
      resolvedName = resolveInjF rt c
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let outV = soleOutputVar fwd
      inlineSample = irMap (\e -> case e of IRVar n | n == outV -> sample; _ -> e)
      fields = [ (inlineSample invBody, inlineSample appT, decons)
               | inV <- inputVars fwd
               , let FDecl {body=invBody, applicability=appT, deconstructing=decons} = inversionFor resolvedName inV inversions ]
  -- The conjunction of the fields' applicability tests guards every group and
  -- the product, so it is bound once rather than copied into each.
  applicable <- case foldr1 (IROp OpAnd) [ a | (_, a, _) <- fields ] of
    c'@(IRConst _) -> return c'
    conj -> do
      v <- mkVariable "applicable"
      setVariables [(v, conj)]
      return (IRVar v)
  -- Nested in an enclosing enumeration, a draw whose value reads no other
  -- draw of the stack is tabulated here, outside the guard below: inside it
  -- the cells could not leave the guarded block, which reads the enclosing
  -- loop's variable, and would be rebuilt at every enclosing world (task
  -- split-read-field-leaf-rebuilt-per-world). Out here the enclosing loops
  -- hoist them as they hoist any invariant binding. The cells read no part of
  -- the sample, which is all the guard protects.
  let stackVars = Set.fromList [ x | (Expr _ (Lambda x _), _) <- dsBinds ds ]
  tables <- if not (nestedDrawTables meta) then return [] else
    fmap catMaybes $ forM (zip [0 :: Int ..] (dsBinds ds)) $ \(j, (_, v)) ->
      if Set.null (freeVarsExpr v `Set.intersection` stackVars)
        then fmap (\t -> (j, t)) <$> drawMeasureTable meta v
        else return Nothing
  groupRes <- forM (dsComps ds) $ \(bis, ois) ->
    guardedSubInference meta [applicable]
      (group meta [ (dsBinds ds !! j, lookup j tables) | j <- bis ] [ (ops !! i, fields !! i) | i <- ois ])
  return (guardP sr [applicable] (foldl1 (prodP sr) groupRes))
  where
    sr = semiringOf meta
    group m [] opFs = productOf <$> mapM (\(op, (fs, _, decons)) ->
                        (if decons then toIRInferenceSave else toIRInference) m cumulative op fs) opFs
    group m binds opFs = inLoops m binds opFs
    inLoops m [] opFs = productOf <$> mapM (\(op, (fs, _, _)) -> leaf m op fs) opFs
    inLoops m (((l, v), tbl) : rest) opFs = enumerateBinding m l v tbl (\bm _ -> inLoops bm rest opFs)
    -- An ANY field matches anything, which the whole-constructor comparison
    -- this replaces got from comparing ADT values; the operand's own term is
    -- compiled only for a field that is not ANY.
    leaf m op fs = do
      let anyField = IRUnaryOp OpIsAny fs
      res <- guardedSubInference m [notIR anyField] (operandTerm m op fs)
      return (zipResult (IRIf anyField) (detP (srOne sr)) res)
    -- A bare draw: compare its value to the field.
    operandTerm m op@(Expr _ (Var _)) fs = do
      opIR <- toIRGenerate m op
      let rt = rType (getTypeInfo op)
      forwardOrInfer m cumulative op fs [("operand", op, opIR)] $ return $
        if cumulative
          then mass (compareValueExpr sr rt opIR fs)
          else indicatorP sr (leafEqIR rt fs opIR)
    operandTerm m op fs = toIREnumerate m cumulative op fs
    productOf = foldl1 (prodP sr)


-- | A conjunction of Boolean clauses over enumerable draws, compiled by
-- variable elimination (task grid-constraint-network-enumerated-jointly).
--
-- > draw x1 = readD a in .. draw x9 = readD i in
-- > diff3 x1 x2 x3 && diff3 x4 x5 x6 && .. && diff3 x3 x6 x9
--
-- Every draw sits in two clauses (a row and a column), so after
-- 'SPLL.DrawSinking' most of them still sit above the whole conjunction, and
-- the nested enumeration walks close to the joint of all nine reads: @10^9@
-- terms per call, more than ten minutes. The probability that the conjunction
-- holds is a sum over the draws of a product of factors, one per draw (its
-- measure) and one indicator per clause, which variable elimination sums one
-- draw at a time: summing out a draw multiplies the factors that mention it
-- into a table over the draws they also mention ('eliminationOrder' picks the
-- draw whose table is smallest). The tables are nested rank-1 tensors indexed
-- by domain position ('BIota'), built at run time, so the code stays linear in
-- the program and the cost is the sum of the table sizes times the eliminated
-- domain.
--
-- The shape is a tree of @&&@ whose inner nodes may carry draws (where
-- sinking left them) and whose leaves are the clauses. It is sound to hoist
-- every draw to the top: each is still one sample covering every use of its
-- name, which the checks below make unique and not captured; and a draw's
-- measure is a factor of the joint whether or not the clause that reads it is
-- evaluated. The leaves must be deterministic given the draws (re-inferred
-- with the draws pinned), and no draw may read another draw or a random
-- enclosing local, so the draws are independent and their factors unary.
--
-- @P(False)@ is the total measure (the product of the draws' own totals)
-- minus @P(True)@, a subtraction on exact sums, which is why the rule is
-- declined under topK (and under branch counting, whose counts it does not
-- reproduce) and under a semiring that has no subtraction (max-product). It is
-- taken only where it pays: the clause hypergraph has a cycle (an acyclic
-- network is what sinking already factorises) and the elimination costs less
-- than a quarter of the joint enumeration.
data ConstraintNet = ConstraintNet
  { cnDraws   :: [(String, Expr)]
    -- ^ each draw's binder and value, in the order the walk met them
  , cnClauses :: [(Expr, [Int])]
    -- ^ each clause and the draws it reads (indices into 'cnDraws')
  , cnOrder   :: [Int]
    -- ^ the elimination order
  }

constraintNet :: CompilerMetadata -> Expr -> Maybe ConstraintNet
constraintNet meta e0 = do
  let conf = compilerConfig meta
      sr = semiringOf meta
  need (not (countBranches conf) && isNothing (topKThreshold conf))
  need (srReduceOp sr `elem` [ROpAdd, ROpLogSumExp])
  need (rType (getTypeInfo e0) == TBool && rootShape e0)
  (draws, leaves) <- collect e0
  let names = map fst draws
      nameSet = Set.fromList names
      domains = [ take 1 [ mv | DiscreteValues mv <- tags (getTypeInfo v) ] | (_, v) <- draws ]
  need (length draws >= 2 && Set.size nameSet == length names)
  need (Set.null (nameSet `Set.intersection` freeVarsExpr e0))
  need (all ((== 1) . length) domains)
  need (all (Set.null . Set.intersection nameSet . freeVarsExpr . snd) draws)
  let sizes = [ length (multiValueToValueList mv) | [mv] <- domains ]
      idx = Map.fromList (zip names [0 :: Int ..])
      clauses = [ (c, sort [ j | x <- Set.toList (freeVarsExpr c), Just j <- [Map.lookup x idx] ]) | c <- leaves ]
  need (all ((== TBool) . rType . getTypeInfo) leaves)
  -- a pruned observation's hole is a unit factor, not a value to compare
  need (null [ () | Expr _ (Constant VAny) <- concatMap subtreesOf leaves ])
  need (cyclicIncidence (length draws) (map snd clauses))
  let (order, veCost) = eliminationOrder sizes (map snd clauses)
  need (4 * veCost < product (map toInteger sizes))
  -- The semantic checks last: they re-run modality inference.
  need (not (any (readsRandomLocal nameSet) (map snd draws ++ leaves)))
  let pins = names ++ recoveredVars meta
  need (all (\c -> pType (getTypeInfo (reinferRecovered meta pins c)) == Deterministic) leaves)
  return (ConstraintNet draws clauses order)
  where
    need b = if b then Just () else Nothing
    rootShape (Expr _ (Apply (Expr _ (Lambda _ _)) _)) = True
    rootShape (Expr _ (InjF (Named "and") [_, _])) = True
    rootShape _ = False
    collect (Expr _ (Apply l@(Expr _ (Lambda x b)) v))
      | isDraw l v = do
          (ds, cs) <- collect b
          return ((x, v) : ds, cs)
    collect (Expr _ (InjF (Named "and") [p, q])) = do
      (d1, c1) <- collect p
      (d2, c2) <- collect q
      return (d1 ++ d2, c1 ++ c2)
    collect leaf = Just ([], [leaf])
    -- The lambda is literal, and its body is walked here rather than
    -- resolved through chain names, so 'calleeBodyInScope' does not apply
    -- (it would see the names the enclosing draws of the net bind as unbound).
    isDraw l v = pType (getTypeInfo v) /= Deterministic
      && isEnumerableApplication meta l v
      && enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
      && isNothing (agreementShape meta l v)
    -- as in 'drawStack': a local neither fixed by an enclosing engine nor
    -- typed 'Deterministic' at every occurrence couples what reads it
    readsRandomLocal netVars ex = any (isRandomLocal netVars) (Set.toList (randomReads ex))
    isRandomLocal netVars u = not (u `Set.member` netVars) && u `notElem` recoveredVars meta
      && case lookup u (typeEnv meta) of
           Just (t, False) -> not (isTArrowType t)
           _ -> False
    randomReads ex = Set.fromList [ n | Expr ti (Var n) <- subtreesOf ex, pType ti /= Deterministic ]
    subtreesOf ex = ex : concatMap subtreesOf (getSubExprs ex)

-- | Whether the incidence graph of @n@ variables and the clauses over them
-- (each a list of variables) has a cycle: more edges than a forest on its
-- nodes could hold.
cyclicIncidence :: Int -> [[Int]] -> Bool
cyclicIncidence n scopes0 =
  let scopes = filter (not . null) scopes0
      nodes = n + length scopes
      edges = [ (n + c, v) | (c, s) <- zip [0 ..] scopes, v <- s ]
      adj = Map.fromListWith (++) (concat [ [(a, [b]), (b, [a])] | (a, b) <- edges ])
      graph = [ (u, u, Map.findWithDefault [] u adj) | u <- [0 .. nodes - 1] ]
      comps = length (stronglyConnComp graph)
  in length edges > nodes - comps

-- | A greedy elimination order for variables of the given domain sizes under
-- factors over the given scopes (one unary factor per variable is implied),
-- and its cost: the sum, over the eliminations, of the size of the table
-- built times the eliminated domain. Each step eliminates the variable whose
-- factors span the fewest assignments.
eliminationOrder :: [Int] -> [[Int]] -> ([Int], Integer)
eliminationOrder sizes scopes0 =
  go (Set.fromList [0 .. n - 1]) (map Set.fromList (filter (not . null) scopes0)) [] 0
  where
    n = length sizes
    sz v = toInteger (sizes !! v)
    span' fs v = Set.insert v (Set.unions [ s | s <- fs, v `Set.member` s ])
    weight fs v = product (map sz (Set.toList (span' fs v)))
    go remaining fs acc cost
      | Set.null remaining = (reverse acc, cost)
      | otherwise =
          let v = snd (minimum [ (weight fs u, u) | u <- Set.toList remaining ])
              (touch, rest) = partition (Set.member v) fs
              merged = Set.delete v (Set.unions touch)
              fs' = if Set.null merged then rest else merged : rest
          in go (Set.delete v remaining) fs' (v : acc) (cost + weight fs v)

-- | A factor of a 'ConstraintNet' during elimination.
data NetFactor
  = NFUnary Int            -- ^ a draw's measure, indexed by its position
  | NFClause IRExpr [Int]  -- ^ a clause, reading the draws by name
  | NFTable Varname [Int]  -- ^ a table built by an elimination, nested in scope order

netFactorScope :: NetFactor -> [Int]
netFactorScope (NFUnary k) = [k]
netFactorScope (NFClause _ s) = s
netFactorScope (NFTable _ s) = s

-- | The probability of a 'ConstraintNet' by variable elimination; see
-- 'ConstraintNet'. Every table is let-bound in the current scope, ahead of
-- the result, which reads the sample only at its root.
compileConstraintNet :: CompilerMetadata -> ConstraintNet -> IRExpr -> CompilerMonad PResult
compileConstraintNet meta net sample = do
  let draws = cnDraws net
      doms = [ head [ mv | DiscreteValues mv <- tags (getTypeInfo v) ] | (_, v) <- draws ]
      sizes = map (length . multiValueToValueList) doms
      reduceSum t = IRBuiltin (BReduce (srReduceOp sr) 0) [t]
      iota k = IRBuiltin (BIota [EFixed (sizes !! k)]) []
  domVars <- forM draws (const (mkVariable "net_dom"))
  setVariables (zip domVars (map tensorDomainSR doms))
  unaryVars <- forM (zip draws doms) $ \((_, v), mv) -> do
    xv <- mkVariable "net_val"
    o <- scoped (unP . rProb <$> toIRInference meta False (drawMeasured meta v) (IRVar xv))
    u <- mkVariable "net_unary"
    setVariables [(u, IRBuiltin BMap [IRLambda xv (closeExpr o id), tensorDomainSR mv])]
    return u
  let metaC = recoverVars (map fst draws) meta { typeEnv = [ (x, (rType (getTypeInfo v), False)) | (x, v) <- draws ] ++ typeEnv meta }
  clauseIRs <- mapM (toIRGenerate metaC . fst) (cnClauses net)
  let eliminate fs k = do
        let (touch, rest) = partition (elem k . netFactorScope) fs
            newScope = sort (nub (concatMap netFactorScope touch)) \\ [k]
        ivs <- Map.fromList <$> forM (k : newScope) (\v -> (,) v <$> mkVariable "net_i")
        let ix v = IRVar (ivs Map.! v)
            weightOf (NFUnary j) = Just (IRBuiltin (BIndex 0) [IRVar (unaryVars !! j), ix j])
            weightOf (NFTable t s) = Just (foldl (\acc v -> IRBuiltin (BIndex 0) [acc, ix v]) (IRVar t) s)
            weightOf NFClause{} = Nothing
            conds = [ c | NFClause c _ <- touch ]
            prod = foldl1 (srTimes sr) (mapMaybe weightOf touch)
            guarded = if null conds then prod else IRIf (foldr1 andIR conds) prod (srZero sr)
            -- the clauses read the draws by name: bound from the indices
            readVars = nub (concat [ s | NFClause _ s <- touch ])
            summand = foldr (\v acc -> IRLetIn (fst (draws !! v)) (IRBuiltin (BIndex 0) [IRVar (domVars !! v), ix v]) acc)
                            guarded readVars
            inner = reduceSum (IRBuiltin BMap [IRLambda (ivs Map.! k) summand, iota k])
            table = foldr (\v acc -> IRBuiltin BMap [IRLambda (ivs Map.! v) acc, iota v]) inner newScope
        t <- mkVariable "net_table"
        setVariables [(t, table)]
        return (NFTable t newScope : rest)
  final <- foldM eliminate ([ NFUnary k | k <- [0 .. length draws - 1] ]
                            ++ [ NFClause c s | (c, (_, s)) <- zip clauseIRs (cnClauses net) ])
                   (cnOrder net)
  let constConds = [ c | NFClause c [] <- final ]
      scalars = [ IRVar t | NFTable t [] <- final ]
      holds = foldl1 (srTimes sr) scalars
      truth = if null constConds then holds else IRIf (foldr1 andIR constConds) holds (srZero sr)
  tVar <- mkVariable "net_true"
  zVar <- mkVariable "net_total"
  setVariables [ (tVar, truth)
               , (zVar, foldl1 (srTimes sr) [ reduceSum (IRVar u) | u <- unaryVars ]) ]
  opaqueMass sr (IRIf (IRUnaryOp OpIsAny sample) (IRVar zVar)
                   (IRIf sample (IRVar tVar) (measureDiffSR sr (IRVar zVar) (IRVar tVar))))
             const0
  where
    sr = semiringOf meta

-- | The enumerable @draw@s an expression reads through the shapes
-- 'latentCellSum' walks: a draw (an applied literal lambda whose argument is
-- random and enumerable within the dense budget given the draws above it),
-- and an 'InjF' over such operands. Whatever else is reached is a leaf, which
-- 'latentCellSum' generates forward and declines if it draws fresh
-- randomness. That is the shape 'DrawSinking' leaves the enumerated operand
-- of a noisy observation in: @(draw x = r1 in draw y = r2 in f x y) + Normal
-- * s@, or with the draws sunk further into @f@'s operands.
--
-- Purely structural on purpose: whether a leaf is deterministic given the
-- draws is asked of its generated IR ('randomDrawSites', the test
-- 'toIREnumerate' applies to an enumerated body), not by re-inferring the
-- leaf -- a re-inference is a whole modality pass, and on the 1090-value
-- operator fold it cost several times the rest of the compile.
latentCellBinders :: CompilerMetadata -> Expr -> [String]
latentCellBinders meta = go (recoveredVars meta)
  where
    go fixed e
      | Expr _ (Apply (Expr _ (Lambda x b)) v) <- e
      , latentCellDraw meta fixed v = x : go (x : fixed) b
      | Expr _ (InjF (Named _) ops) <- e = concatMap (go fixed) ops
      | otherwise = []

-- | Is @v@, the value of a @draw@ with @fixed@ already enumerated, one
-- 'latentCellSum' loops over: random given them, with a finite domain within
-- the dense-enumeration budget ('enumerateAppliedLambda''s own gate).
latentCellDraw :: CompilerMetadata -> [String] -> Expr -> Bool
latentCellDraw meta fixed v =
  enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
  && pType (getTypeInfo (reinferReading meta fixed v)) /= Deterministic

-- | 'reinferRecovered' over only the recovered names @e@ reads. The others
-- cannot change its typing, and with none left there is no re-inference at
-- all -- a draw over a neural read of an argument, the common case, is typed
-- as it stands. A re-inference re-runs the modality engine, which costs a
-- tenth of a second per call on the operator fold of
-- 'latentCellBinders''s note, however small @e@ is.
reinferReading :: CompilerMetadata -> [String] -> Expr -> Expr
reinferReading meta names e = reinferRecovered meta (filter (`Set.member` freeVarsExpr e) names) e

-- | @sum_cells p(cell) * k(value(cell))@ over the joint cells of the draws
-- 'latentCellBinders' finds in @e@, one nested loop per draw, where @k@
-- compiles the term for one forward value of @e@ (an 'IRExpr' over the loop
-- variables). The terms keep their own dims and are combined as a mixture
-- ('enumMixP', @densityDim@ being the density terms' dim) in probability mode
-- and summed as CDF masses ('enumSumP') in cumulative mode -- the sums the
-- value-domain loop of the mixed enumerate-and-shift equation builds, over
-- cells instead of values. A cell with no mass is an impossible term, as a
-- value with none is there.
--
-- @k@ runs once, inside the innermost loop, and binds what it needs through
-- the writer, so its loop-invariant bindings are hoisted like any loop body's.
-- 'Nothing' (from @k@, or) when a leaf is not deterministic given the draws; the caller
-- then discards the scope this ran in.
latentCellSum :: CompilerMetadata -> Bool -> IRExpr -> Expr -> (IRExpr -> CompilerMonad (Maybe PResult)) -> CompilerMonad (Maybe PResult)
latentCellSum meta cumulative densityDim e k
  | Expr _ (Apply (Expr _ (Lambda x b)) v) <- e
  , latentCellDraw meta (recoveredVars meta) v = do
      -- As in 'enumerateAppliedLambda': the loop binds @x@ around the draw's
      -- own measure too, so a value reading another @x@ is renamed apart.
      (boundVar, drawBody) <-
        if x `Set.member` freeVarsExpr v
          then do
            fresh <- mkVariable x
            return (fresh, renameFreeVar x fresh b)
          else return (x, b)
      let sr = semiringOf meta
          bodyMeta = recoverVars [boundVar] meta{ typeEnv = (boundVar, (rType (getTypeInfo v), False)) : typeEnv meta
                         , fixedLatents = Set.insert (chainName (getTypeInfo v)) (fixedLatents meta) }
      innerO <- scoped (do
        pRaw <- (unP . rProb) <$> toIRInference meta False (reinferReading meta (recoveredVars meta) v) (IRVar boundVar)
        pVar <- mkVariable "cell_p"
        setVariables [(pVar, pRaw)]
        bodyRes <- latentCellSum bodyMeta cumulative densityDim drawBody k
        return (prodP sr (impossibleWhen (IROp OpEq (IRVar pVar) (srZero sr)) (mass (IRVar pVar))) <$> bodyRes))
      forM (openValue innerO) $ \res -> do
        let irTuple = generateLetInBlock meta (res <$ innerO)
            (outerBinds, innerTuple) = hoistInvariantBindings boundVar irTuple
            dom = head [mv | DiscreteValues mv <- tags (getTypeInfo v)]
            bc = countBranches (compilerConfig meta)
        setVariables outerBinds
        if cumulative
          then enumSumP sr bc id boundVar dom innerTuple
          else enumMixP sr bc id densityDim boundVar dom innerTuple
  | Expr ti (InjF (Named name) ops) <- e = do
      let go acc [] = do
            FPair fwd _ <- instantiate mkVariable (adtDecls meta) (resolveInjF (rType ti) name)
            let FDecl {inputVars=vars, body=fwdExpr} = fwd
            prefix <- mkVariable ""
            k (irMap (uniqueify vars prefix) (buildLetIns (zip vars (reverse acc)) fwdExpr))
          go acc (o : os) = latentCellSum meta cumulative densityDim o (\val -> go (val : acc) os)
      go [] ops
  | otherwise = do
      ir <- toIRGenerate meta e
      if null (randomDrawSites (detGenNames meta) ir)
        then k ir
        else return Nothing

-- | The partial application @f a1 .. ak@ (k >= 1) of 'Apply' @l v@, retyped
-- with the enclosing enumerated latents fixed, when the application should be
-- compiled by enumerating @v@: @f@ is a conditional top-level function, every
-- @ai@ is deterministic given the enclosing latents, the application is
-- saturated, and @v@ is a probabilistic enumerable draw. The one-argument case
-- is 'isEnumerableApplication''s; this is its curried generalisation, which
-- 'SPLL.Analysis.applyTags' tags since the same task.
--
-- A random /leading/ argument is not handled here -- 'enumerateCurriedArgument'
-- marginalises the last argument only -- and declines, leaving the node to the
-- equations that follow, exactly as before.
curriedEnumerableCallee :: CompilerMetadata -> Expr -> Expr -> Maybe Expr
curriedEnumerableCallee meta l v
  | (hd@(Expr _ (Var f)), args@(_:_)) <- flattenApplySpine l'
  , headIsConditional (fcData meta) (compilingProgram meta) hd
  , Just (TArrow _ _, True) <- lookup f (typeEnv meta)
  , all ((== Deterministic) . pType . getTypeInfo) args
  , isEnumerable (tags (getTypeInfo v))
  , pType (getTypeInfo v) /= Deterministic
  , not (returnsFunction (rType (getTypeInfo l)))
  = Just l'
  | otherwise = Nothing
  where
    l' = reinferRecovered meta (recoveredVars meta) l
    returnsFunction (TArrow _ (TArrow _ _)) = True
    returnsFunction _ = False

-- | A saturated call @f a1 .. an@ of a conditional top-level function whose
-- one non-deterministic argument @ai@ is enumerable and is not the last one
-- (that case is 'curriedEnumerableCallee''s): every other argument is
-- deterministic given the enclosing latents. Answers the call with @ai@
-- replaced by a given expression, and @ai@ itself. Two or more random
-- arguments decline, leaving the call to 'leadingArgBinding'.
leadingEnumerableArgument :: CompilerMetadata -> Expr -> Maybe (Expr -> Expr, Expr)
leadingEnumerableArgument meta expr0
  | not (isTArrowType (rType (getTypeInfo expr)))
  , (hd@(Expr _ (Var f)), args@(_:_:_)) <- flattenApplySpine expr
  , Just (TArrow _ _, True) <- lookup f (typeEnv meta)
  , [i] <- [ k | (k, a) <- zip [0 ..] args, pType (getTypeInfo a) /= Deterministic ]
  , i < length args - 1
  , ai <- args !! i
  , isEnumerable (tags (getTypeInfo ai))
  , headIsConditional (fcData meta) (compilingProgram meta) hd
  = Just (\x -> replaceSpineArg (length args - 1 - i) x expr, ai)
  | otherwise = Nothing
  where
    expr = reinferRecovered meta (recoveredVars meta) expr0

-- | @sum_x P(v = x) * P(body x = sample)@ over @v@'s domain, where @body x@ is
-- the call with @v@'s position fixed at @x@: for the curried spine
-- 'curriedEnumerableCallee' accepted, @l x@; for a leading argument,
-- 'leadingEnumerableArgument''s spine. The counterpart of
-- 'enumerateAppliedLambda', which marginalises a 'let'-bound argument through
-- its lambda body; a partial application has no lambda body of its own to
-- resolve, so the loop body is the application itself with a fresh loop
-- variable in the argument position. Inside the loop every argument is fixed,
-- so 'toIREnumerate' compiles it forward and compares (or, for a helper that
-- draws fresh randomness, hands it to the ordinary inference rules).
enumerateCurriedArgument :: CompilerMetadata -> Bool -> (Expr -> Expr) -> Expr -> IRExpr -> CompilerMonad PResult
enumerateCurriedArgument meta cumulative mkBody v sample = do
  boundVar <- mkVariable "enum_arg"
  let vTi = getTypeInfo v
      loopVar = Expr (vTi {pType = Deterministic, tags = []}) (Var boundVar)
      loopBody = mkBody loopVar
      (keepsDims, dimBound) = enumSumDims meta (rType (getTypeInfo loopBody))
      bodyMeta = recoverVars [boundVar] meta { typeEnv = (boundVar, (rType vTi, False)) : typeEnv meta
                      , dimAwareEnum = keepsDims }
  irTuple <- scoped (do
    pBranch <- (unP . rProb) <$> toIRInference meta False (reinferRecovered meta (recoveredVars meta) v) (IRVar boundVar)
    bodyRes <- toIREnumerate bodyMeta cumulative loopBody sample
    return (pBranch, bodyRes))
  let discreteVVals = head [x | DiscreteValues x <- tags vTi]
  enumSumTerms meta dimBound boundVar discreteVVals irTuple

-- | How an enumerated sum whose body measures a value of type @rt@ combines
-- its terms (task enumerated-sum-over-density-body). The first component is
-- 'dimAwareEnum' for the body: whether this sum, and every one enclosing it,
-- reports the body's dim faithfully. The second is the static dim bound the
-- dim-aware sum ('enumMinDimP') is built with, 'Nothing' when every term is
-- a mass anyway (a float-free type, which 'floatFree' covers).
--
-- A type with no static bound ('floatLeafBound' 'Nothing': a list of reals)
-- keeps the old sum, which reports a mass: there 'forwardOrInfer''s run-time
-- guard stays, and raises on a density rather than mislabelling it.
enumSumDims :: CompilerMetadata -> RType -> (Bool, Maybe Int)
enumSumDims meta rt = case floatLeafBound (adtDecls meta) (resultOf rt) of
  Nothing -> (False, Nothing)
  Just d -> (dimAwareEnum meta, if d > 0 then Just d else Nothing)
  where
    -- The bound is taken on what the enumerated body returns, which for a
    -- lambda being applied is its codomain.
    resultOf (TArrow _ b) = b
    resultOf t = t

-- | Sum the scoped terms of an enumerated variable's domain, each the body's
-- result and the mass @pBranch@ of its value, over the domain: the body
-- weighted by that mass. With a dim bound ('enumSumDims') and a body whose
-- dim is not statically 0 ('packedStaticDim') the sum keeps the terms' dims
-- ('enumMinDimP'); otherwise it is the plain mass sum 'enumSumP'. A
-- forward-and-compare indicator's dim is always statically 0, so those sums
-- emit what they did before. In the dim-aware sum a value with no mass is an
-- impossible term rather than a possible zero: the lowest possible dim
-- decides the sum's dim, and a zero-weight atom must not outvote a real
-- density (the tag over-approximates the support).
enumSumTerms :: CompilerMetadata -> Maybe Int -> Varname -> MultiValue -> Open (IRExpr, PResult) -> CompilerMonad PResult
enumSumTerms meta dimBound boundVar vals o = do
  let sr = semiringOf meta
      bc = countBranches (compilerConfig meta)
      weighted (pBranch, r) = onProb (\p -> srTimes sr p pBranch) r
      sumWith f o' = do
        let irTuple = generateLetInBlock meta o'
            (outerBinds, innerTuple) = hoistInvariantBindings boundVar irTuple
        setVariables outerBinds
        f boundVar vals innerTuple
  case dimBound of
    Just d | packedStaticDim (generateLetInBlock meta (snd <$> o)) /= Just 0 -> do
      o' <- scoped (do
        (pBranch, r) <- inline o
        w <- mkVariable "enum_weight"
        setVariables [(w, pBranch)]
        return (impossibleWhen (IROp OpEq (IRVar w) (srZero sr)) (weighted (IRVar w, r))))
      sumWith (enumMinDimP sr bc id d) o'
    _ -> sumWith (enumSumP sr bc id) (weighted <$> o)

-- | The dim of a packed result ('packResult' under its let block) when it is
-- a compile-time constant: read through the block's bindings, tuple
-- projections of constructed tuples (and of both arms of a guarded block), an
-- @if@ whose arms agree and a sum of dims. 'Nothing' when the dim depends on anything else (a run-time
-- projection of a call, a binding outside the block, an @ANY@ test).
packedStaticDim :: IRExpr -> Maybe Int
packedStaticDim e = case flattenLetIns e of
  (binds, IRConstruct TgTuple [_, IRConstruct TgTuple [d, _]]) -> staticInt (Map.fromList binds) d
  _ -> Nothing
  where
    staticInt env x = case resolve env x of
      IRConst (VInt n) -> Just n
      IRIf _ a b -> do
        n <- staticInt env a
        m <- staticInt env b
        if n == m then Just n else Nothing
      IROp OpPlus a b -> (+) <$> staticInt env a <*> staticInt env b
      _ -> Nothing
    resolve env x = case x of
      IRVar v | Just b <- Map.lookup v env -> resolve (Map.delete v env) b
      IRLetIn v b rest -> resolve (Map.insert v b env) rest
      IRDestruct AcFst t | IRConstruct TgTuple [a, _] <- resolve env t -> resolve env a
      IRDestruct AcSnd t | IRConstruct TgTuple [_, b] <- resolve env t -> resolve env b
      -- a projection of a guarded block ('closeResult'): project both arms
      IRDestruct acc t | IRIf c a b <- resolve env t -> IRIf c (IRDestruct acc a) (IRDestruct acc b)
      _ -> x


-- ===== Agreement fusion (task categorical-product-ov-fusion) =====
--
-- Two categorical variables combined by /agreement/ -- @let a = .. in let b =
-- .. in if a == b then X else Y@ -- are the product-of-experts shape: the kept
-- mass is @P_a(k) * P_b(k)@ per class, and @sum_k P_a(k) * P_b(k)@ is the
-- fusion evidence. The corpus spells it as @showcase_poe_discrete@ and
-- @observeDiscretePoE@.
--
-- Compiled by the ordinary path this is a /joint/ enumeration: the outer
-- 'enumerateAppliedLambda' loops over @a@'s domain and, inside that loop,
-- 'toIREnumerate' reaches the inner @let@ and loops over @b@'s domain again,
-- evaluating @b@'s marginal V times per outer value. That is O(V^2) and it
-- calls the second network V^2 times. At the vocabulary scale this exists for
-- (V in the tens of thousands) V^2 is four to five orders of magnitude too
-- slow, so the complexity bound is the feature, not an optimisation of it.
--
-- The fusion rewrites the double sum into dense vector algebra over the shared
-- domain. Writing @pa@/@pb@ for the two marginals, @T@/@E@ for the two arms'
-- masses against the query, and @Sb = sum_k pb(k)@:
--
-- @
--   sum_j pa(j) * sum_k pb(k) * ( [j==k] * T(j) + [j/=k] * E(j) )
--     = sum_j pa(j) * pb(j) * T(j)          -- the diagonal
--     + sum_j pa(j) * (Sb - pb(j)) * E(j)   -- everything off it
-- @
--
-- Both lines are O(V): four 'BMap's build the @[V]@ vectors, a 'BZip' with the
-- semiring's own multiply is the elementwise product the task is named for,
-- and a 'BReduce' sums. @Sb@ is one reduction of a vector that is built once.
--
-- The off-diagonal line is a /subtraction/, and that is forced rather than
-- chosen: any O(V) form of "sum over everything but the diagonal" is the total
-- minus the diagonal, because summing the off-diagonal terms directly is the
-- O(V^2) we are removing. It loses precision exactly when the agreement mass
-- approaches @Sa*Sb@ (near-certain agreement), which is the same cancellation
-- the existing @AnyExcept@ marginal-minus-one-branch site already accepts, and
-- is why 'srMinus' rather than a hand-rolled @-@ is used: log space needs
-- 'logSubExpIR'.
--
-- WHAT IS NOT FUSED, and why each refusal is cheap. Every one of them falls
-- back to 'enumerateAppliedLambda', so the behaviour is exactly today's:
--
--   * __branch counting__ (@-c@). The fused artifact really does traverse
--     fewer leaves, so its branch count is not the enumerated path's -- and
--     'bc' is documented as a measure of the compiled artifact rather than an
--     invariant of the distribution, so it /should/ differ. Refusing under
--     @-c@ keeps every existing @-c@ number exactly as it was and, better,
--     turns the corpus's own "branch counting does not change the
--     probability" property into a differential test of the fused path
--     against the unfused one.
--   * __topK__. Pruning is a per-branch decision inside the enumeration
--     loop, and the fused form has no per-branch site to hang it on. A fused
--     result would silently ignore the cutoff.
--   * __the max-product semiring__. The algebra above distributes a product
--     over a /sum/ and takes a complement; neither is valid for max, whose
--     'srMinus' is 'Nothing' for the same reason.
--   * __an arm that reads the inner variable__. Then @E@ is @E(j,k)@, the
--     off-diagonal sum does not factor, and there is no O(V) form at all.
--   * __unequal domains__, which would make the elementwise product a
--     shape error.
--   * __operands that may share an enumerated latent__. This is the
--     correctness gate, not a performance one: @sum_k pa(k) * pb(k)@ is the
--     right joint only when the two subexpressions are independent. It is
--     answered by the decomposability analysis ('latentVerdicts'), which is
--     keyed by binary-'InjF' chain name and scope-correct -- and the
--     agreement condition @a == b@ /is/ a binary 'InjF', so the verdict for
--     exactly this node's two operands is already computed. That analysis was
--     built (design materialize-discrete-marginals) with no consumer; this is
--     its consumer. @let a = camNN i in let b = f a in if a == b then ..@ is
--     the shape it refuses.
data AgreementShape = AgreementShape
  { agVar    :: Varname     -- ^ the outer bound variable, reused as the loop variable of every emitted 'BMap'
  , agInner  :: Varname     -- ^ the inner bound variable, which the arms must not read
  , agOpA    :: Expr        -- ^ the outer operand, whose marginal is the left factor
  , agOpB    :: Expr        -- ^ the inner operand, whose marginal is the right factor
  , agDomain :: MultiValue  -- ^ the shared enumerated domain
  , agThen   :: Expr        -- ^ the arm taken when the two agree
  , agElse   :: Expr        -- ^ the arm taken when they do not
  , agRType  :: RType       -- ^ the conditional's return type, picking the query comparison
  }

-- | Recognise the agreement shape at an enumerable application, or answer
-- 'Nothing' so the caller takes the ordinary enumeration.
--
-- Recognition is at the surface-language level -- it matches the SPLL AST
-- (a nested enumerable @let@ whose body is an @if@ over an @InjF (Named "eq")@ of the
-- two bound variables), not an IR peephole. An IR-level rewrite would have to
-- prove that an arbitrary loop body is affine in an equality indicator, which
-- is symbolic algebra over IR; the source shape states it outright.
--
-- Callable only where 'enumerateAppliedLambda' is, since it resolves chain
-- names with the same partial 'equivalentLambda'.
-- | 'Control.Monad.guard' for 'Maybe', spelled locally: this module already
-- binds @guard@ as a local name for an IR guard expression in two unrelated
-- places, and importing the 'Alternative' one would shadow them.
require :: Bool -> Maybe ()
require True  = Just ()
require False = Nothing

agreementShape :: CompilerMetadata -> Expr -> Expr -> Maybe AgreementShape
agreementShape meta l v = do
  let cfg = compilerConfig meta
  -- Refusals that do not depend on the shape at all, checked first so the
  -- common non-fusing compile does no AST walking.
  require (not (countBranches cfg))
  require (topKThreshold cfg == Nothing)
  require (srReduceOp (semiringOf meta) /= ROpMax)
  let fcd = fcData meta
      fExprs = map snd (functions (compilingProgram meta))
      (_, vOuter, bodyACN, _) = equivalentLambda "agreementShape" fcd (chainName (getTypeInfo l))
      bodyA = findExprWithCN fExprs bodyACN
  (l2, v2) <- case node bodyA of
    Apply a b | isEnumerableApplication meta a b -> Just (a, b)
    _ -> Nothing
  let (_, vInner, bodyBCN, _) = equivalentLambda "agreementShape/inner" fcd (chainName (getTypeInfo l2))
      bodyB = findExprWithCN fExprs bodyBCN
  (cond, thenE, elseE) <- case node bodyB of
    IfThenElse c t e -> Just (c, t, e)
    _ -> Nothing
  -- The condition must be exactly the two bound variables compared for
  -- equality, in either order.
  case node cond of
    InjF (Named "eq") [Expr _ (Var x), Expr _ (Var y)]
      | (x, y) == (vOuter, vInner) || (x, y) == (vInner, vOuter) -> Just ()
    _ -> Nothing
  -- Neither arm may read the inner variable: the off-diagonal sum only
  -- factors because the arms are constant in it. Anywhere in the arm, not
  -- just at its root -- 'varsOfExpr' alone sees only the root node, so
  -- @left (b + 10)@ used to pass and the fused body read an unbound @b@
  -- (test/cases/neural/agreementArmReadsInnerNested).
  require (Set.notMember vInner (containedVars varsOfExpr thenE))
  require (Set.notMember vInner (containedVars varsOfExpr elseE))
  -- Independence, from the decomposability analysis keyed by this very node.
  require (Map.lookup (chainName (getTypeInfo cond)) (latentVerdicts meta) == Just False)
  domA <- enumeratedDomain v
  domB <- enumeratedDomain v2
  require (domA == domB)
  return AgreementShape
    { agVar = vOuter, agInner = vInner, agOpA = v, agOpB = v2
    , agDomain = domA, agThen = thenE, agElse = elseE
    , agRType = rType (getTypeInfo bodyB) }

-- | A node's single 'DiscreteValues' domain, if it has exactly one. Total
-- where 'enumerateAppliedLambda' uses a @head@ on the same list, because a
-- missing tag here means "do not fuse" rather than a compiler bug.
enumeratedDomain :: Expr -> Maybe MultiValue
enumeratedDomain e = case [x | DiscreteValues x <- tags (getTypeInfo e)] of
  (d:_) -> Just d
  []    -> Nothing

-- | Emit the fused O(V) form for a recognised 'AgreementShape'. See the
-- commentary on 'AgreementShape' for the algebra this implements.
enumerateAgreement :: CompilerMetadata -> Bool -> AgreementShape -> IRExpr -> CompilerMonad PResult
enumerateAgreement meta cumulative ag sample = do
  let sr    = semiringOf meta
      v     = agVar ag
      dom   = agDomain ag
      rt    = agRType ag
      -- Both bound variables enter the type environment exactly as the nested
      -- enumeration would have bound them, so the arms and the operands are
      -- compiled in the scope they were written in.
      metaV = meta { typeEnv = (agVar ag,   (rType (getTypeInfo (agOpA ag)), False))
                            : (agInner ag, (rType (getTypeInfo (agOpB ag)), False))
                            : typeEnv meta }
      -- One compiled body, as a function of the shared loop variable.
      -- Bindings the sub-compilation floated are bound INSIDE the body, since
      -- it becomes a 'BMap' lambda and a loop-variable read must not escape
      -- its binder -- except for those that do not mention the loop variable
      -- at all, which are lifted out by 'hoistInvariantBindings' exactly as
      -- 'enumerateAppliedLambda' lifts them. That split is not cosmetic: the
      -- raw network call (@camNN(img)@) is loop-invariant, and leaving it
      -- inside would run the network once per class instead of once, turning
      -- an O(V) probability computation back into O(V) *network invocations*
      -- -- which at vocabulary scale is the whole cost.
      closeOver m = do
        o <- m
        let (invariant, inner) = hoistInvariantBindings v (closeExpr o id)
        setVariables invariant
        return inner
  paBody <- closeOver (scoped ((unP . rProb) <$> toIRInference metaV False (agOpA ag) (IRVar v)))
  pbBody <- closeOver (scoped ((unP . rProb) <$> toIRInference metaV False (agOpB ag) (IRVar v)))
  -- The arms are generated forward and compared against the query, exactly as
  -- 'toIREnumerate's 'IfThenElse' equation does -- including its premise
  -- check, since the fused form generates the same operands it does.
  let armMass e = do
        eIR <- toIRGenerate metaV e
        requireDeterministicUnderEnum metaV "agreement arm" e eIR
        return (eIR, if cumulative then compareValueExpr sr rt eIR sample
                                   else maskSR sr (leafEqIR rt sample eIR))
      -- 'closeOver' for an arm, also handing back the arm's generated value so
      -- 'armSum' can recognise a constructor of the loop variable.
      closeOverArm m = do
        o <- m
        let (invariant, inner) = hoistInvariantBindings v (closeExpr o snd)
        setVariables invariant
        return (fst (openValue o), inner)
  (thenIR, thenBody) <- closeOverArm (scoped (armMass (agThen ag)))
  (elseIR, elseBody) <- closeOverArm (scoped (armMass (agElse ag)))
  let mkMap b = IRBuiltin BMap [IRLambda v b, tensorDomainSR dom]
      zipSR a b  = IRBuiltin (BZip (srTimesOp sr)) [a, b]
      reduceSR t = IRBuiltin (BReduce (srReduceOp sr) 0) [t]
      -- @sum_j w(j) * M(j)@ for a weight vector @w@ and an arm's mass @M@
      -- against the query (task agreement-enumeration-point-collapse). Three
      -- forms, cheapest first; each is exactly the generic scan's value.
      --
      --   * __the arm is a constructor of the loop variable__ (@right a@) over a
      --     contiguous Int domain, for a point query: @M(j)@ is the indicator
      --     @[sample == Tag j]@, which is nonzero for at most one @j@ -- the
      --     sample's payload. So the sum is a tag test on the sample and one
      --     'BIndex' at the payload's position, O(1) after the vectors exist,
      --     where the scan built a second @[V]@ indicator vector against the
      --     query. A payload of ANY matches every @j@ (it is the plain sum of
      --     @w@), as does a top-level ANY sample; a payload outside the domain
      --     matches none. Contiguity is what makes the position arithmetic
      --     (@k - lo@) rather than a lookup; a non-contiguous domain keeps the
      --     scan, since finding the position there is itself the O(V) search.
      --   * __the arm does not read the loop variable__ (@left ()@): @M@ is a
      --     constant of the loop, so it factors out of the sum as one
      --     indicator times @sum_j w(j)@.
      --   * otherwise, the scan.
      armSum w eIR armBody
        | not cumulative
        , Just (isTag, fromTag) <- constructorOfLoopVar eIR
        , Just (lo, n) <- contiguousIntDomain dom = do
            wV <- mkVariable "agree_arm_weights"
            kV <- mkVariable "agree_key"
            setVariables [(wV, w)]
            let k = IRVar kV
                inDomain = IROp OpAnd (notIR (IROp OpLessThan k (IRConst (VInt lo))))
                                      (IROp OpLessThan k (IRConst (VInt (lo + n))))
                position = IRBuiltin (BIndex 0) [IRVar wV, IROp OpSub k (IRConst (VInt lo))]
            return $
              IRIf (IRUnaryOp OpIsAny sample) (reduceSR (IRVar wV)) $
              IRIf (IRDestruct isTag sample)
                (IRLetIn kV (IRDestruct fromTag sample)
                  (IRIf (IRUnaryOp OpIsAny k) (reduceSR (IRVar wV))
                    (IRIf inDomain position (srZero sr))))
                (srZero sr)
        | not (v `freeInIR` armBody) = return (srTimes sr armBody (reduceSR w))
        | otherwise = return (reduceSR (zipSR w (mkMap armBody)))
      -- @Tag v@, seen through the let-aliases the arm's generate compilation
      -- wraps a variable read in (@let a' = v in Right a'@).
      constructorOfLoopVar = conOf [v]
      conOf vs (IRLetIn x (IRVar y) b) | y `elem` vs = conOf (x : vs) b
      conOf vs (IRConstruct TgRight [IRVar x]) | x `elem` vs = Just (AcIsRight, AcFromRight)
      conOf vs (IRConstruct TgLeft  [IRVar x]) | x `elem` vs = Just (AcIsLeft,  AcFromLeft)
      conOf _ _ = Nothing
  -- The two marginal vectors are each read twice (the diagonal and the
  -- off-diagonal line), so they are bound once rather than rebuilt.
  paV <- mkVariable "agree_pa"
  pbV <- mkVariable "agree_pb"
  sbV <- mkVariable "agree_pb_total"
  cV  <- mkVariable "agree_complement"
  setVariables [ (paV, mkMap paBody)
               , (pbV, mkMap pbBody)
               , (sbV, reduceSR (IRVar pbV)) ]
  let -- the elementwise product of the two [V] marginals: the whole point
      product' = zipSR (IRVar paV) (IRVar pbV)
      -- (Sb - pb(j)) per element. A BMap rather than a second BZip because
      -- 'srMinus' is 'logSubExpIR' under log space, which is not an Operand.
      -- Agreement fusion is never chosen under max-product (see above), so
      -- 'srMinus' is always present here.
      minus = fromMaybe (error "agreement fusion under a semiring without srMinus") (srMinus sr)
      complement = IRBuiltin BMap [IRLambda cV (minus (IRVar sbV) (IRVar cV)), IRVar pbV]
  diagonal    <- armSum product' thenIR thenBody
  offDiagonal <- armSum (zipSR (IRVar paV) complement) elseIR elseBody
  opaqueMass sr (srPlus sr diagonal offDiagonal) const0

-- | A domain whose enumeration order ('multiValueToValueList', the order
-- 'tensorDomainSR' lays a @[V]@ vector out in) is @lo, lo+1, .., lo+n-1@, as
-- @(lo, n)@ -- so a value's position in the vector is plain subtraction.
contiguousIntDomain :: MultiValue -> Maybe (Int, Int)
contiguousIntDomain mv = case multiValueToValueList mv of
  vals@(VInt lo : _)
    | vals == map VInt [lo .. lo + length vals - 1] -> Just (lo, length vals)
  _ -> Nothing

-- | Refuse a generate-backed probability. 'toIREnumerate' compiles its operands
-- /forward/ on the premise stated at its fallback equation: with the enclosing
-- discrete latents pinned to concrete enumerated values, the operand is
-- deterministic, so generating it and comparing the result against the sample is
-- an exact indicator. When that premise does not hold the same code emits a
-- fresh random draw compared against the query value -- which is not a
-- probability at all, but a number that differs on every call with the same
-- argument, with no crash and no diagnostic on the Python and Julia backends
-- (task @self-recursive-prob-nondeterministic-fallback@).
--
-- The shape that reaches it is an unbounded self-recursive branch with no
-- decreasing argument (@main = ... if a == b then a else main@): @main@'s own
-- @_gen@ call is spliced into @main_prob@. NeST does exact inference, so this is
-- refused at compile time rather than emitted -- matching the sibling
-- witness-construction failures, which fail loudly. Solving the resulting
-- fixed-point equation algebraically was considered and declined: it would make
-- \"does my program infer?\" unpredictable from the source.
--
-- This is the local guard for the enumeration path only; the central \"no
-- generate call in any probability-mode body\" invariant is investigation
-- @generate-backed-inference-sweep@.
requireDeterministicUnderEnum :: CompilerMetadata -> String -> Expr -> IRExpr -> CompilerMonad ()
requireDeterministicUnderEnum meta what src ir =
  case nub (recursiveDrawCalls (cyclicGenNames meta Set.\\ detGenNames meta) (enclosingFunction meta src) ir) of
    [] -> return ()
    gens -> refuse cn $ init $ unlines
      [ "probability-mode compilation reached a generate-backed fallback."
      , "The " ++ what ++ " of an enumerated conditional (chain name " ++ cn ++ ") draws fresh"
      , "randomness by calling " ++ intercalate ", " gens ++ ", which is on a recursive call cycle."
      , "Measuring that call means re-entering the same enumeration with an unchanged argument,"
      , "which does not terminate, and generating it forward instead would produce a probability"
      , "function that returns a different number on every call with the same query value."
      , "NeST does exact inference, so this is refused. This is the shape of an unbounded"
      , "self-recursive branch (`... else main`), or of a call through another function on the"
      , "cycle, where no argument of a direct self-call changes. Rewrite the recursion so that"
      , "it calls itself directly with a changed argument (a counter, `tail xs`), or use the"
      , "program in generate mode only."
      , "(task self-recursive-prob-nondeterministic-fallback)" ]
  where cn = chainName (getTypeInfo src)

-- | The function whose body contains the node, with its parameter names; the
-- context 'recursiveDrawCalls' needs to tell a self-call that changes an
-- argument from one that does not. 'Nothing' when no declaration contains it.
enclosingFunction :: CompilerMetadata -> Expr -> Maybe (Varname, [Varname])
enclosingFunction meta src =
  listToMaybe [ (n ++ "_gen", params b)
              | (n, b) <- functions (compilingProgram meta), contains b ]
  where
    cn = chainName (getTypeInfo src)
    contains e = chainName (getTypeInfo e) == cn || any contains (getSubExprs e)
    params (Expr _ (Lambda x rest)) = x : params rest
    params _ = []

-- | The random calls in a generate-mode IR expression that go to a function on
-- a call cycle -- the subset of 'randomDrawSites' 'requireDeterministicUnderEnum'
-- still refuses.
--
-- A direct self-call that changes an argument is not one of them (task
-- decreasing-recursion-refused-as-generate-fallback): the call is made with a
-- different argument than the enclosing invocation received (@loop (r - 1)@,
-- @walk (tail xs)@), so its probability function is a different invocation,
-- not the same enumeration re-entered, and the callee's own probability
-- function measures it. What stays refused is a call whose every argument is
-- the enclosing function's own parameter in its own position (@... else main@),
-- any call to a different function on the cycle (mutual recursion: the
-- argument comparison says nothing there), and a bare or partial reference.
recursiveDrawCalls :: Set.Set Varname -> Maybe (Varname, [Varname]) -> IRExpr -> [String]
recursiveDrawCalls cyc encl = go
  where
    go ir = case collectApplyChain ir of
      (IRVar n, args)
        | Set.member n cyc, not (null args) ->
            [ n | not (changesArgument n args) ] ++ concatMap go args
      (IRVar n, _) | Set.member n cyc -> [n]
      _ -> concatMap go (getIRSubExprs ir)
    changesArgument n args = case encl of
      Just (self, ps) | self == n, length args == length ps ->
        or (zipWith (\p a -> a /= IRVar p) ps args)
      _ -> False

-- | The randomness sources in a generate-mode IR expression, named for a
-- diagnostic; empty exactly when 'isPureGiven' would call the expression pure.
-- The two are the optimizer's own notions of effect: an 'IRSample', and a
-- reference to a generate function not proven deterministic.
randomDrawSites :: Set.Set Varname -> IRExpr -> [String]
randomDrawSites det ir = case ir of
  IRSample d -> ["from " ++ show d]
  IRVar n | isEffectfulVar n && not (Set.member n det) -> ["by calling " ++ n]
  _ -> concatMap (randomDrawSites det) (getIRSubExprs ir)

toIREnumerate :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
-- Nested enumerable application (e.g. an inner `let` binding a fresh discrete draw):
-- recurse with enumeration + weighting rather than generating the draw forward.
--
-- Gated on the same materialization budget as 'toIRInference''s enumerable
-- 'Apply' equation (task enumeration-budget-gate-misses-nested-application):
-- without it a small outer enumeration passes that gate and then materializes
-- an over-budget inner one densely, one level down. Over budget, the inner
-- application is handed to 'toIRInference' rather than falling through here --
-- the remaining 'toIREnumerate' equations have no plan path, and the catch-all
-- compiles the node forward and refuses it as a generate-backed fallback. In
-- 'toIRInference' the same gate declines again and dispatch reaches the
-- plan-guided arm. That is sound for the same reason 'enumerateAppliedLambda'
-- calls 'toIRInference' on its own argument: the enclosing bound variables are
-- already in 'typeEnv' as locals, so P(application = sample) there is exactly
-- the conditional this equation would otherwise have enumerated.
--
-- Not for an argument that is itself a variable this enumeration already
-- fixed (@hit x@ inside the loop over @x@): its measure is the indicator
-- @o == x@, so enumerating it again walks the whole domain for the one value
-- it keeps -- a 97-fold loop per cell on a CLEVR object slot (task
-- product-scene-discrete-count-enumerates-slot-patterns). The application is
-- deterministic given the loop, and the forward equations below compile it.
toIREnumerate meta cumulative e@(Expr _ (Apply l v)) sample
  | isEnumerableApplication meta l v
  , not (isRecoveredVar v) =
  if not (enumerationWithinMaterializationBudget meta (tags (getTypeInfo v)))
    then toIRInference meta cumulative (reinferRecovered meta (recoveredVars meta) e) sample
    else case agreementShape meta l v of
      Just ag -> enumerateAgreement meta cumulative ag sample
      Nothing
        | not cumulative, Just net <- constraintNet meta e -> compileConstraintNet meta net sample
        | Just ds <- drawStack meta e -> factoredDrawStack meta cumulative ds sample
        | otherwise -> enumerateAppliedLambda meta cumulative l v sample
  where
    isRecoveredVar (Expr _ (Var x)) = x `elem` recoveredVars meta
    isRecoveredVar _ = False
toIREnumerate meta cumulative (Expr TypeInfo{chainName=cn} (Var _)) sample = do
  let equivCN = equivalentChainName "toIREnumerate/Var" (fcData meta) cn
  let fs = map snd (functions (compilingProgram meta))
  let equivExpr = findExprWithCN fs equivCN
  toIREnumerate meta cumulative equivExpr sample
toIREnumerate meta cumulative whole@(Expr TypeInfo{rType=rt} (IfThenElse c t e)) sample = do
  let sr = semiringOf meta
  cIR <- toIRGenerate meta c
  tIR <- toIRGenerate meta t
  eIR <- toIRGenerate meta e
  forwardOrInfer meta cumulative whole sample
    [("condition", c, cIR), ("then branch", t, tIR), ("else branch", e, eIR)] $ do
    --(pBranch, _, _) <- toIRInference meta False distr elem
    -- Due to eager evaluation, we must make sure, that the wrong branch is not executed
    let condSelector resultExpr = IRIf cIR resultExpr (srZero sr)
    let notCondSelector resultExpr = IRIf (IRUnaryOp OpNot cIR) resultExpr (srZero sr)
    let thenSelector = if cumulative then compareValueExpr sr rt tIR sample else maskSR sr (leafEqIR rt sample tIR)
    let elseSelector = if cumulative then compareValueExpr sr rt eIR sample else maskSR sr (leafEqIR rt sample eIR)
    let thenRes = condSelector thenSelector
    let elseRes = notCondSelector elseSelector
    -- The two selectors are mutually exclusive (exactly one is ever "live", the
    -- other is the semiring zero), so this is a mixture-sum, not a plain add:
    -- in log space 'srZero' is negative infinity, and OpPlus-ing that against a
    -- finite log-probability would wrongly zero the whole result out.
    let returnExpr = srPlus sr thenRes elseRes
    return (mass returnExpr)
-- Fallback: under enumeration the bound variable carries a concrete enumerated value,
-- so the body is deterministic and can be generated forward and compared to the sample.
-- This covers shapes whose root is not an if, e.g. an InjF sum of conditional terms.
toIREnumerate meta cumulative e sample = do
  eIR <- toIRGenerate meta e
  forwardOrInfer meta cumulative e sample [("expression", e, eIR)] $ do
    let rt = rType (getTypeInfo e)
    if cumulative
      then return (mass (compareValueExpr (semiringOf meta) rt eIR sample))
      else return (indicatorP (semiringOf meta) (leafEqIR rt sample eIR))

-- | The premise check of 'toIREnumerate's forward-and-compare equations, with
-- the way out it used to lack (task enum-let-latent-gates-fresh-draw).
--
-- When every forward-compiled operand is deterministic given the enumerated
-- latents, the forward-and-compare body (the last argument) is exact and is
-- used. When one of them draws fresh randomness, the node is not refused but
-- handed to 'toIRInference' -- with every enclosing enumerated variable retyped
-- 'Deterministic' ('reinferRecovered' over 'recoveredVars'), since inside the
-- enumeration loop each holds one fixed domain value. That is the same step the
-- over-budget nested application in this function already takes, and it is
-- sound for the same reason: the enumerated variables are 'typeEnv' locals, so
-- P(node = sample) under the ordinary rules is exactly the conditional the
-- enumeration needs. A fresh draw then meets its usual machinery -- an @if@
-- over a fixed latent selects an arm and measures it, an @if@ over a fresh
-- Bernoulli is the ordinary mixture, a tuple factorizes -- instead of being
-- generated and compared against the query. The canonical shape is the noisy
-- observation of a shared latent,
-- @draw b = Uniform < 0.5 in (b, if b then Uniform < 0.9 else Uniform < 0.1)@,
-- which used to be refused although hoisting the noise into its own enumerable
-- binding compiled.
--
-- The refusal stays for a draw through a function on a call cycle: handing
-- that to 'toIRInference' turns @... else main@ into a @main_prob@ call with an
-- unchanged argument, which re-enters this same enumeration and never returns.
-- That is the shape 'requireDeterministicUnderEnum' was written for (task
-- self-recursive-prob-nondeterministic-fallback). A call to any recursive
-- function is refused, not only one reaching back into the function being
-- compiled: 'CompilerMetadata' does not know which one that is, and refusing
-- more keeps the old verdict rather than risking a non-terminating body.
forwardOrInfer :: CompilerMetadata -> Bool -> Expr -> IRExpr
               -> [(String, Expr, IRExpr)] -> CompilerMonad PResult -> CompilerMonad PResult
forwardOrInfer meta cumulative whole sample operands forward
  | all (null . randomDrawSites (detGenNames meta) . thd3) operands = forward
  | otherwise = do
      mapM_ (\(what, src, ir) -> requireDeterministicUnderEnum meta what src ir) operands
      res <- toIRInference meta cumulative (reinferRecovered meta (recoveredVars meta) whole) sample
      -- A delegated body can be a density (@if b then Normal else Normal +
      -- 3.0@), and whether it is one is in general a RUNTIME fact: @(x,
      -- Uniform)@ is a mass exactly when the query marginalises the second
      -- slot with @ANY@ (the fuzz-found @enumDeadLetFreshDrawTuple@ reaches
      -- this through @fst@), and topK pruning makes the dim a runtime choice
      -- even where it would otherwise fold. The enclosing enumerated sums
      -- keep their terms' dims ('enumTerm', 'enumMinDimP'; task
      -- enumerated-sum-over-density-body), so the result is returned as it
      -- is -- unless one of them sums its terms as masses ('dimAwareEnum'
      -- off: its body's type has no static dim bound, a list of reals). Then
      -- the probability is guarded at run time: a possible result with a
      -- non-zero dim raises instead of being summed as a mass. The guard is
      -- also skipped where it is statically true -- a cumulative result (a
      -- CDF value is a mass by construction), or a type with no 'TFloat'
      -- leaf, which no density ever measures -- and the optimizer folds it
      -- away where the dim is a literal 0.
      if cumulative || floatFree (adtDecls meta) (rType (getTypeInfo whole)) || dimAwareEnum meta
        then return res
        else do
          let isMass = orIR (rImposs res) (IROp OpEq (rDim res) dim0)
              refusal = IRError $ "probability-mode inference of an enumerated conditional (chain name "
                          ++ chainName (getTypeInfo whole) ++ ") met a continuous density: given the"
                          ++ " enumerated latents the query measures a fresh continuous draw, and an"
                          ++ " enumerated sum over density-valued terms of a type with no static dim bound"
                          ++ " (a list of reals) is not implemented (tasks enum-let-latent-gates-fresh-draw,"
                          ++ " enumerated-sum-over-density-body)"
          return (onProb (\p -> IRIf isMass p refusal) res)
  where thd3 (_, _, x) = x

-- | A static upper bound on the dim of a point probability of a value of the
-- type: its number of real leaves, the larger alternative for a sum type.
-- 'Nothing' when there is none (a list or tensor of reals, a recursive ADT
-- with a real field) or the type is not recognised. Used by the enumerated
-- sums ('enumSumTerms') to find the lowest dim among their terms
-- ('enumMinDimP'), which needs the bound to build its ladder.
floatLeafBound :: [ADTDecl] -> RType -> Maybe Int
floatLeafBound decls = go Set.empty
  where
    go seen t
      | floatFree decls t = Just 0
      | otherwise = case t of
          TFloat -> Just 1
          Tuple a b -> (+) <$> go seen a <*> go seen b
          TEither a b -> max <$> go seen a <*> go seen b
          TADT n
            | Set.member n seen -> Nothing
            | otherwise -> case find ((== n) . dataName) decls of
                Just d -> fmap (maximum . (0 :)) $ sequence
                            [ sum <$> mapM (go (Set.insert n seen) . snd) fs | (_, fs) <- constructors d ]
                Nothing -> Nothing
          _ -> Nothing

-- | True when no value of the type contains a 'TFloat' leaf, so a point
-- probability of it is always a mass (dim 0). Conservative: anything it does
-- not recognise (arrows, type variables, an unknown ADT) answers 'False'.
floatFree :: [ADTDecl] -> RType -> Bool
floatFree decls = go Set.empty
  where
    go seen t = case t of
      TBool -> True
      TInt -> True
      TSymbol -> True
      TUnit -> True
      ListOf a -> go seen a
      TTensor _ a -> go seen a
      Tuple a b -> go seen a && go seen b
      TEither a b -> go seen a && go seen b
      TADT n
        | Set.member n seen -> True
        | otherwise -> case find ((== n) . dataName) decls of
            Just d -> and [ go (Set.insert n seen) ft | (_, fs) <- constructors d, (_, ft) <- fs ]
            Nothing -> False
      _ -> False
