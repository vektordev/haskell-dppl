{-# LANGUAGE ScopedTypeVariables #-}
module SPLL.IROptimizer (
  optimizeEnv
, postProcess
, failConversion
, OptStats(..)
, OptEnv(..)
, optimizeStats
, deterministicGens
, distributeIf
, headHash
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.Number.Erf (erf)
import Data.Bits (xor)
import Data.List (maximumBy, foldl', findIndex, partition, intercalate)
import Data.Ord (comparing)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (State, runState, get, put, modify')
import Debug.Trace (trace)
import SPLL.Lang.Lang (floatApproxEqThresh)


optimizeEnv :: CompilerConfig -> IREnv -> IREnv
optimizeEnv conf (IREnv funcs adtsDecl consts) = reportStats conf report (IREnv funcs' adtsDecl consts)
  where
    optGroup :: IRFunGroup -> State [(String, OptStats)] IRFunGroup
    (funcs', report) = runState (mapM optGroup funcs) []
    -- Bound once for the whole environment, not per function.
    det = OptEnv (deterministicGens funcs)
                 (Set.fromList ["is" ++ cn | d <- adtsDecl, (cn, _) <- constructors d])
    optGroup fg = do
      g <- onFun (groupName fg ++ "_gen")   (genFun fg)
      pr <- onFun (groupName fg ++ "_prob")  (probFun fg)
      i <- onFun (groupName fg ++ "_integ") (integFun fg)
      e <- onFun (groupName fg ++ "_writeLogits") (writeLogitsFun fg)
      n <- onFun (groupName fg ++ "_normal") (normalFun fg)
      return fg { genFun = g, probFun = pr, integFun = i, writeLogitsFun = e, normalFun = n }
    onFun :: String -> Maybe IRFunDecl -> State [(String, OptStats)] (Maybe IRFunDecl)
    onFun _ Nothing = return Nothing
    onFun label (Just (expr, doc)) = do
      let (expr', st) = postProcessStats conf det expr
      modify' ((label, st) :)
      return (Just (expr', doc))

postProcess :: CompilerConfig -> IRExpr -> IRExpr
--postProcess = id
postProcess conf = fst . postProcessStats conf (OptEnv Set.empty Set.empty)

-- | 'postProcess' told which generate functions are deterministic, so the
-- duplicating and sharing rewrites can treat calls to them as pure, plus the
-- telemetry the run produced.
-- | Run the optimizer to a fixed point, keeping the near-idempotent stages out
-- of the loop.
--
-- Telemetry (@--optStats@) over the whole corpus shows a sharp split in how much
-- work each rule finds after the first pass. Five rules essentially never find
-- more -- @applyToLetIn@ 2589 firings in pass 1 against 17 in all later passes
-- combined, @applyConstant@ 772 against 1, @propagateAnyGuard@ 517 against 3,
-- @associativity@ 9 against 4, @indexMagic@ 51 against 0 -- while the rest keep
-- finding work in proportion (@simplify@ 67147 against 10211, @letIn@ 53196
-- against 2246, @cse@ 3911 against 2025). Running the first group on every
-- iteration costs a full traversal each time to rewrite almost nothing.
--
-- So the first pass runs everything, later passes run only 'loopStage' rules,
-- and when those settle the 'onceStage' rules get one verification pass.
-- "Almost nothing" is not "nothing", so that pass is a real check rather than an
-- assertion: if it does find work, the loop is re-entered and the run is tallied
-- as a recheck ('statRechecks', reported by @--optStats@). The result is
-- therefore a fixed point of the same combined rule set as before -- the split
-- changes the route, never the destination -- while the rare programs that need
-- the extra rounds stay visible instead of being silently under-optimized.
postProcessStats :: CompilerConfig -> OptEnv -> IRExpr -> (IRExpr, OptStats)
postProcessStats conf det e0 = go 1 [] 0 AllStages e0
  where
    go n acc rechecks set e =
      let (e', tally) = optimizeStats' conf det set e
      in if e' /= e
           then go (n + 1) (tally : acc) rechecks LoopStages e'
           else case set of
             -- The reduced loop has settled; give the once-only rules their pass.
             LoopStages ->
               let (e'', residue) = optimizeStats' conf det OnceStagesOnly e
               in if e'' == e
                    then done n acc rechecks e
                    else go (n + 1) (residue : acc) (rechecks + 1) LoopStages e''
             -- The very first pass changed nothing, so nothing can have work.
             _ -> done n acc rechecks e
    -- The last iteration is the one that proved the fixed point: counted, but by
    -- definition it rewrote nothing, so its empty tally is not listed.
    done n acc rechecks e = (e, OptStats n (reverse acc) rechecks)

-- | What one optimizer run did, for @--optStats@. 'statIterations' counts every
-- pass including the final no-change one that established the fixpoint;
-- 'statPerIteration' holds the rules that fired in each of the earlier ones.
data OptStats = OptStats
  { statIterations   :: !Int
  , statPerIteration :: [Tally]
    -- | How many times the post-loop verification pass found work for a rule the
    -- loop had stopped running, so the loop had to be re-entered. Expected to be
    -- 0 for almost every program; a nonzero count names a program whose shape
    -- keeps feeding one of the 'onceStage' rules.
  , statRechecks     :: !Int
  } deriving (Show)

-- | How many nodes each named rewrite rule changed during one pass.
type Tally = Map.Map String Int

-- | Emit the telemetry as a trace, then hand back the environment unchanged.
reportStats :: CompilerConfig -> [(String, OptStats)] -> IREnv -> IREnv
reportStats conf report env
  | not (optStats conf) = env
  | otherwise           = trace (unlines (summary ++ detail)) env
  where
    entries = reverse report
    iters = map (statIterations . snd) entries
    rechecks = sum (map (statRechecks . snd) entries)
    total = Map.unionsWith (+) (concatMap (statPerIteration . snd) entries)
    summary =
      [ "=== Optimizer telemetry (-O" ++ show (optimizerLevel conf) ++ ") ==="
      , "  " ++ show (length entries) ++ " function bodies, "
          ++ show (sum iters) ++ " fixed-point iterations total"
          ++ (if null iters then "" else ", max " ++ show (maximum iters)
               ++ " (" ++ fst (maximumBy (comparing (statIterations . snd)) entries) ++ ")")
      ] ++ [ "  rules fired: " ++ showTally total | not (Map.null total) ]
        ++ [ "  once-only check re-entered the loop " ++ show rechecks ++ " time(s): "
               ++ intercalate ", " [l | (l, st) <- entries, statRechecks st > 0]
           | rechecks > 0 ]
    detail
      | verbose conf < 1 = []
      | otherwise = concatMap perFun entries
    perFun (label, OptStats n tallies _) =
      ("  " ++ label ++ ": " ++ show n ++ " iteration(s)")
        : [ "    iteration " ++ show i ++ ": " ++ showTally t
          | (i, t) <- zip [(1 :: Int) ..] tallies, not (Map.null t) ]
    showTally t = intercalate ", " [k ++ "=" ++ show v | (k, v) <- Map.toList t]

-- | Whole-program facts the local rewrites consult. Both are conservative
-- over-approximations of "nothing": an empty 'OptEnv' makes every rewrite fall
-- back to what it did before these analyses existed.
data OptEnv = OptEnv
  { -- | Generate functions proven not to draw randomness, so a call to one may
    -- be shared or duplicated ('isPureGiven').
    optDetGens :: Set.Set Varname
    -- | The compiler-generated @is\<Ctor\>@ constructor tests. They return a
    -- Bool, so an @isAny@ over a call to one is statically False -- which an
    -- 'IRApply' cannot be told on its own, since a user function may well
    -- return the ANY sentinel.
  , optCtorTests :: Set.Set Varname
  }

-- | The @_gen@ functions whose evaluation draws no randomness, so that sharing
-- or duplicating a reference to one cannot collapse or multiply a random draw.
--
-- A generate function is deterministic when its own body holds no 'IRSample'
-- and every generator it references is itself deterministic. That is a mutual
-- condition, so it is computed as a greatest fixpoint: assume all of them are
-- deterministic, then repeatedly drop any whose body refutes the assumption.
-- Starting optimistic is what admits mutually recursive groups; starting from
-- the empty set would never let a self-recursive generate function in.
--
-- A generator this analysis cannot see (a name with no group, e.g. a neural
-- @_auto_gen@ wrapper, which samples from the read-logits network anyway) is absent from
-- the candidate set and therefore refutes any body mentioning it -- the same
-- answer 'isEffectfulVar' alone would have given.
deterministicGens :: [IRFunGroup] -> Set.Set Varname
deterministicGens funcs = fixedPointIteration shrink candidates
  where
    named = [(groupName fg ++ "_gen", body) | fg <- funcs, Just (body, _) <- [genFun fg]]
    candidates = Set.fromList (map fst named)
    shrink live = Set.fromList [n | (n, body) <- named, Set.member n live, isPureGiven live body]

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

-- | One optimizer pass, plus a count of how many nodes each rewrite rule
-- changed. The tally is what @--optStats@ reports; a rule is credited once per
-- node whose value it altered, so a stage that is idempotent with respect to
-- everything else in the pipeline shows a zero tally in every iteration after
-- the first -- which is the evidence needed before lifting a stage out of the
-- fixed point.
--
-- CSE runs as a whole-expression pass (not per-node via irMap) so it can hand
-- out globally-unique binding names; running it per node lets the same name be
-- reused at different nesting levels, which produces shadowing bugs.
-- | Which stages a pass runs. See 'postProcessStats' for why the split exists.
data StageSet
  = AllStages       -- ^ the first pass
  | LoopStages      -- ^ every later pass
  | OnceStagesOnly  -- ^ the post-loop idempotence check
  deriving (Eq)

optimizeStats :: CompilerConfig -> OptEnv -> IRExpr -> (IRExpr, Tally)
optimizeStats conf det = optimizeStats' conf det AllStages

optimizeStats' :: CompilerConfig -> OptEnv -> StageSet -> IRExpr -> (IRExpr, Tally)
optimizeStats' conf det stages e0 = runState (nodeWise e0 >>= commonSubexprStage) Map.empty
  where
    nodeWise = irMapM (\e ->
      pruneAnyCkecksStage e
        >>= lambdaApplicationStage
        >>= distributeConditionals
        >>= indexStage
        >>= anyGuardStage
        >>= simplifyStage
        >>= constantDistrStage
        >>= letInStage
        >>= assiciativityStage
        >>= applyConstStage)
    oLvl = optimizerLevel conf
    -- A rule that has more to do once other rules have run: it stays in the loop.
    loopStage name enabled = mkStage name (enabled && stages /= OnceStagesOnly)
    -- A rule believed to reach its fixed point in the first pass. Runs in the
    -- first pass and in the check, never in the loop.
    onceStage name enabled = mkStage name (enabled && stages /= LoopStages)
    mkStage name enabled f = if enabled then counted name f else return
    commonSubexprStage =
      if oLvl >= 2 && stages /= OnceStagesOnly
        then countedBy "cse" (optimizeCommonSubexprCounted det)
        else return
    applyConstStage = onceStage "applyConstant" (oLvl >= 2) applyConstant
    assiciativityStage = onceStage "associativity" (oLvl >= 2) optimizeAssociativity
    indexStage = onceStage "indexMagic" (oLvl >= 1) indexmagic
    anyGuardStage = onceStage "propagateAnyGuard" (oLvl >= 1) propagateAnyGuard
    lambdaApplicationStage = onceStage "applyToLetIn" (oLvl >= 2) applyToLetIn
    letInStage = loopStage "letIn" (oLvl >= 2) (optimizeLetIns det)
    constantDistrStage = loopStage "constantDistr" (oLvl >= 2) evalConstantDistr
    simplifyStage = loopStage "simplify" (oLvl >= 1) (simplify det)
    distributeConditionals = loopStage "distributeIf" (oLvl >= 2) (distributeIf det (oLvl >= 3))
    -- No telemetry either way (it only runs under --pruneAnyChecks), so it keeps
    -- the conservative placement.
    pruneAnyCkecksStage = loopStage "pruneAnyChecks" (pruneAnyChecks conf) pruneAnyCkecksExpr

-- | Run a rewrite and record whether it changed the node.
counted :: String -> (IRExpr -> IRExpr) -> IRExpr -> State Tally IRExpr
counted name f = countedBy name (\e -> let e' = f e in (e', if e' == e then 0 else 1))

-- | 'counted' for a rewrite that reports its own amount of work.
countedBy :: String -> (IRExpr -> (IRExpr, Int)) -> IRExpr -> State Tally IRExpr
countedBy name f e = do
  let (e', n) = f e
  if n == 0 then return () else modify' (Map.insertWith (+) name n)
  return e'

-- | The monadic 'irMap': bottom-up, so a rewrite sees children already rewritten.
irMapM :: Monad m => (IRExpr -> m IRExpr) -> IRExpr -> m IRExpr
irMapM f x = irDescendM (irMapM f) x >>= f

indexmagic :: IRExpr -> IRExpr
-- if calling Apply ("indexOf") elem [0..], replace with elem
indexmagic (IRApply (IRApply (IRVar "indexOf") elemExpr) (IRConst (VList list)))
  | isNaturals valList = elemExpr
  | Just vals <- constEnumList valList = indexOfChain elemExpr vals
  where
    valList = toList list
    isNaturals lst = and (zipWith (==) [0..] (map toNatural lst))
    toNatural (VInt x) = x
    toNatural _ = -1 -- not a natural number, should fail the above.
indexmagic x = x

-- | A non-naturals enumeration constant (e.g. [False, True] or [3, 7, 11]) that
-- indexmagic's fast path above doesn't fold: every element is a scalar constant
-- (Bool/Int) so equality against it is cheap and unambiguous. Used to fold
-- `indexOf elem [..]` into a chain of equality comparisons below, which keeps the
-- enum-index lookup an elementwise IRIf chain (select-pass/batching eligible)
-- rather than surviving to codegen as a call to the linked-list-walking stdlib
-- `indexOf`, whose `VList` argument has no batched representation
-- (task batched-bool-enum-index).
constEnumList :: [IRValue] -> Maybe [IRValue]
constEnumList lst@(_:_) | all isScalarConst lst = Just lst
  where
    isScalarConst (VBool _) = True
    isScalarConst (VInt _) = True
    isScalarConst _ = False
constEnumList _ = Nothing

-- | indexOf elem [v0, v1, .., vn] ~> if elem == v0 then 0 else if elem == v1 then 1
-- else .. else n. The last element needs no comparison: indexOf's own contract
-- (StandardLibrary.stdIndexOf) is a total function only when elem is a member of
-- the list, so falling through to the final index is sound whenever this fold's
-- caller relied on that same guarantee (as SPLL.AutoNeural.indexOf's callers do).
indexOfChain :: IRExpr -> [IRValue] -> IRExpr
indexOfChain _ [] = IRError "indexOf: empty enumeration"
indexOfChain elemExpr vals = go (zip [0 ..] vals)
  where
    go [(i, _)] = IRConst (VInt i)
    go ((i, v) : rest) = IRIf (IROp OpEq elemExpr (IRConst v)) (IRConst (VInt i)) (go rest)
    go [] = IRError "indexOf: empty enumeration"

-- A tuple of conditionals sharing one condition can be hoisted into a single
-- conditional over tuples, e.g. (if c then x else y, if c then z else w) becomes
-- if c then (x, z) else (y, w).  Generalised to any nesting of IRTCons: whenever
-- every leaf of the tuple tree is an IRIf with the same condition, pull that
-- condition out and split the tree into a then-tree and an else-tree.
-- | Pull a condition shared by a tuple's leaves out to the front of the tuple:
-- @(if c then a else b, if c then x else y)@ becomes
-- @if c then (a, x) else (b, y)@.
--
-- The @mergeOverConstants@ flag (-O3) also admits tuples whose remaining leaves
-- are constants, copying those into both arms. That case is what re-unites
-- 'PResult' fields split across tuple slots: a probability and the
-- impossibility flag derived from it start out sharing one let-bound value, but
-- packing them into a result tuple gives each slot its own copy of the
-- condition and hence a single use of the binding, which 'optimizeLetIns'
-- inlines -- so the shared value is recomputed per slot. Merging the arms puts
-- both back in one straight-line region where CSE can share them again. The
-- constant slots in between (a statically-known dim of 0, a branch count of 0)
-- are exactly what makes the strict form refuse.
--
-- It is off below -O3 because it is a compile-time-for-run-time trade, not a
-- free win: hoisting conditionals outward exposes far more material to the CSE
-- scan. Measured on the corpus it cuts emitted code ~13% and halves the
-- enumerated work in neural-enumeration programs, while
-- @testCases/planEnumRecDeepCount.ppl@ goes from 1.2s to 9.0s to compile.
--
-- The shared condition must be __pure__ ('isPureGiven'), for the same reason
-- CSE and 'optimizeLetIns' consult purity (tasks ir-effectful-var-purity,
-- stochastic-call-cse-unsound): the rewrite keeps one copy of a condition that
-- the tuple evaluated once per leaf, so an effectful condition would have its
-- draws fused. @(if Uniform < 0.5 then 1 else 2, if Uniform < 0.5 then 1 else
-- 2)@ is two independent coin flips in the source and the two syntactically
-- equal conditions are two distinct draws in the IR; distributing them made the
-- mixed outcomes @(1,2)@ and @(2,1)@ unreachable, silently and with no crash.
distributeIf :: OptEnv -> Bool -> IRExpr -> IRExpr
distributeIf det mergeOverConstants e
  | isTupleShape e, leavesShareCond = IRIf cond (mapTupleLeaves ifThen e) (mapTupleLeaves ifElse e)
  where
    -- 'IRConstruct TgTuple' (design ir-reengineering, slice S1a) is dead code
    -- today; this guard is what lets it fire the rule above once a producer
    -- migrates, without a second copy of the whole equation.
    isTupleShape (IRTCons _ _) = True
    isTupleShape (IRConstruct TgTuple _) = True
    isTupleShape _ = False
    leaves = tupleTreeLeaves e
    conds = [c | IRIf c _ _ <- leaves]
    nonConditional = [l | l <- leaves, not (isConditional l)]
    isConditional (IRIf _ _ _) = True
    isConditional _            = False
    leavesShareCond = not (null conds)
      && all (== head conds) (tail conds)
      && isPureGiven (optDetGens det) (head conds)
      && if mergeOverConstants
           then length conds >= 2 && all isValue nonConditional
           else null nonConditional
    cond = head conds
    ifThen (IRIf _ t _) = t
    ifThen x = x
    ifElse (IRIf _ _ el) = el
    ifElse x = x
distributeIf _ _ x = x

-- | The leaves of a tree of nested IRTCons (everything that is not itself an IRTCons).
tupleTreeLeaves :: IRExpr -> [IRExpr]
tupleTreeLeaves (IRTCons a b) = tupleTreeLeaves a ++ tupleTreeLeaves b
tupleTreeLeaves (IRConstruct TgTuple [a, b]) = tupleTreeLeaves a ++ tupleTreeLeaves b
tupleTreeLeaves x = [x]

-- | Rebuild a tree of nested IRTCons, applying f to each leaf.
mapTupleLeaves :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
mapTupleLeaves f (IRTCons a b) = IRTCons (mapTupleLeaves f a) (mapTupleLeaves f b)
mapTupleLeaves f (IRConstruct TgTuple [a, b]) = IRConstruct TgTuple [mapTupleLeaves f a, mapTupleLeaves f b]
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

optimizeLetIns :: OptEnv -> IRExpr -> IRExpr
optimizeLetIns det (IRLetIn name val scope)
  -- A binding may be inlined into *every* use (i.e. duplicated) only when doing so
  -- is both cheap and effect-free. `duplicableBinding` is the gate: IRConst
  -- (small, pure) and pure copy-propagations of a bare IRVar qualify. Effectfulness
  -- is decided by the shared `isPure` mechanism rather than the old
  -- "IRConst only" rule -- a bare IRVar can name a nullary generator (e.g.
  -- coin_gen) whose evaluation samples randomness, so inlining it into multiple
  -- uses would re-draw the sample (task ir-effectful-var-purity). Multi-use
  -- non-duplicable bindings stay as a let; single use is still inlined below.
  | duplicableBinding det val = replaceAll (IRVar name) val scope
  | countUses name scope == 1 && not (usedInEnumSumBodyInvariant name val scope) = replaceAll (IRVar name) val scope
  | countUses name scope == 0 = scope
optimizeLetIns _ ex = ex

-- | A binding whose value may be duplicated across all uses without changing
-- semantics or blowing up code size: a literal constant, or a pure bare
-- variable reference (copy propagation). The purity check is what keeps an
-- effectful generator reference (@coin_gen@) from being duplicated
-- (ir-effectful-var-purity).
duplicableBinding :: OptEnv -> IRExpr -> Bool
duplicableBinding det val = isValue val || (isBareVar val && isPureGiven (optDetGens det) val)
  where isBareVar (IRVar _) = True
        isBareVar _         = False

-- | An /iterating/ form: one whose body is evaluated once per element of a
-- domain, together with the variable it binds over that body. This is the one
-- place that knows which constructors iterate; the analyses below are written
-- against it rather than re-matching the constructor set each time, which is
-- how the enum-sum family came to be spelled out in four separate walks
-- (design ir-tensor-values).
--
-- Note what is deliberately /not/ here: a bare 'IRLambda'. A lambda's body is
-- evaluated once per application, which is usually once, so treating every
-- lambda as a loop would change hoisting decisions for every program with a
-- lambda in it -- a behaviour change well beyond adding a dense axis. A
-- 'BMap''s lambda /is/ listed, because a map applies it once per element by
-- construction.
loopBinder :: IRExpr -> Maybe (Varname, IRExpr)
loopBinder (IREnumSum n _ body) = Just (n, body)
loopBinder (IRLogEnumSum n _ body) = Just (n, body)
loopBinder (IREnumSumPaired _ n _ body) = Just (n, body)
loopBinder (IRBuiltin BMap [IRLambda n body, _]) = Just (n, body)
loopBinder _ = Nothing

-- | True if `var` is used inside an iterating body in `scope` AND `val` does not
-- reference any loop variable of those forms.  Such a binding is
-- loop-invariant and should be hoisted rather than inlined into the loop body.
usedInEnumSumBodyInvariant :: String -> IRExpr -> IRExpr -> Bool
usedInEnumSumBodyInvariant var val scope =
  usedInEnumSumBody var scope &&
  all (\loopVar -> countUses loopVar val == 0) (enumSumBoundVars scope)

-- | True if `var` appears free inside at least one iterating body in `expr`.
usedInEnumSumBody :: String -> IRExpr -> Bool
usedInEnumSumBody var expr = case loopBinder expr of
  Just (_, body) -> countUses var body > 0
  Nothing -> any (usedInEnumSumBody var) (getIRSubExprs expr)

-- | Collect all variables bound by an iterating form in an expression.
enumSumBoundVars :: IRExpr -> [String]
enumSumBoundVars expr = case loopBinder expr of
  Just (n, _) -> n : rest
  Nothing -> rest
  where rest = concatMap enumSumBoundVars (getIRSubExprs expr)

evalConstantDistr :: IRExpr -> IRExpr
evalConstantDistr (IRDensity IRNormal Linear (IRConst (VFloat x))) = IRConst (VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x)))
evalConstantDistr (IRCumulative IRNormal Linear (IRConst (VFloat x))) = IRConst (VFloat ((1/2) * (1 + erf (x/sqrt (2)))))
evalConstantDistr (IRDensity IRUniform Linear (IRConst (VFloat x))) = IRConst (VFloat (if x >= 0 && x <= 1 then 1 else 0))
evalConstantDistr (IRCumulative IRUniform Linear (IRConst (VFloat x))) = IRConst (VFloat (if x < 0 then 0 else if x > 1 then 1 else x))
evalConstantDistr (IRDensity IRNormal Log (IRConst (VFloat x))) = IRConst (VFloat ((-0.5) * x * x - 0.5 * log (2 * pi)))
evalConstantDistr (IRCumulative IRNormal Log (IRConst (VFloat x))) = IRConst (VFloat (log ((1/2) * (1 + erf (x/sqrt (2))))))
evalConstantDistr (IRDensity IRUniform Log (IRConst (VFloat x))) = IRConst (VFloat (if x >= 0 && x <= 1 then 0 else (-1)/0))
evalConstantDistr (IRCumulative IRUniform Log (IRConst (VFloat x))) = IRConst (VFloat (log (if x < 0 then 0 else if x > 1 then 1 else x)))
evalConstantDistr x = x

simplify :: OptEnv -> IRExpr -> IRExpr
simplify _ (IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | isValue leftV || isValue rightV = softForceLogic op leftV rightV
-- Mask fusion: a semiring indicator times a value becomes a branch on the
-- indicator's condition, so the value is evaluated only where the indicator
-- admits it. 'indicatorP' (via 'maskSR') builds exactly this shape, and
-- 'prodP' multiplies it against whatever the branch costs -- in an enumerated
-- sum, the per-world density. Without the fusion every enumerated world pays
-- that density and then multiplies it by zero; with it, only the worlds the
-- indicator selects pay. Strictly smaller IR as well as strictly less work.
--
-- Only fired for a pure operand: making evaluation conditional must not drop
-- an IRSample draw. Dropping a value that would have been multiplied by the
-- semiring zero is the same licence 'softForceLogic' already takes for
-- @0 * x@.
simplify det (IROp op left right)
  | Just (c, z) <- semiringMask op left, isPureGiven (optDetGens det) right = IRIf c right z
  | Just (c, z) <- semiringMask op right, isPureGiven (optDetGens det) left = IRIf c left z
simplify det (IRUnaryOp OpIsAny x) = forceAnyCheck det x
simplify _ (IRUnaryOp op val) | isValue val = IRConst $ forceUnaryOp op (unval val)
simplify _ (IRIf _ left right) | left == right = left
simplify _ x@(IRIf cond left right) =
  if isValue cond
    then if unval cond == VBool True
      then left
      else right
    else x
-- The same two foldings are sound for a select (pytorch-tensorizer M1): equal
-- arms collapse to that value, and a constant mask picks one arm -- both hold
-- whether one arm is taken (scalar) or both are computed and masked (batched),
-- so unlike distributeIf these are safe to fire on IRSelect. They keep batched
-- code from bloating when the select pass converts constant-conditioned ifs.
simplify _ (IRSelect _ left right) | left == right = left
simplify _ x@(IRSelect cond left right) =
  if isValue cond
    then if unval cond == VBool True
      then left
      else right
    else x
simplify _ x@(IRCons left right) =
  case (isValue left && isValue right, unval right) of
    -- A non-list tail is ill-typed rather than merely unsimplifiable, but the
    -- optimizer is not the place to reject it: leave the cons alone.
    (True, VList tl) -> IRConst (VList (ListCont (unval left) tl))
    _ -> x
simplify _ (IRHead (IRCons a _)) = a
simplify _ (IRTail (IRCons _ b)) = b
simplify _ (IRTFst (IRTCons a _)) = a
simplify _ (IRTSnd (IRTCons _ b)) = b
-- The new-shape counterparts (design ir-reengineering, slice S1a): dead code
-- today (nothing constructs 'IRConstruct'/'IRDestruct' yet), added alongside
-- the old-shape rules above so a future producer slice gets these folds for
-- free rather than silently losing them.
simplify _ x@(IRConstruct TgCons [left, right]) =
  case (isValue left && isValue right, unval right) of
    (True, VList tl) -> IRConst (VList (ListCont (unval left) tl))
    _ -> x
simplify _ (IRDestruct AcHead (IRConstruct TgCons [a, _])) = a
simplify _ (IRDestruct AcTail (IRConstruct TgCons [_, b])) = b
simplify _ (IRDestruct AcFst  (IRConstruct TgTuple [a, _])) = a
simplify _ (IRDestruct AcSnd  (IRConstruct TgTuple [_, b])) = b
--simplify (IRHead (IRConst (VList (ListCont a _)))) = IRConst a
--simplify (IRTail (IRConst (VList (ListCont _ a)))) = IRConst (VList a)
simplify _ x = x

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
-- The new-shape counterpart (design ir-reengineering, slice S1a): dead code
-- today, added for parity with the rule above.
softForceLogic OpEq (IRConstruct TgCons _) (IRConst (VList EmptyList)) = IRConst $ VBool False
softForceLogic OpEq (IRConst (VList EmptyList)) (IRConstruct TgCons _) = IRConst $ VBool False
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

-- | Recognise @op@ applied to a semiring indicator: linear @(if c then 1 else
-- 0) * x@, or its log-space twin @(if c then 0 else -inf) + x@ (log-space
-- multiplication is addition, and the log of zero is negative infinity).
-- Returns the condition and the semiring zero to fall back to.
semiringMask :: Operand -> IRExpr -> Maybe (IRExpr, IRExpr)
semiringMask OpMult (IRIf c one zero@(IRConst z))
  | isValue one, isNumOne (unval one), isNumZero z = Just (c, zero)
semiringMask OpPlus (IRIf c zero negInf@(IRConst n))
  | isValue zero, isNumZero (unval zero), isNegInf n = Just (c, negInf)
semiringMask _ _ = Nothing

-- | The log-space semiring zero.
isNegInf :: IRValue -> Bool
isNegInf (VFloat x) = isInfinite x && x < 0
isNegInf _ = False

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
-- Same policy as forceOp: an operation on ANY is an unreachable path being
-- folded, not a real negation.
forceUnaryOp OpNot VAny = VAny
forceUnaryOp OpExp (VFloat x) = VFloat (exp x)
forceUnaryOp OpLog (VFloat x) = VFloat (log x)
forceUnaryOp _ _ = error "Error during forceUnaryOp optimizer"


--TODO

forceAnyCheck :: OptEnv -> IRExpr -> IRExpr
forceAnyCheck _ x | isValue x = IRConst $ VBool (unval x == VAny || unval x == VList AnyList)
forceAnyCheck _ (IRCons _ _) = IRConst $ VBool False  -- Lists can never be any
forceAnyCheck _ (IRTCons _ _) = IRConst $ VBool False -- Tuples can never be any
forceAnyCheck _ (IRLeft _) = IRConst $ VBool False -- Eithers can never be any
forceAnyCheck _ (IRRight _) = IRConst $ VBool False -- Eithers can never be any
-- The new-shape counterpart (design ir-reengineering, slice S1a): dead code
-- today, but one arm covers all four 'ConTag's at once -- a computed
-- construct of any tag can never be the ANY sentinel, same reasoning as the
-- four old-shape rules above.
forceAnyCheck _ (IRConstruct _ _) = IRConst $ VBool False
-- A computed scalar is never the ANY sentinel. ANY reaches an expression only
-- as a query value -- an IRConst VAny or a parameter carrying one -- and does
-- NOT propagate through arithmetic: every operator case in 'IRInterpreter'
-- errors on a VAny operand rather than returning VAny (the propagating cases
-- are present but commented out), and the Python/Julia runtimes likewise raise
-- on arithmetic against the sentinel. So an operator, a distribution leaf, a
-- draw or an enumerated sum is statically not-ANY, and the check guarding it
-- collapses -- which matters because that check is typically the second copy
-- of the whole value expression it tests, next to the equality it guards.
forceAnyCheck _ (IROp _ _ _) = IRConst $ VBool False
forceAnyCheck _ (IRUnaryOp _ _) = IRConst $ VBool False
forceAnyCheck _ (IRDensity _ _ _) = IRConst $ VBool False
forceAnyCheck _ (IRCumulative _ _ _) = IRConst $ VBool False
forceAnyCheck _ (IRSample _) = IRConst $ VBool False
forceAnyCheck _ (IREnumSum _ _ _) = IRConst $ VBool False
forceAnyCheck _ (IRLogEnumSum _ _ _) = IRConst $ VBool False
forceAnyCheck _ (IREnumSumPaired _ _ _ _) = IRConst $ VBool False
-- A tensor is a computed aggregate and a reduction of one is a computed
-- scalar; neither can be the ANY sentinel, for the same reason the enumerated
-- sums above cannot. 'BIndex' is deliberately absent: it reads back an element
-- someone else put in the tensor, so it is only not-ANY if that value was,
-- which is not decidable here -- it falls through to a real runtime check.
forceAnyCheck _ (IRBuiltin (BTensor _) _) = IRConst $ VBool False
forceAnyCheck _ (IRBuiltin BMap _) = IRConst $ VBool False
forceAnyCheck _ (IRBuiltin (BReduce _ _) _) = IRConst $ VBool False
-- Push the check through the binding forms, so a scalar body above can decide
-- it. Only kept when it actually decided: otherwise this would just relocate
-- the test (and, for an if, duplicate it).
forceAnyCheck env (IRLetIn n v b)
  | IRConst c <- forceAnyCheck env b = IRLetIn n v (IRConst c)
forceAnyCheck env (IRIf c t e)
  | IRConst t' <- forceAnyCheck env t
  , IRConst e' <- forceAnyCheck env e = IRIf c (IRConst t') (IRConst e')
-- A constructor test is Bool-valued. Only these calls fold: an arbitrary
-- 'IRApply' may return the sentinel it was handed.
forceAnyCheck env (IRApply (IRVar f) _)
  | f `Set.member` optCtorTests env = IRConst $ VBool False
forceAnyCheck _ x = IRUnaryOp OpIsAny x
-- Maybe more, I am not quite sure

-- | Inside @if isAny(v) then .. else ..@, another @isAny(v)@ is decided: True
-- in the then-arm, False in the else-arm. The compiler emits these guards at
-- every level ('anySafe' wraps each result, and each leaf adds its own), so a
-- nested one re-tests what the enclosing branch already established -- and the
-- dead arm it selects is often another copy of the value expression.
--
-- Restricted to a check on a bare variable so the substitution is a cheap
-- structural match, and skipped under any binder that shadows that variable.
propagateAnyGuard :: IRExpr -> IRExpr
propagateAnyGuard (IRIf c@(IRUnaryOp OpIsAny (IRVar v)) t e) =
  IRIf c (subst True t) (subst False e)
  where
    subst b = go
      where
        go x | x == c = IRConst (VBool b)
        go x | v `Set.member` binderOf x = x
        go x = irDescend go x
    binderOf (IRLetIn n _ _)      = Set.singleton n
    binderOf (IRLambda n _)       = Set.singleton n
    binderOf (IREnumSum n _ _)    = Set.singleton n
    binderOf (IRLogEnumSum n _ _) = Set.singleton n
    binderOf (IREnumSumPaired _ n _ _) = Set.singleton n
    binderOf _                    = Set.empty
propagateAnyGuard x = x

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
--   * pure — evaluating it has no side effect ('isPure', tracked as 'annImpure'):
--     no IRSample draw and no generator reference, so sharing a single value for
--     it cannot collapse distinct random draws;
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

-- | CSE plus the number of bindings it hoisted. Unlike the per-node rules this
-- is a whole-expression pass, so "fired once" would say nothing about how much
-- it did; the counter behind the fresh-name supply is the useful number.
-- (A name collision with an existing @cse_N@ -- possible from a previous
-- fixed-point iteration -- consumes a counter step without hoisting, so the
-- figure is an upper bound, off by the number of such collisions.)
optimizeCommonSubexprCounted :: OptEnv -> IRExpr -> (IRExpr, Int)
optimizeCommonSubexprCounted det topExpr = runState (scan (annotateIR det topExpr)) 0
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
      IRSelect{}      | [c, t, el] <- annKids a -> IRSelect <$> descendToScanRoots c <*> scan t <*> scan el
      IRLambda n _    | [b] <- annKids a -> IRLambda n <$> scan b
      IREnumSum n v _ | [b] <- annKids a -> IREnumSum n v <$> scan b
      IRLogEnumSum n v _ | [b] <- annKids a -> IRLogEnumSum n v <$> scan b
      IREnumSumPaired lg n v _ | [b] <- annKids a -> IREnumSumPaired lg n v <$> scan b
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
      IRSelect{}      | [c, t, el] <- annKids a -> IRSelect <$> route c <*> scan t <*> scan el
      IRLambda n _    | [b] <- annKids a -> IRLambda n <$> scan b
      IREnumSum n v _ | [b] <- annKids a -> IREnumSum n v <$> scan b
      IRLogEnumSum n v _ | [b] <- annKids a -> IRLogEnumSum n v <$> scan b
      IREnumSumPaired lg n v _ | [b] <- annKids a -> IREnumSumPaired lg n v <$> scan b
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
        let body = annReplace det sub (annotateIR det (IRVar name)) a
        extractHere (mkAnnIR det (IRLetIn name (annExpr sub) (annExpr body)) [sub, body])

-- | True if any of the given (hash, size) keys occurs at least twice in the
-- node's unconditional skeleton.
keysRepeatedIn :: Set.Set (Int, Int) -> AnnIR -> Bool
keysRepeatedIn keys annIR = any (>= (2 :: Int)) (Map.elems counts)
  where
    counts = Map.fromListWith (+)
      [ (k, 1) | a <- unconditionalAnns annIR
               , let k = (annHash a, annSize a)
               , k `Set.member` keys ]

-- | Subtree annotated with memoized structural facts, so repeats can be
-- counted by hash instead of pairwise tree comparison.
data AnnIR = AnnIR
  { annExpr    :: IRExpr
  , annKids    :: [AnnIR]
  , annHash    :: !Int
  , annSize    :: !Int      -- leaf count
  , annImpure  :: !Bool     -- evaluation has a side effect: an IRSample draw or
                            -- a generator reference (see 'isPure'). Sharing an
                            -- impure repeat would collapse independent draws.
  , annBound   :: Set.Set String  -- names bound by binders anywhere in the subtree
  }

annotateIR :: OptEnv -> IRExpr -> AnnIR
annotateIR det e = mkAnnIR det e (map (annotateIR det) (getIRSubExprs e))

-- | Annotate a node whose children are already annotated.
mkAnnIR :: OptEnv -> IRExpr -> [AnnIR] -> AnnIR
mkAnnIR det e kids = AnnIR e kids h sz smp bnd
  where
    h = foldl' hashMix (headHash e) (map annHash kids)
    sz = if null kids then 1 else sum (map annSize kids)
    smp = case e of
      IRSample _              -> True
      IRVar n | isEffectfulVar n, not (Set.member n (optDetGens det)) -> True
      _                       -> any annImpure kids
    kidsBound = Set.unions (map annBound kids)
    bnd = case e of
      IRLetIn n _ _   -> Set.insert n kidsBound
      IRLambda n _    -> Set.insert n kidsBound
      IREnumSum n _ _ -> Set.insert n kidsBound
      IRLogEnumSum n _ _ -> Set.insert n kidsBound
      IREnumSumPaired _ n _ _ -> Set.insert n kidsBound
      _               -> kidsBound

-- | Replace every subtree structurally equal to `sub` by `rep`, rebuilding
-- annotations only along changed paths and sharing untouched subtrees.
-- Occurrences cannot nest (a strict subtree is smaller than its host), so a
-- match is not descended into — same result as the historical whole-tree
-- replaceAll with a fresh re-annotation, without its quadratic cost.
annReplace :: OptEnv -> AnnIR -> AnnIR -> AnnIR -> AnnIR
annReplace det sub rep a0 = maybe a0 id (go a0)
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
                    in Just (mkAnnIR det (setIRSubExprs (annExpr a) (map annExpr kids')) kids')

hashMix :: Int -> Int -> Int
hashMix a b = (a * 16777619) `xor` b

hashStr :: String -> Int
hashStr = foldl' (\a c -> hashMix a (fromEnum c)) 5381

-- | Hash of a node's constructor and non-child payload.
headHash :: IRExpr -> Int
headHash e = case e of
  IRIf{}            -> 1
  IRSelect{}        -> 33
  IROp op _ _       -> hashMix 2 (hashStr (show op))
  IRUnaryOp op _    -> hashMix 3 (hashStr (show op))
  IRTheta _ i       -> hashMix 4 i
  IRSubtree _ i     -> hashMix 5 i
  IRConst v         -> hashMix 6 (hashStr (show v))
  IRCons{}          -> 7
  IRTCons{}         -> 9
  IRHead{}          -> 10
  IRTail{}          -> 11
  IRTFst{}          -> 13
  IRTSnd{}          -> 14
  IRLeft{}          -> 15
  IRRight{}         -> 16
  IRFromLeft{}      -> 17
  IRFromRight{}     -> 18
  IRIsLeft{}        -> 19
  IRIsRight{}       -> 20
  IRDensity d ls _  -> hashMix 21 (hashMix (hashStr (show d)) (hashStr (show ls)))
  IRCumulative d ls _ -> hashMix 22 (hashMix (hashStr (show d)) (hashStr (show ls)))
  IRSample d        -> hashMix 23 (hashStr (show d))
  IRLetIn n _ _     -> hashMix 24 (hashStr n)
  IRVar n           -> hashMix 25 (hashStr n)
  IRLambda n _      -> hashMix 26 (hashStr n)
  IRApply{}         -> 27
  IREnumSum n v _   -> hashMix (hashMix 28 (hashStr n)) (hashStr (show v))
  IRIsPossible v _  -> hashMix 29 (hashStr (show v))
  IRError s         -> hashMix 31 (hashStr s)
  IRConformsTo t _  -> hashMix 32 (hashStr (show t))
  IRLogEnumSum n v _  -> hashMix (hashMix 36 (hashStr n)) (hashStr (show v))
  IREnumSumPaired lg n v _ -> hashMix (hashMix (hashMix 37 (if lg then 1 else 0)) (hashStr n)) (hashStr (show v))
  IRBuiltin b _       -> hashMix 38 (hashStr (show b))
  IRConstruct t _     -> hashMix 39 (hashStr (show t))
  IRDestruct a _      -> hashMix 40 (hashStr (show a))

-- | The largest hoistable common subexpression of a node (candidates are in
-- first-occurrence order and ties break like the historical
-- @maximumBy . nub@, i.e. towards the last equal maximum), plus the
-- (hash, size) keys of repeated pure candidates that were refused only for
-- capture reasons (and may become extractable further down).
bestCommonSubexpr :: AnnIR -> (Maybe AnnIR, Set.Set (Int, Int))
bestCommonSubexpr annIR =
  ( if null candidates then Nothing else Just (maximumBy (comparing annSize) candidates)
  , Set.fromList [ (annHash a, annSize a) | a <- blocked ] )
  where
    skeleton = unconditionalAnns annIR
    bound = annBound annIR
    repeated = [ a | (a, n) <- tallyAnns skeleton
                   , n >= 2
                   , annSize a > 1
                   -- Deliberately not raised at -O3, where the merge exposes far
                   -- more material and hoisting everything is expensive: the
                   -- chain is order-dependent, and it is the SMALL hoists that
                   -- enable the large ones. `cse_0 = readScene(sym)` is two
                   -- leaves, and without it the two enumerated sums that read it
                   -- keep referring to differently-named bindings and never
                   -- compare equal, so the one hoist that actually halves the
                   -- runtime never happens. Measured: a minimum of 4 leaves cuts
                   -- planEnumRecDeepCount's -O3 compile from 5.8s to 1.1s and
                   -- loses the entire -O3 runtime win.
                   , not (annImpure a) ]
    (candidates, blocked) = partition captureSafe repeated
    captureSafe a = not (any (`Set.member` bound) (freeVarsIR (annExpr a)))

-- | Subexpressions reached on every evaluation of the node.  We descend through
-- ordinary nodes but stop at the branches of an IRIf, the body of an IREnumSum,
-- and the body of a lambda, since those are only conditionally, repeatedly, or
-- never evaluated.
--
-- One node shape is descended into but never LISTED: the function half of an
-- application that is itself an application, i.e. a partially applied call.
-- The IR is curried (@IRApply (IRApply f a) b@) while the scalar backends are
-- not -- they flatten a whole application spine into one @f(a, b)@ call site --
-- so hoisting the inner spine into its own binding emits @cse_0 = f(a)@, a call
-- with the wrong arity, which is a runtime TypeError rather than a slower
-- program. (A partially applied LAMBDA is legitimate and common; this only
-- refuses to let CSE manufacture one where the source had a saturated call.)
unconditionalAnns :: AnnIR -> [AnnIR]
unconditionalAnns a0 = go True a0 []
  where
    go listed a acc = (if listed then (a :) else id) $ case annExpr a of
      IRIf{}      -> case annKids a of { (c:_) -> go True c acc; [] -> acc }
      -- A select's arms are conditional under scalar lowering exactly like an
      -- if's (pytorch-tensorizer M1): only the condition is unconditional, so a
      -- guarded subexpression must not be counted as hoistable above the guard.
      IRSelect{}  -> case annKids a of { (c:_) -> go True c acc; [] -> acc }
      IRLambda{}  -> acc
      IREnumSum{} -> acc
      IRLogEnumSum{} -> acc
      IREnumSumPaired{} -> acc
      IRApply{}   -> case annKids a of
        [fn, arg] -> go (not (isApplication (annExpr fn))) fn (go True arg acc)
        kids      -> foldr (go True) acc kids
      _           -> foldr (go True) acc (annKids a)
    isApplication IRApply{} = True
    isApplication _         = False

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
setIRSubExprs (IRSelect{}) [a, b, c] = IRSelect a b c
setIRSubExprs (IROp op _ _) [a, b] = IROp op a b
setIRSubExprs (IRUnaryOp op _) [a] = IRUnaryOp op a
setIRSubExprs (IRTheta _ i) [a] = IRTheta a i
setIRSubExprs (IRSubtree _ i) [a] = IRSubtree a i
setIRSubExprs (IRCons{}) [a, b] = IRCons a b
setIRSubExprs (IRTCons{}) [a, b] = IRTCons a b
setIRSubExprs (IRHead{}) [a] = IRHead a
setIRSubExprs (IRTail{}) [a] = IRTail a
setIRSubExprs (IRTFst{}) [a] = IRTFst a
setIRSubExprs (IRTSnd{}) [a] = IRTSnd a
setIRSubExprs (IRLeft{}) [a] = IRLeft a
setIRSubExprs (IRRight{}) [a] = IRRight a
setIRSubExprs (IRFromLeft{}) [a] = IRFromLeft a
setIRSubExprs (IRFromRight{}) [a] = IRFromRight a
setIRSubExprs (IRIsLeft{}) [a] = IRIsLeft a
setIRSubExprs (IRIsRight{}) [a] = IRIsRight a
setIRSubExprs (IRConstruct t _) kids = IRConstruct t kids
setIRSubExprs (IRDestruct a _) [c] = IRDestruct a c
setIRSubExprs (IRIsPossible val _) [a] = IRIsPossible val a
setIRSubExprs (IRDensity d ls _) [a] = IRDensity d ls a
setIRSubExprs (IRCumulative d ls _) [a] = IRCumulative d ls a
setIRSubExprs (IRLetIn n _ _) [a, b] = IRLetIn n a b
setIRSubExprs (IRLambda n _) [a] = IRLambda n a
setIRSubExprs (IRApply{}) [a, b] = IRApply a b
setIRSubExprs (IREnumSum n val _) [a] = IREnumSum n val a
setIRSubExprs (IRLogEnumSum n val _) [a] = IRLogEnumSum n val a
setIRSubExprs (IREnumSumPaired lg n val _) [a] = IREnumSumPaired lg n val a
setIRSubExprs (IRConformsTo t _) [a] = IRConformsTo t a
setIRSubExprs (IRBuiltin b _) kids = IRBuiltin b kids
setIRSubExprs e [] = e  -- leaves: IRConst, IRSample, IRVar, IRError
setIRSubExprs e kids = error ("setIRSubExprs: arity mismatch for " ++ irPrintFlat e ++ " with " ++ show (length kids) ++ " children")

-- | Free variables of an IR expression.
freeVarsIR :: IRExpr -> [String]
freeVarsIR (IRVar v) = [v]
freeVarsIR (IRLetIn n decl body) = freeVarsIR decl ++ filter (/= n) (freeVarsIR body)
freeVarsIR (IRLambda n body) = filter (/= n) (freeVarsIR body)
freeVarsIR (IREnumSum n _ body) = filter (/= n) (freeVarsIR body)
freeVarsIR (IRLogEnumSum n _ body) = filter (/= n) (freeVarsIR body)
freeVarsIR (IREnumSumPaired _ n _ body) = filter (/= n) (freeVarsIR body)
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
      IRLogEnumSum n _ _ -> foldl' go (Set.insert n acc) (getIRSubExprs e)
      IREnumSumPaired _ n _ _ -> foldl' go (Set.insert n acc) (getIRSubExprs e)
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

