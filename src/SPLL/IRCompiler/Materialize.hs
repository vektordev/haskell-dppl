-- | Materialized marginals: the dense enumeration budget, marginal tables of
-- enumerable operands, their convolution, and point queries against them.
module SPLL.IRCompiler.Materialize (
  strictBelowBound,
  enumeratedBoundShape,
  isEnumerableApplication,
  enumerationWithinMaterializationBudget,
  enumeratedCount,
  MarginalTable,
  materializeOperandTable,
  pointQueryTable,
  lookupMarginal,
  operandProb,
  isForwardOnly,
  binaryInputVars
) where

import SPLL.ReservedNames (topKCutoffParamName)
import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.OptimizerProjection (optimizerConfig)
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.IROptimizer
import PredefinedFunctions
import SPLL.Analysis (isEnumerable, isCandidateBinaryEnumInjF, sharesLatentGiven, enumerableApplication, materializationDomain, withinMaterializationBudget)
import SPLL.Typing.PType
import Data.Maybe
import SPLL.Semiring
import Control.Monad (forM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import SPLL.IRCompiler.Monad

-- | The operands of a comparison against a random enumerable bound, when the
-- 'toIRInference' equation of that name applies: @Just (enumIsLeft, enumSide,
-- cdfSide)@. Both sides are random (a Deterministic one has its own
-- equation); exactly one carries an enumerable 'DiscreteValues' domain within
-- the materialization budget (two are the enumerate-both grid's); the other
-- has a CDF; and no random local is read by both, so the joint law is the
-- product of the two operands' own laws. A local fixed by an enclosing
-- enumeration or witness ('recoveredVars') is a value, not a law, and
-- correlates nothing. The ModalityInfer counterpart is 'compareGround'.
-- | The point at which the cumulative query must be asked when a comparison's
-- True outcome is "the random side lies strictly below @b@". The cumulative
-- query is inclusive (@P(X <= b)@), which is the strict mass for a continuous
-- side (the boundary has measure zero) but not for an Int one, whose strict
-- mass is @P(X <= b - 1)@. The other direction, @X > b@, is the complement of
-- the inclusive CDF and needs no step. Without this, @x < y@ answered
-- @P(x <= y)@ once @y@ was enumerated by a sibling operand (task
-- strict-int-less-than-non-strict-when-operand-shared); 'comparisonWorlds'
-- makes the same step on its interval endpoints.
strictBelowBound :: Expr -> IRExpr -> IRExpr
strictBelowBound side b
  | rType (getTypeInfo side) == TInt = IROp OpSub b (IRConst (VInt 1))
  | otherwise = b

enumeratedBoundShape :: CompilerMetadata -> Expr -> Expr -> Maybe (Bool, Expr, Expr)
enumeratedBoundShape meta l r
  | det l || det r = Nothing
  | not (null sharedRandom) = Nothing
  | enumOk l, not (enumerable r), measurable r = Just (True, l, r)
  | enumOk r, not (enumerable l), measurable l = Just (False, r, l)
  | otherwise = Nothing
  where
    det e = pType (getTypeInfo e) == Deterministic
    enumerable e = isEnumerable (tags (getTypeInfo e))
    enumOk e = enumerable e && enumerationWithinMaterializationBudget meta (tags (getTypeInfo e))
    measurable e = pType (getTypeInfo e) `elem` [Integrate, PNormal, PLogNormal]
    sharedRandom = [ v | v <- Set.toList (Set.intersection (freeVarsExpr l) (freeVarsExpr r))
                       , isLocal v, v `notElem` recoveredVars meta ]
    isLocal v = case lookup v (typeEnv meta) of
      Just (t, False) -> not (isTArrowType t)
      _ -> False

-- | The enumeration engine's applicability ('SPLL.Analysis.enumerableApplication'),
-- in this compile's program.
isEnumerableApplication :: CompilerMetadata -> Expr -> Expr -> Bool
isEnumerableApplication meta l v = isJust (enumerableApplication (fcData meta) (compilingProgram meta) l v)

-- | Is the domain this enumerable application would materialize small enough to
-- be worth materializing? Reads the same 'DiscreteValues' tag
-- 'enumerateAppliedLambda' will use (its @head@ of the tag list) and measures its
-- cardinality against 'materializationCardinality' -- the same budget
-- 'SPLL.Analysis.materializationDomain' enforces for Tier-0 marginal
-- materialization, which this path previously escaped.
--
-- The count comes from 'multiValueCardinality', NOT from @length
-- (multiValueToValueList mv)@: the list is the cross-product whose size is
-- precisely what is being refused, so counting it by building it would pay the
-- cost the guard exists to avoid. The 'Integer' count is clamped into 'Int' at
-- one above the bound before the budget check, which cannot change the verdict
-- (anything above the bound is over budget) and keeps an astronomically large
-- product from having to fit a machine word.
--
-- 'Nothing' (no tag, or a non-finite domain) answers 'False': there is no domain
-- to enumerate, so this arm must not claim the node. 'isEnumerableApplication'
-- has already established a tag exists, so this is a total-function guard
-- rather than a reachable case.
enumerationWithinMaterializationBudget :: CompilerMetadata -> [Tag] -> Bool
enumerationWithinMaterializationBudget meta tgs = case [mv | DiscreteValues mv <- tgs] of
  (mv:_) -> maybe False withinBudget (enumeratedCount mv)
  []     -> False
  where
    bound = materializationCardinality (compilerConfig meta)
    withinBudget n = withinMaterializationBudget bound (fromInteger (min n (toInteger bound + 1)))

-- | How many values 'enumerateAppliedLambda' would loop over: the length of
-- 'multiValueToValueList', computed without building it. This is the budget
-- gate's count, and it must measure exactly that list, because the gate is a
-- refusal to blow up and nothing else -- any domain it declines for another
-- reason is silently rerouted.
--
-- It differs from 'multiValueCardinality' in one place: an EMPTY enumeration
-- counts as zero values rather than "no domain". A value known to be @right
-- ..@ is tagged @MultiEither (MultiDiscretes []) rs@, whose list has exactly
-- @rs@'s values; 'multiValueCardinality' answers 'Nothing' there (it mirrors
-- 'multiValueIsFinite', which rejects an empty enumeration), and the gate then
-- declined a two-value domain as if it were unbounded
-- (task enumeration-budget-gate-misses-nested-application; the program is
-- test/cases/let-bindings/enumDeadLetFreshDrawTuple, formerly the known issue
-- fuzzLetWitnessGenerateBackedFallback). 'Nothing' is
-- kept for the leaves with no enumerable list at all.
enumeratedCount :: MultiValue -> Maybe Integer
enumeratedCount mv = case mv of
  MultiContinuous  -> Nothing
  MultiAuto        -> Nothing
  MultiTypeRef _   -> Nothing
  MultiDiscretes vs -> Just (toInteger (length vs))
  MultiTuple a b   -> (*) <$> enumeratedCount a <*> enumeratedCount b
  MultiEither a b  -> (+) <$> enumeratedCount a <*> enumeratedCount b
  MultiADT cs      -> sum <$> mapM (fmap product . mapM enumeratedCount . snd) cs

-- ===== Tier 0: materialized discrete marginals =====
-- (task materialize-discrete-marginals, design materialized-marginals-semiring)
--
-- THE COST BEING RETIRED. The enumerable-InjF inference paths below compile a
-- point query on `l (+) r` into a loop over l's finite domain whose body
-- re-descends into `l` for every value. That descent is EAGER (pLeft is
-- computed before the topK cutoff, which only gates the right-hand descent),
-- so a nested chain costs T(n) = |D(n-1)| * T(n-1) -- super-exponential, and
-- invisible to every optimizer pass we have: the recomputation is a runtime
-- loop re-entry, not duplicated IR, and CSE deliberately stops at a loop body
-- bodies. Measured (task measure-marginal-recomputation) at 10.7x redundant
-- neural-cell evaluations for a 3-term MNIST-digit sum and 4021x for a 6-term
-- one, tracking wall clock almost exactly.
--
-- WHAT REPLACES IT. When an OPERAND is itself such a chain, its marginal is
-- tabulated once over its finite domain -- one let-bound scalar cell per value,
-- each cell an unrolled convolution over the operand grid -- and the loop body
-- reads a cell instead of re-descending. The chain then costs
-- sum(k) |D(k)|*|D(leaf)| instead of the product.
--
-- THREE DESIGN POINTS, each load-bearing:
--
--  1. Cells are LET-BOUND SCALARS, not a table in the IR. 'IRExpr' has no dense
--     array type and @IRBuiltin BListIndex@ is an O(n) cons-cell walk in the
--     interpreter, so a runtime table would turn the O(n*range) DP into
--     O(n*range^2) on the path the whole corpus runs on. The domains are
--     compile-time known and small, so unrolling is both possible and the
--     cheaper choice -- which is why the
--     cardinality guard ('materializationDomain') and the unrolling
--     affordability condition are literally the same predicate.
--
--  2. Only an operand that is ITSELF a nested enumerable InjF is tabulated;
--     the queried node keeps today's path. Tabulating the queried node would be
--     a pessimization for an invertible op: its point query costs O(|D_left|)
--     (enumerate left, invert to right) while its table costs |D_left|*|D_node|,
--     and only one cell is ever read. (For a forward-only op -- and/or/max, no
--     inverse -- the point query already walks the whole |L|x|R| grid, so a
--     table there would be cost-neutral rather than harmful; still no gain at
--     the top, and as an operand it is tabulated by the same rule below.)
--     Consequence worth knowing: a two-term program's emitted IR is unchanged.
--
--  3. The tables are built by evaluating the InjF's FORWARD function at compile
--     time over the operand grid ('propagateValues' -- the same evaluator
--     Analysis already uses to derive the DiscreteValues domains), never by
--     inverting. So forward-only ops need no special case, and the terms of each
--     cell land in the same order today's loop accumulates them in, which is why
--     materialization is numerically IDENTICAL to the path it replaces rather
--     than merely equal within tolerance. (Observed exception: a chain of
--     if-spelled Bool leaves, @if Uniform < 0.1 then False else True@, differs
--     in the last ulp or two -- chains of @Uniform < p@ leaves and the mNistAdd
--     sums do not. Not diagnosed further; see task
--     and-chain-exponential-over-random-operands.)
--
-- TOPK. The cutoff is `accProb * pLeft > top_k_cutoff`, where accProb is the
-- globally accumulated path probability. A context-free table could not see it
-- -- except that accProb is only ever modified at an 'IfThenElse', so every
-- level of an enum chain shares the one accProb IRExpr, and the cells are bound
-- in the scope where it is live. The per-term guard emitted below is therefore
-- the same test on the same value, dropping exactly the terms today's in-loop
-- cutoff drops: table-local pruning drops no more mass than accProb pruning
-- would, by identity rather than by argument.
--
-- rIMPOSS. Deliberately not tracked per cell. The paths that consume these
-- tables already discard the sub-result's dim, branch count and impossibility
-- flag (they read `unP . rProb` only) and derive the node's own flag from the
-- summed mass via 'opaqueMass' -- sound there because it is a discrete mass, as
-- that function's own comment argues. A cell is one term of exactly such a sum,
-- so per-cell flags would have no consumer; giving them one is a change to what
-- the enumeration paths report, not to materialization.

-- | A materialized marginal: for each value of a node's finite domain, an
-- 'IRExpr' reading the let-bound cell holding p(node = value).
type MarginalTable = [(Value, IRExpr)]

-- | An orderable key for a domain value, so grid pairs can be grouped by the
-- output they produce in one pass. 'Value' has no 'Ord' instance and giving it
-- one would be a much wider change; a domain is a finite set of literal
-- constants, on which 'show' is injective, which is all this needs.
valueKey :: Value -> String
valueKey = show

-- | Tabulate an operand's marginal for one of the enumerable-InjF paths, or
-- decline (in which case the caller re-descends as before). Declines unless the
-- operand is itself a nested enumerable InjF -- see design point 2 above.
materializeOperandTable :: CompilerMetadata -> Expr -> CompilerMonad (Maybe MarginalTable)
materializeOperandTable meta e
  | isNestedEnumInjF e = materializeMarginal meta e
  | otherwise          = return Nothing

-- | The shape whose marginal is worth tabulating: a binary InjF both of whose
-- operands are enumerable and non-'Deterministic' -- i.e. exactly what the
-- enumerable-InjF inference paths below fire on, and therefore exactly what
-- costs a full re-descent per queried value today.
isNestedEnumInjF :: Expr -> Bool
isNestedEnumInjF e = case node e of
  InjF (Named _) [l, r] -> isCandidateBinaryEnumInjF l r
  _                     -> False

-- | Build the marginal table for @e@, recursively: a convolution of its
-- operands' tables when @e@ is a permitted nested node, a per-value point query
-- when it is a leaf. 'Nothing' means "do not materialize", and propagates: a
-- nested node that fails the gate does NOT fall back to per-value point queries
-- of itself, since that would emit |domain| copies of a whole sub-inference and
-- compound multiplicatively with depth.
materializeMarginal :: CompilerMetadata -> Expr -> CompilerMonad (Maybe MarginalTable)
materializeMarginal meta e = case domainOf e of
  Nothing  -> return Nothing
  Just dom
    | isNestedEnumInjF e -> materializeConvolution meta e dom
    | isEnumerable (tags ti) && pType ti /= Deterministic -> pointQueryTable meta e dom
    | otherwise -> return Nothing
  where
    ti = getTypeInfo e
    domainOf = materializationDomain (materializationCardinality (compilerConfig meta))
                 . tags . getTypeInfo

-- | The table of a nested node, as the convolution of its two operands' tables:
-- cell v = sum over the operand pairs whose forward value is v, of the product
-- of their cells. Declines if the decomposability gate says the operands may
-- share an enumerated latent (tabulating them separately would then be silently
-- wrong -- 'testCases/letThreadEnumerable' is the canary), if the operand grid
-- is too large to unroll, if either operand declines, or if any grid pair fails
-- to evaluate forward at compile time or lands outside the node's own domain.
materializeConvolution :: CompilerMetadata -> Expr -> [Value] -> CompilerMonad (Maybe MarginalTable)
materializeConvolution meta e dom = case node e of
  InjF (Named name) [l, r]
    | mayShareLatent -> return Nothing
    | otherwise -> do
        mTblL <- materializeMarginal meta l
        mTblR <- materializeMarginal meta r
        case (mTblL, mTblR) of
          (Just tblL, Just tblR)
            | withinMaterializationBudget bound (length tblL * length tblR)
            , Just buckets <- forwardGrid (resolveInjF (rType (getTypeInfo e)) name) tblL tblR
              -> Just <$> convolveTables meta dom buckets
          _ -> return Nothing
  _ -> return Nothing
  where
    bound = materializationCardinality (compilerConfig meta)
    -- Missing verdict (a node the whole-program walk did not reach) is
    -- conservative "may share", like every other unknown in this analysis.
    -- Latents fixed by an enclosing enumeration loop do not count: given
    -- them, operands that share nothing else are independent.
    mayShareLatent =
      Map.findWithDefault True (chainName (getTypeInfo e)) (latentVerdicts meta)
      && maybe True (sharesLatentGiven (fixedLatents meta))
           (Map.lookup (chainName (getTypeInfo e)) (latentScopes meta))
    domKeys = Set.fromList (map valueKey dom)
    -- Evaluate the InjF's forward function on every operand-value pair at
    -- compile time, and bucket the pairs by the output value they produce.
    -- Nothing if any pair fails to evaluate or produces a value outside the
    -- node's own tagged domain -- either would silently drop mass.
    --
    -- Bucketing here, rather than letting each cell filter the whole grid, is
    -- what keeps a level's cost linear in the grid: the per-cell filter is
    -- |domain| * |grid| value comparisons, which on a wide domain (the
    -- cardinality guard permits several thousand cells) dominates everything
    -- else the compiler does -- measured at 8.3s for a single generated
    -- program before this, 0.3s after.
    forwardGrid fName tblL tblR =
      bucket <$> mapM pairCell [(lv, lc, rv, rc) | (lv, lc) <- tblL, (rv, rc) <- tblR]
      where
        pairCell (lv, lc, rv, rc) = case propagateValues (adtDecls meta) fName [[lv], [rv]] of
          [v] | valueKey v `Set.member` domKeys -> Just (valueKey v, (lc, rc))
          _                                     -> Nothing
        -- fromListWith prepends, so each bucket comes out in reverse grid
        -- order; the reverse restores it, and the order is load-bearing (see
        -- 'convolveTables' on why the fold order has to match the loop's).
        bucket = Map.map reverse . Map.fromListWith (++) . map (fmap (: []))

-- | Emit one let-bound cell per domain value out of the compile-time grid.
convolveTables :: CompilerMetadata -> [Value] -> Map.Map String [(IRExpr, IRExpr)] -> CompilerMonad MarginalTable
convolveTables meta dom buckets = do
  cells <- mapM cellFor dom
  return (zip dom cells)
  where
    sr = semiringOf meta
    -- One cell per domain value: a 'BMap' over that value's own bucket of the
    -- operand grid (task batched-enumsum-materialization), reduced by one
    -- 'BReduce'. This replaces the old hand-rolled fold -- a right-associated
    -- chain of 'srPlus' nodes, log-space additionally let-binding a running
    -- accumulator per term ('logSumExpIR' reads both its operands three
    -- times, so an unbound accumulator grew the cell 3^n in the term count)
    -- -- with two tensor builtins whose body text is written once and
    -- reused per pair, instead of duplicated per pair. 'BReduce's own
    -- interpreter/codegen lowerings already fold right-to-left over the
    -- tensor's element order (matching the enumeration's), so listing the bucket
    -- in grid order (as it already comes) keeps the tabulated cell
    -- bit-identical to the re-descending loop it replaces, the same claim the
    -- old fold made.
    --
    -- Buckets of size 0 or 1 skip the tensor machinery entirely: there is
    -- nothing to reduce (0) or share (1), and building one would only add
    -- nodes.
    cellFor v = do
      let bucket = Map.findWithDefault [] (valueKey v) buckets
      cellExpr <- case bucket of
        []         -> return (srZero sr)
        [(lc, rc)] -> return (term lc rc)
        _          -> do
          pairVar <- mkVariable "mat_pair"
          let gridTensor = IRBuiltin (BTensor [EFixed (length bucket)])
                             [IRConstruct TgTuple [lc, rc] | (lc, rc) <- bucket]
              mapBody  = term (IRDestruct AcFst (IRVar pairVar)) (IRDestruct AcSnd (IRVar pairVar))
              mapped   = IRBuiltin BMap [IRLambda pairVar mapBody, gridTensor]
              -- Task semiring-parametric-marginals: was hardcoded to
              -- 'ROpLogSumExp'/'ROpAdd' by 'srLogSpace' alone, which is
              -- exactly what 'srReduceOp' already computes for the two
              -- families that existed before this task (so this is a
              -- behaviour-preserving read, not a new choice) -- and, unlike
              -- the hardcoded version, also picks 'ROpMax' under the
              -- max-product (MAP) semiring. Tier 1's whole premise is that it
              -- rides Tier 0's identical table; leaving this hardcoded would
              -- have silently kept every materialized cell on plain sum
              -- reduction under '--semiring=map', the one path this task
              -- exists to cover.
              reduceOp = srReduceOp sr
          return (IRBuiltin (BReduce reduceOp 0) [mapped])
      cellName <- mkVariable "mat_cell"
      setVariables [(cellName, cellExpr)]
      return (IRVar cellName)
    -- The topK guard, in the same shape and on the same accProb the in-loop
    -- cutoff uses (see the TOPK note above). No membership test is needed: the
    -- grid only holds pairs that are in both operands' domains by construction,
    -- where today's loop has to test the inverted value at runtime. This is
    -- the map's per-element body when a bucket goes through 'BMap'/'BReduce'
    -- above, so its 'IRIf' -- the "masked" half of "masked reduce" -- is
    -- written once per cell rather than once per pair.
    term lc rc = case topKThreshold (compilerConfig meta) of
      Nothing -> srTimes sr lc rc
      Just _  -> IRIf (IROp OpGreaterThan (srTimes sr (accProb meta) lc) (IRVar topKCutoffParamName))
                      (srTimes sr lc rc)
                      (srZero sr)

-- | The base case: one let-bound cell per domain value, each the ordinary
-- point-query inference of @e@ at that (compile-time constant) value. This is
-- the same IR today's loop body builds against the loop variable, with the
-- constant substituted -- which is what makes the tabulated value bit-identical
-- to the re-descended one.
--
-- Unlike a convolution cell, which is a handful of references to cells below
-- it, a leaf cell holds a whole compiled sub-inference -- so this is the one
-- place where materialization multiplies real IR rather than rearranging it,
-- and it is where an unaffordable unrolling actually shows up. A `ReadNN`
-- digit read is a few nodes and ten of them cost nothing; an arbitrary
-- enumerable expression (a deep if-tree over comparisons, say) can be
-- thousands, and copying that per domain value blows the IR up by more than an
-- order of magnitude -- measured 14x, and a 0.17s compile turning into 16s,
-- before this guard.
--
-- So the first value is compiled in its own scope as a PROBE, and the
-- whole table is declined -- with the probe's bindings discarded, never
-- reaching the enclosing scope -- unless the unrolling it implies is
-- affordable. The probe is kept and reused for its own cell rather than
-- recompiled, so the measurement costs one sub-compile, not two.
--
-- Affordable is two conditions, because the total and the per-copy size are
-- different failure modes: the total must fit the cardinality budget (the same
-- "how much unrolling is affordable" question the guard asks of domains and
-- grids), and the individual copy must be small enough to be worth copying at
-- all ('maxTabulatedLeafNodes') -- judged on the copy's size once its constant
-- key has been folded in, when its raw size is over (see the fallback below),
-- and in both cases with literal data counted as one node ('irLogicNodeCount').
pointQueryTable :: CompilerMetadata -> Expr -> [Value] -> CompilerMonad (Maybe MarginalTable)
pointQueryTable _ _ [] = return Nothing
pointQueryTable meta e dom@(v0 : vs) = do
  probe <- scoped (inferAt v0)
  let probeSize = compiledSize irNodeCount probe
      bound = materializationCardinality (compilerConfig meta)
      withinTotal = withinMaterializationBudget bound (length dom * probeSize)
  if withinTotal && compiledSize irLogicNodeCount probe <= maxTabulatedLeafNodes
    then do
      probeRes <- inline probe
      cell0 <- bindCell (unP (rProb probeRes))
      cells <- forM vs (\v -> inferAt v >>= bindCell . unP . rProb)
      return (Just (zip dom (cell0 : cells)))
    else if not withinTotal
      then return Nothing
      else do
        -- Over the per-copy bound as emitted, but maybe not as it will run:
        -- each copy is compiled at a CONSTANT key, and the key-dependent
        -- tests that dominate a small leaf's raw IR (ANY checks on the key,
        -- equality against it, the arms it makes impossible) fold away once
        -- the key is known. A Bernoulli spelled @if Uniform < 0.1 then False
        -- else True@ is 181 nodes raw and 1 folded; the same leaf reading an
        -- enumerated latent is 193 and 38 -- a leaf by any reading of
        -- 'maxTabulatedLeafNodes', and exactly the operand of an @&&@ chain
        -- that costs 2^Q per call untabulated (task
        -- and-chain-exponential-over-random-operands). So judge "is this a
        -- leaf" on the folded size, per copy: folding is key-dependent, so
        -- every value is compiled (in its own scope, so a decline leaks no
        -- bindings) and every one must fit. The copies are still EMITTED
        -- raw, in the order the branch above emits them, so the table is the
        -- same IR either way and the global optimizer does the folding it
        -- was going to do anyway; and the total above is still judged on the
        -- raw size, so the unrolled volume the optimizer receives stays
        -- inside the cardinality budget.
        rest <- mapM (scoped . inferAt) vs
        let copies = probe : rest
        if all ((<= maxTabulatedLeafNodes) . foldedSize) copies
          then do
            cells <- forM copies (\o -> inline o >>= bindCell . unP . rProb)
            return (Just (zip dom cells))
          else return Nothing
  where
    inferAt v = toIRInference meta False e (IRConst (valueToIR v))
    compiledSize count o = count (unP (rProb (openValue o))) + openBlockSize count o
    foldedSize o = irLogicNodeCount (postProcess (optimizerConfig (compilerConfig meta)) (closeExpr o (unP . rProb)))
    bindCell p = do
      cellName <- mkVariable "mat_leaf"
      setVariables [(cellName, p)]
      return (IRVar cellName)

-- | How large a leaf's compiled inference may be and still be worth copying
-- once per domain value. Not a second cardinality budget -- a statement about
-- what a "leaf" is: past this size the node is a sub-program that happens to
-- have a finite domain, and tabulating it multiplies IR instead of
-- rearranging it, for a chain whose depth was never what made it slow.
--
-- Calibrated, not guessed. A `ReadNN` digit read -- the shape the whole design
-- targets -- compiles to 10 nodes. Sweeping 250 generated programs, every leaf
-- that made materialization a compile-time pessimization was 181 nodes or
-- more (up to 5099, at which point a 0.17s compile became 16s). Nothing
-- observed lands between; this sits in the gap.
maxTabulatedLeafNodes :: Int
maxTabulatedLeafNodes = 100

-- | Read a materialized marginal at a runtime key. Two lowerings, chosen by
-- 'CompilerConfig''s 'batched' flag rather than left to per-backend codegen:
--
-- * __Scalar__: the short-circuiting if-chain this always was. It stops at
--   the first match, which is faster than reading a tensor for the small
--   domains this fires on, so scalar emission is unchanged.
-- * __Batched__: an O(1) gather ('BIndex') into a 'BTensor' of the cells,
--   worth 1.7-2.4x measured end to end (task
--   batched-enumsum-materialization) -- a @torch.where@ cascade evaluates
--   every arm, so the if-chain form costs O(|domain|) tensor selects per
--   read where the index form costs one.
--
-- The index is found by a small if-chain of its own (@idxExpr@), over
-- integer positions rather than the (possibly large) cell expressions -- so
-- it stays cheap even though it is itself a cascade. A key matching nothing
-- in the table resolves to position 0, an arbitrary in-bounds sentinel: safe
-- because 'tensor_index' (pythonLibBatched.py) clamps rather than reads out
-- of bounds, and because every caller that can pass an off-domain key (the
-- inverted-value case in the two-operand enumerate path below) discards this
-- read's result behind a separate 'IRIsPossible' guard before it reaches the
-- output -- exactly the pattern 'nn_gather' already relies on for the same
-- reason. The final @else@ of the scalar if-chain is the semiring zero, which
-- is what a key outside the domain must contribute there (and is unreachable
-- when the key is an enumeration variable ranging over exactly this domain).
-- @key@ is read once per arm either way, so callers pass a variable, not an
-- expression.
lookupMarginal :: CompilerMetadata -> MarginalTable -> IRExpr -> IRExpr
lookupMarginal meta tbl key
  | batched (compilerConfig meta) = indexLookup
  | otherwise                     = ifChainLookup
  where
    sr = semiringOf meta
    ifChainLookup =
      foldr (\(v, cell) rest -> IRIf (IROp OpEq key (IRConst (valueToIR v))) cell rest) (srZero sr) tbl
    indexLookup =
      IRBuiltin (BIndex 0) [IRBuiltin (BTensor [EFixed (length tbl)]) (map snd tbl), idxExpr]
    idxExpr =
      foldr (\(i, (v, _)) rest -> IRIf (IROp OpEq key (IRConst (valueToIR v))) (IRConst (VInt i)) rest)
            (IRConst (VInt 0)) (zip [0 :: Int ..] tbl)

-- | @p(operand = key)@ for one of the enumerable-InjF loop bodies: a
-- materialized-table read when the operand was tabulated, today's re-descent
-- otherwise. Only the probability is taken either way -- see the rIMPOSS note
-- above for why that is not a loss.
operandProb :: CompilerMetadata -> Maybe MarginalTable -> Expr -> IRExpr -> CompilerMonad IRExpr
operandProb meta (Just tbl) _ key = return (lookupMarginal meta tbl key)
operandProb meta Nothing    e key = (unP . rProb) <$> toIRInference meta False e key


-- | True if the named InjF is forward-only (no inverse declarations), e.g. and/or.
-- Such ops cannot be inverted to recover an operand from the result, so their
-- discrete inference enumerates both operand grids and filters by the forward value
-- rather than inverting one side.
isForwardOnly :: [ADTDecl] -> String -> Bool
isForwardOnly adtDecls' name = case lookup name (globalFEnv adtDecls') of
  Just (FPair _ []) -> True
  _                 -> False

-- | The two input variables of an InjF used as a binary function.
binaryInputVars :: String -> FDecl -> (String, String)
binaryInputVars _ FDecl{inputVars=[a, b]} = (a, b)
binaryInputVars name d = error ("InjF '" ++ name ++ "' is applied as a binary function but declares input variables " ++ show (inputVars d))
