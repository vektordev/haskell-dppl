-- The pattern-match coverage checker exceeds its default 30-model budget on
-- 'planInvertNode''s match on the peeled slice (a @Maybe (Either String
-- (PlanRef, [PLeafCon], [PeelStep], Monotonicity))@ scrutinee with guarded
-- alternatives), and then reports that exhaustive match as incomplete.
-- Raising the budget lets it finish rather than hiding the result.
{-# OPTIONS_GHC -fmax-pmcheck-models=4000 #-}
-- | Plan-guided enumeration over partition plans: plan worlds, their
-- inversion, grouping and factorization (measured by 'measureWorlds').
module SPLL.IRCompiler.Plan (
  planWitnessApply,
  planReadOf,
  planApplicable
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Typing.PType
import Data.Maybe
import Data.Either (partitionEithers)
import Data.List (isPrefixOf, find, elemIndex, nub, intercalate)
import Data.Functor ((<&>))
import SPLL.AutoNeural hiding (planReadOf, planProjectedReadOf)
import qualified SPLL.AutoNeural as AutoNeural
import SPLL.Typing.ForwardChaining
import SPLL.Typing.AlgebraicDataTypes
import SPLL.Semiring
import Control.Monad (forM, unless, void, zipWithM)
import Control.Monad.State.Strict (StateT, runStateT, get, gets, put, modify, lift)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Worlds

equalityGuardStatic :: RType -> IRExpr -> IRExpr -> IRExpr
equalityGuardStatic = equalityGuardBody equalityGuardStatic

-- ===== Plan-guided lazy enumeration (design plan-guided-lazy-enumeration, M1) =====
--
-- When the bound variable of a probabilistic let is the structured output of a
-- neural network (an argument that is a ReadNN whose declaration yields a
-- PartitionPlan), the NN's distribution over that value is fully factorized
-- per plan slot -- softmax regions for enums and constructor flags, (mu,
-- sigma) pairs for continuous leaves -- and the plan is depth-unrolled, hence
-- finite. So instead of materializing the argument's (possibly astronomically
-- large) discrete support into an enumerated sum, the observation is inverted into
-- worlds whose constraints live on individual plan LEAVES: each world maps
-- constrained leaf regions to their still-allowed logit slots (with optional
-- per-slot runtime guards) and is measured as the product of the constrained
-- regions' masses, read directly from the raw logit vector. Leaves untouched
-- by a world contribute their full marginal of 1 (the same principle as the
-- witnessed-inference ANY guard), which is also what makes plans with
-- continuous leaves safe here as long as the body never constrains them.
--
-- Milestone 1 scope: constraints on discrete leaves only -- bodies are inline
-- predicate expressions built from field accessors (fst/snd/ADT fields),
-- is<Ctor> tests, ==/</> against deterministic values, boolean connectives,
-- and if splits. Milestone 2 adds user-function application: a call whose
-- arguments are plan slices (accessor chains) or deterministic values is
-- specialized -- its body is traversed under a fresh parameter frame --
-- with specializations memoized by (body, plan offsets, det args) and a
-- strict-plan-descent stack guard for termination; recursion bottoms out
-- where the depth-unrolled plan prunes the recursive constructors (their
-- branch worlds become unsatisfiable and the branch is never traversed).
-- Value-valued plan-dependent expressions (counting folds compared against
-- deterministic bounds) enumerate as (value, world) pairs via
-- 'planEnumValues'. Anything the traversal cannot handle makes this dispatch
-- decline (Left), and the caller falls through to the set-witness fallback,
-- whose refusal diagnostic then names the unsupported node.

-- | A reference into the neural argument's PartitionPlan: the sub-plan
-- denoting an expression's value plus that sub-plan's flat logit offset.
data PlanRef = PlanRef PartitionPlan Int

-- | A 'PLeafEq' as the per-slot 'PLeafCon' it stands for; anything else
-- unchanged.
expandLeafEq :: PLeafCon -> PLeafCon
expandLeafEq (PLeafEq b _ _ _ _ slots) = PLeafCon b slots
expandLeafEq c = c

-- | The constraint "the discrete leaf at @off@, over @vals@, equals (or, with
-- @pol@ False, differs from) @x@", given as its per-slot guards @slots@: a
-- 'PLeafEq' where the domain is a contiguous Int range and @x@ is cheap to
-- read three times, else the 'PLeafCon' of those guards.
discreteEqCon :: Int -> [Value] -> IRExpr -> Bool -> [(Int, IRExpr)] -> PLeafCon
discreteEqCon off vals x pol slots
  | simpleRead x
  , (lo : _) <- ints
  , length ints == length vals
  , ints == [lo .. lo + length ints - 1] = PLeafEq off lo (lo + length ints - 1) x pol slots
  | otherwise = PLeafCon off slots
  where
    ints = [ k | VInt k <- vals ]
    simpleRead (IRVar _)        = True
    simpleRead (IRDestruct _ e) = simpleRead e
    simpleRead _                = False

-- | A plan world: a 'World' whose constraints are all on plan leaves
-- ('OnLeaf') or pairs of them ('Pair'). It contributes (product of constrained
-- leaf masses) when all guards hold, else 0. A pair (milestone 3) couples two
-- continuous leaves: (a, b) constrains leaf@a > leaf@b. A world may couple each
-- continuous leaf at most once, and a coupled leaf may carry no other
-- constraint -- anything beyond that is an orthant probability, which the
-- language excludes (checked in 'pwOverCoupled'; design
-- plan-guided-lazy-enumeration M3).
--
-- Its factors are of two kinds. A 'WMass' (milestone 4) is a pre-measured
-- multiplicative mass contribution: the summed mass of a collapsed value group
-- for the DP path-counting worlds (see 'planGroupValues') -- a group of
-- same-value worlds is merged into one world with empty constraints and this
-- factor, so counting folds stay O(depth) instead of 2^depth. A 'WFactor'
-- (task plan-free-stochastic-subtree-not-factorized) carries a whole
-- independent sub-inference, the plan analogue of the set-witness residue
-- factors: a subtree of the body that mentions no plan-bound variable is
-- independent of everything the plan constrains, so the joint factorizes and
-- the subtree can be measured by the ordinary probability compiler and
-- multiplied in ('prodP': dims and branch counts add) -- a full 'PResult', so
-- it may carry its own dimension.
type PlanWorld = World

-- | A plan world from its parts: leaf constraints, pairs, factors, baked
-- leaves, clash.
planWorld :: [IRExpr] -> [PLeafCon] -> [(Int, Int)] -> [WFactor] -> [Int] -> Bool -> PlanWorld
planWorld gs cs ps = World gs (map OnLeaf cs ++ map (uncurry Pair) ps)

-- | The world with its leaf constraints replaced (its pairs kept).
withLeafCons :: [PLeafCon] -> PlanWorld -> PlanWorld
withLeafCons cs w = w { wCons = map OnLeaf cs ++ [ c | c@Pair{} <- wCons w ] }

-- | An unguarded world from leaf constraints alone.
pw1 :: [PLeafCon] -> PlanWorld
pw1 cs = planWorld [] cs [] [] [] False

-- | The unconstrained world @pw1 []@: no guards, constraints or factors.
planWorldTrivial :: PlanWorld -> Bool
planWorldTrivial w = null (wGuards w) && null (wCons w) && null (wFactors w) && null (wBaked w)

-- | A world's independent sub-inference factors, each with the block it
-- reads, bound once ('planFactorFree', 'planFactorBool').
pwSubFactors :: PlanWorld -> [Open PResult]
pwSubFactors w = [ o | WFactor o <- wFactors w ]

-- | The observation target: the plan-leaf analogue of the point/interval
-- split in 'WSet'. PTUpTo is the cumulative target (body <= sample).
data PTarget = PTPoint IRExpr | PTUpTo IRExpr

-- | Traversal-scope binding of one lambda parameter (milestone 2): the
-- parameter denotes either a slice of the neural argument's plan or a
-- deterministic call-site value. Parameters are identified by the occurrence
-- chain names of their binding lambda (shadowing-aware, via
-- 'lambdaVarOccurrences').
data PlanBinding = PBPlan PlanRef
                 | PBDet String IRExpr  -- ^ parameter name, call-site value

-- | The traversal environment: one entry per parameter in scope. Since callee
-- bodies can only reference their own parameters and top-level names, each
-- specialization replaces the environment with the callee's own frame rather
-- than nesting.
type PlanEnv = [([ChainName], PlanBinding)]

-- | Occurrence chain names bound to plan slices: the "random occurrences" of
-- the traversal. Deterministic parameter occurrences deliberately do not
-- count -- a subtree mentioning only those is deterministic given scope.
planEnvOccs :: PlanEnv -> [ChainName]
planEnvOccs env = concat [cns | (cns, PBPlan _) <- env]

-- | Occurrence chain names bound to call-site deterministic values. These are
-- deliberately NOT plan occurrences, but a subtree mentioning one is not
-- self-contained either: 'planGenDet' compiles it and then rewrites the bare
-- parameter variable to its call-site value. The factorization of a plan-free
-- *stochastic* subtree ('planFactorFree') has no such rewrite available (the
-- parameter can appear anywhere inside a full inference compile, including
-- inside bindings the sub-compile hoists), so it declines such subtrees.
planEnvDetOccs :: PlanEnv -> [ChainName]
planEnvDetOccs env = concat [cns | (cns, PBDet _ _) <- env]

planEnvLookup :: PlanEnv -> ChainName -> Maybe PlanBinding
planEnvLookup env cn = listToMaybe [b | (cns, b) <- env, cn `elem` cns]

-- | Static truth value of a guard built over constants (the canonical
-- polarity targets of 'planInvertBool' produce exactly such guards).
staticBool :: IRExpr -> Maybe Bool
staticBool (IRConst (VBool b)) = Just b
staticBool (IROp OpEq (IRConst a) (IRConst b)) = Just (a == b)
staticBool (IRUnaryOp OpNot e) = not <$> staticBool e
staticBool (IROp OpAnd a b) = (&&) <$> staticBool a <*> staticBool b
staticBool (IROp OpOr  a b) = (||) <$> staticBool a <*> staticBool b
staticBool _ = Nothing

-- | A world is statically unsatisfiable when some constrained leaf region has
-- no allowed slots left, or a guard is statically false. Used to prune
-- zero-mass worlds and, crucially, to gate traversal of if-branches
-- unreachable under the plan's depth unrolling: at the plan's deepest level
-- the recursive constructors are pruned, the branch worlds guarded by them
-- die, and the branch body -- containing the recursive call -- is never
-- traversed. This is the recursion base of the milestone-2 specialization.
pwUnsat :: PlanWorld -> Bool
pwUnsat w = any conUnsat (leafCons w)
         || any ((== Just False) . staticBool) (wGuards w)
         || any (\(a, b) -> (b, a) `elem` pairs || a == b) pairs
  where
    pairs = leafPairs w
    conUnsat (PLeafCon _ slots)  = null slots
    conUnsat (PLeafIvl _ (WFinite (IRConst (VFloat lo))) (WFinite (IRConst (VFloat hi)))) = lo >= hi
    conUnsat (PLeafPt _ _ _ gs') = any ((== Just False) . staticBool) gs'
    conUnsat _ = False

-- | Milestone-3 refusal rule, kept precise: a world may couple each
-- continuous leaf to at most one other leaf, and a coupled leaf may carry no
-- interval or point constraint of its own. Anything beyond that is a
-- correlated-Gaussian orthant probability, i.e. quadrature the language
-- excludes by design (see "Hard residual" in the design doc). Returns a
-- diagnostic for the first offending world.
pwOverCoupled :: PlanWorld -> Maybe String
pwOverCoupled w
  | (base:_) <- overCoupled = Just
      ("a world couples the continuous leaf at logit offset " ++ show base
       ++ " to other random leaves more than once (or couples it and also"
       ++ " bounds it); measuring this exactly is an orthant probability,"
       ++ " which is out of scope by design (plan-guided-lazy-enumeration,"
       ++ " milestone 3 refusal rule)")
  | otherwise = Nothing
  where
    coupled = concat [[a, b] | (a, b) <- leafPairs w]
    contCon = [plcBase c | c <- leafCons w, isCont c]
    isCont PLeafCon{} = False
    isCont PLeafEq{}  = False
    isCont _          = True
    overCoupled = [ b | b <- coupled
                      , length (filter (== b) coupled) > 1 || b `elem` contCon ]

-- | Memo key of a user-function specialization: callee body chain name +
-- plan-argument offsets + deterministic arguments. Det args are keyed
-- syntactically on their generated IR (no normalization/constant folding is
-- attempted, so semantically equal but syntactically distinct arguments miss
-- the cache -- costs sharing, never correctness).
type PlanSpecKey = (ChainName, [Int], [String])

-- | Compile-time state of the milestone-2 specialization machinery: memoized
-- specializations (shared world lists; sound because worlds only reference
-- absolute plan offsets, top-level names, and once-bound argument variables),
-- and the active-specialization stack for the termination guard.
data PlanState = PlanState
  { psBoolMemo :: Map.Map PlanSpecKey ([PlanWorld], [PlanWorld])
  , psEnumMemo :: Map.Map PlanSpecKey [(IRExpr, PlanWorld)]
    -- | (callee body CN, sum of plan-argument offsets, 'psNextOff' at entry)
    -- per active specialization: re-entering a body already on the stack
    -- without strictly descending the plan cannot terminate and is declined,
    -- as is re-entering it after a neural read was opened since its entry
    -- (the opened read extends the offset space, so offsets no longer bound
    -- the recursion).
  , psStack    :: [(ChainName, Int, Int)]
    -- | Where the raw logit vectors live in the traversal's flat offset space
    -- ('PlanRaws'): the plan-bound read first, then one entry per nested
    -- neural read the traversal opened ('planOpenBinding'). The value grouping
    -- measures collapsed worlds against them in-flight (milestone 4), so each
    -- is bound before any world reading it is built.
  , psRaws     :: PlanRaws
    -- | The first offset not yet claimed by any read: where the next nested
    -- read's plan is placed.
  , psNextOff  :: Int
    -- | Whether the milestone-4 value grouping ('planGroupValues') may collapse
    -- same-value worlds into a single measured mass. Merging bakes a group's
    -- residual leaf constraints into one mass, so anything else constraining
    -- those leaves would double-count them. The traversal is first run with
    -- this on; merged worlds record what they baked ('wBaked'), meeting a
    -- baked leaf again marks a clash ('wClash'), and on a clash
    -- 'planWitnessApply' reruns with it off.
  , psMerge    :: Bool
    -- | Statically known values of the specialization argument variables
    -- ('planResolveApply' binds a non-trivial deterministic call-site argument
    -- to a fresh @spec_arg@ variable). A fold that threads a deterministic
    -- accumulator parameter -- @checksumSum (w+1) (rest ds)@ -- reads that
    -- variable in every per-level value, so without this environment the value
    -- (@spec_arg * d@) never folds to a constant and 'planGroupValues' merges
    -- nothing below the first level (task m4-grouping-for-value-reading-folds).
    -- Consulted only by the grouping's classification and when folding further
    -- argument bindings; the variables themselves are still emitted, so the
    -- generated IR is unchanged wherever grouping was already firing.
  , psDetConsts :: [(String, IRValue)]
    -- | The semiring the worlds are measured in ('semiringOf' the compile):
    -- the value grouping measures collapsed groups mid-traversal.
  , psSemiring :: Semiring
    -- | Whether a constructed value's fields may each be collapsed to one
    -- measured world before they are intersected ('planFieldProduct'), so an
    -- N-field construction costs a sum of the fields' world counts rather
    -- than their product. Like 'psMerge' it bakes leaves ('wBaked'), and a
    -- clash reruns the traversal with it off (then with 'psMerge' off too).
    -- Off whenever 'psMerge' is.
  , psFactor   :: Bool
    -- | Set once 'planFieldProduct' has collapsed some field: a clashing run
    -- that never factored gains nothing from a rerun with factoring off.
  , psFactored :: Bool
  }

-- | The state a traversal starts from: one read, bound at @nnRaw@, whose plan
-- occupies the first @size@ offsets.
emptyPlanState :: Semiring -> String -> Int -> Bool -> Bool -> PlanState
emptyPlanState sr nnRaw size merge factor = PlanState Map.empty Map.empty [] [(0, nnRaw)] size merge [] sr (merge && factor) False

-- ('CompilerM', the unapplied form: 'CompilerMonad' would be an unsaturated
-- synonym application here.)
type PlanM a = StateT PlanState CompilerM a

planAddGuard :: IRExpr -> PlanWorld -> PlanWorld
planAddGuard g w = w { wGuards = g : wGuards w }

andGuard :: IRExpr -> IRExpr -> IRExpr
andGuard a b | a == constTrueIR = b
             | b == constTrueIR = a
             | otherwise        = IROp OpAnd a b


-- | Intersect two constraints on the same region. Discrete regions keep the
-- slots allowed by both, conjoining their guards. Continuous leaves follow
-- the scalar 'intersectSet' conventions: interval-interval tightens the
-- bounds, a point absorbs an interval as membership guards, and point-point
-- keeps the first under a guard that the second agrees with it. A region cannot be discrete in one constraint
-- and continuous in another (the plan fixes each region's kind).
intersectLeafCon :: PLeafCon -> PLeafCon -> PLeafCon
intersectLeafCon c@(PLeafEq _ _ _ x p _) (PLeafEq _ _ _ x' p' _)
  | x == x' && p == p' = c
intersectLeafCon c@PLeafEq{} c' = intersectLeafCon (expandLeafEq c) c'
intersectLeafCon c c'@PLeafEq{} = intersectLeafCon c (expandLeafEq c')
intersectLeafCon (PLeafCon b s1) (PLeafCon _ s2) =
  PLeafCon b [ (i, andGuard g1 g2) | (i, g1) <- s1, Just g2 <- [lookup i s2] ]
intersectLeafCon (PLeafIvl b lo1 hi1) (PLeafIvl _ lo2 hi2) =
  PLeafIvl b (maxWBound lo1 lo2) (minWBound hi1 hi2)
intersectLeafCon (PLeafPt b v cov gs) (PLeafIvl _ lo hi) =
  PLeafPt b v cov (gs ++ boundGuards v lo hi)
intersectLeafCon (PLeafIvl _ lo hi) (PLeafPt b v cov gs) =
  PLeafPt b v cov (gs ++ boundGuards v lo hi)
-- Two points: keep the first, guarded on the second agreeing with it. Both
-- come from one observation, but not necessarily from the same component of
-- it -- @Scene (f (o1 sc)) (f (o1 sc))@ pins o1's leaf to the query's px of
-- each field -- so a query whose two points differ is impossible (task
-- plan-point-point-intersection-ignores-mismatch). The agreement is the float
-- equality of every point target ('leafEqIR', 'OpApprox'); a syntactically
-- identical point needs none. The second point's own image guards are kept.
intersectLeafCon (PLeafPt b v cov gs) (PLeafPt _ v' _ gs') =
  PLeafPt b v cov (gs ++ gs' ++ [leafEqIR TFloat v v' | v /= v'])
-- Invariant, not a refusal (task static-refusals-become-absent-variants): a leaf region is either discrete or continuous.
intersectLeafCon c c' = error ("plan leaf region at offset " ++ show (plcBase c)
  ++ " is constrained as both discrete and continuous (plan invariant violation): "
  ++ show (isDisc c) ++ " vs " ++ show (isDisc c'))
  where isDisc PLeafCon{} = True
        isDisc PLeafEq{}  = True
        isDisc _          = False

insertLeafCon :: PLeafCon -> [PLeafCon] -> [PLeafCon]
insertLeafCon c [] = [c]
insertLeafCon c (c':cs) | plcBase c == plcBase c' = intersectLeafCon c' c : cs
                        | otherwise               = c' : insertLeafCon c cs

intersectPlanW :: PlanWorld -> PlanWorld -> PlanWorld
intersectPlanW w1 w2 =
  planWorld (wGuards w1 ++ wGuards w2) (foldl (flip insertLeafCon) (leafCons w1) (leafCons w2))
            (nub (leafPairs w1 ++ leafPairs w2)) (wFactors w1 ++ wFactors w2)
            (wBaked w1 ++ wBaked w2) (wClash w1 || wClash w2 || touchesBaked (wBaked w1) w2 || touchesBaked (wBaked w2) w1)

-- | The leaf regions a world reads: its constrained leaves, its pairwise
-- couplings, and the leaves already folded into its factor.
pwLeaves :: PlanWorld -> [Int]
pwLeaves w = map plcBase (leafCons w) ++ concat [[a, b] | (a, b) <- leafPairs w] ++ wBaked w

-- | Does the world read any of these baked leaf regions? Meeting a baked leaf
-- again is a double count (see 'wBaked').
touchesBaked :: [Int] -> PlanWorld -> Bool
touchesBaked [] _ = False
touchesBaked bs w = any (`elem` bs) (pwLeaves w)

-- | Cross-intersect two world sets, dropping statically unsatisfiable
-- results. This is what keeps the world count of an if-chain over several
-- recursive predicates in check: cross-terms pinning contradictory scene
-- shapes (e.g. different lengths, via the same constructor-flag region) die
-- here instead of surviving as zero-mass worlds in the generated IR.
liveIntersects :: [PlanWorld] -> [PlanWorld] -> [PlanWorld]
liveIntersects ws1 ws2 = filter (not . pwUnsat) [ intersectPlanW a b | a <- ws1, b <- ws2 ]

-- | Bool-valued IR: is the deterministic value @val@ inside the target?
-- Mirrors the memberGuard / compareValueExpr conventions (approximate
-- equality for floats; False < True for Bool cumulatives).
--
-- A cumulative target recurses structurally exactly as 'compareValueExpr'
-- does: only an ordered scalar is tested with @not (val > s)@; a tuple is the
-- conjunction of its components, an Either matches the arm and recurses into
-- the payload, and a list takes the equality indicator. An ordering op on a
-- composite value means something different in every runtime and @<=@ in
-- none of them (task
-- plan-det-guard-compares-composite-values-with-greater-than).
planDetGuard :: RType -> IRExpr -> PTarget -> IRExpr
planDetGuard rt val (PTPoint s) = equalityGuardStatic rt s val
planDetGuard rt val (PTUpTo s) = planUpToGuard rt val s

-- | 'planDetGuard' on a cumulative target: Bool IR for @val <= s@.
planUpToGuard :: RType -> IRExpr -> IRExpr -> IRExpr
planUpToGuard rt val s = case rt of
  TBool       -> IROp OpOr (IRUnaryOp OpNot val) s
  TFloat      -> scalar
  TInt        -> scalar
  TVarR _     -> scalar
  TUnit       -> constTrueIR
  Tuple ft st -> IROp OpAnd (planUpToGuard ft (IRDestruct AcFst val) (IRDestruct AcFst s))
                            (planUpToGuard st (IRDestruct AcSnd val) (IRDestruct AcSnd s))
  TEither lr rr ->
    IRIf (IRDestruct AcIsLeft val)
      (IRIf (IRDestruct AcIsLeft s) (planUpToGuard lr (IRDestruct AcFromLeft val) (IRDestruct AcFromLeft s)) (IRConst (VBool False)))
      (IRIf (IRDestruct AcIsLeft s) (IRConst (VBool False)) (planUpToGuard rr (IRDestruct AcFromRight val) (IRDestruct AcFromRight s)))
  -- componentwise, as 'compareValueExpr' orders a list
  ListOf et | Just (h, t) <- listSpine val ->
    IRIf (IRUnaryOp OpIsAny s) constTrueIR
      (IRIf (IROp OpEq s (IRConst (VList EmptyList))) (IRConst (VBool False))
        (IROp OpAnd (planUpToGuard et h (IRDestruct AcHead s)) (planUpToGuard rt t (IRDestruct AcTail s))))
  ListOf _    -> equalityGuardStatic rt s val
  NullList    -> equalityGuardStatic rt s val
  TADT n      -> IRError (adtCdfMessage n)
  TSymbol     -> IRError symbolCdfMessage
  -- Invariant, mirroring 'compareValueExpr': a CDF comparison is only built
  -- for first-order result types.
  _           -> error $ "planDetGuard: cumulative comparison not implemented for type: " ++ show rt
  where scalar = IRUnaryOp OpNot (IROp OpGreaterThan val s)

-- | Combine the canonical (outcome-True, outcome-False) worlds of a
-- Bool-valued node against the actual target, mirroring 'comparisonWorlds'.
-- Statically decidable membership guards (the canonical polarity targets of
-- 'planInvertBool') are folded away here rather than left for the optimizer:
-- the milestone-2 dead-branch gating inspects worlds at compile time, so a
-- world excluded by its polarity must not survive with a False guard.
planBoolWorlds :: PTarget -> [PlanWorld] -> [PlanWorld] -> [PlanWorld]
planBoolWorlds tgt ts fs =
     attach (planDetGuard TBool constTrueIR tgt) ts
  ++ attach (planDetGuard TBool (IRConst (VBool False)) tgt) fs
  where
    attach g ws = case staticBool g of
      Just True  -> ws
      Just False -> []
      Nothing    -> map (planAddGuard g) ws

-- | Short node description for the fall-through diagnostic.
planNodeName :: Expr -> String
planNodeName (Expr _ (InjF (Named n) _)) = "InjF " ++ n
planNodeName (Expr _ (Var n))            = "Var " ++ n
planNodeName (Expr _ (Apply _ _))        = "Apply"
planNodeName (Expr _ (ReadNN n _))       = "ReadNN " ++ n
planNodeName e                    = head (words (show e))

-- | Field bases of an ADTPlan region at offset @off@: for each constructor
-- (in plan order), the flat offset where its field block starts. Mirrors the
-- constrIx arithmetic of AutoNeural.makeProbRec exactly.
adtCtorBases :: Int -> [(String, [PartitionPlan])] -> [Int]
adtCtorBases off ctorPlans = scanl (+) (off + adtFlagSlots ctorPlans) (map (sum . map getSize . snd) ctorPlans)

-- | Worlds constraining an ADT region's constructor flags to the allowed
-- (constructor index, guard) slots, on top of @cons@: the 'PLeafCon' of its
-- flag region. A lone constructor has no flag region ('adtFlagSlots'): its
-- flag is statically 1, so an allowed slot becomes a plain world guard, and
-- no allowed slot means no world (mass 0). Emitting a 'PLeafCon' at @off@
-- there would be wrong, not merely wasteful -- @off@ is then the first
-- field's region, and 'insertLeafCon' keys regions by their base offset.
adtFlagWorlds :: Int -> [(String, [PartitionPlan])] -> [(Int, IRExpr)] -> [PLeafCon] -> [PlanWorld]
adtFlagWorlds off ctorPlans slots cons
  | adtFlagSlots ctorPlans == 0 =
      [ if g == constTrueIR then pw1 cons else planAddGuard g (pw1 cons) | (0, g) <- slots ]
  | otherwise = [pw1 (insertLeafCon (PLeafCon off slots) cons)]

-- | Look up an ADT field accessor name across the declared ADTs: yields the
-- owning constructor's name and the field's index within it.
lookupADTAccessor :: [ADTDecl] -> String -> Maybe (String, Int)
lookupADTAccessor adtDecls' name = listToMaybe
  [ (cName, fj)
  | adt <- adtDecls', (cName, fields) <- constructors adt
  , Just fj <- [elemIndex name (map fst fields)] ]

-- | The fields (accessor name and type) of a declared ADT constructor, in field
-- order -- i.e. "is @name@ a constructor, and what does applying it take?".
-- Nullary constructors yield @Just []@.
lookupADTConstructor :: [ADTDecl] -> String -> Maybe [(String, RType)]
lookupADTConstructor adtDecls' name = listToMaybe
  [ fields | adt <- adtDecls', (cName, fields) <- constructors adt, cName == name ]

-- | Runtime test that @y@ carries constructor @nm@; False on a wildcard.
--
-- A world guard is no evaluation fence: the optimizer's CSE binds a guard's
-- subterms ahead of the conjunction that short-circuits them, so the
-- not-@ANY@ guard 'planAnySplit' puts first does not keep @is<Ctor>@ off a
-- wildcard sub-observation (task
-- writelogits-dropped-for-read-passthrough-continuous-leaf). The test is
-- total instead.
planIsCtor :: String -> IRExpr -> IRExpr
planIsCtor nm y = IRIf (IRUnaryOp OpIsAny y) (IRConst (VBool False)) (planIsCtorRaw nm y)

-- | @is<Ctor>@ itself, for a @y@ already known not to be a wildcard.
planIsCtorRaw :: String -> IRExpr -> IRExpr
planIsCtorRaw nm y = IRApply (IRVar ("is" ++ nm)) y

-- | Read field @f@ (of type @fty@) off an observation that only carries
-- constructor @nm@ on the branch the enclosing world guards.
--
-- The world guard cannot protect this read on its own: leaf constraints float
-- their deterministic sides out into let-bindings ('bindDetSide'), and
-- 'generateLetInBlock' emits those *outside* the guarded mass expression, where
-- they are evaluated unconditionally. An unguarded @tl y@ would then run against
-- an @Empty@ and crash the whole query rather than contributing zero. So the read
-- carries its own constructor test.
--
-- The else-branch is a canonical value of the field's type, NOT 'VAny': these
-- reads nest (@hd (tl y)@), so the fallback is itself fed to the next level's
-- @is<Ctor>@, and the convention everywhere else in the compiler is that
-- @is<Ctor>@ is only ever reached after an 'isAny' test (see the read-logits network's own
-- reader) -- 'isImpl' errors on a wildcard rather than answering it. A
-- well-formed dummy answers False cleanly and the chain stays total. Which
-- dummy is irrelevant: the enclosing guard discards the whole world.
--
-- A wildcard observation reads as a wildcard field (task
-- writelogits-dropped-for-read-passthrough-continuous-leaf): a partial-@ANY@
-- query puts @ANY@ where a field's sub-observation is read, and the read,
-- floated out of the world that 'planAnySplit' guards, must not reach
-- @is<Ctor>@ on it. Answering @ANY@ keeps the wildcard visible to the next
-- level's split.
planSafeField :: [ADTDecl] -> String -> String -> RType -> IRExpr -> Either String IRExpr
planSafeField adtDecls' nm f fty y = do
  dummy <- maybe (Left ("no canonical value for field type " ++ show fty ++ " of constructor " ++ nm)) Right
                 (planCanonicalValue adtDecls' [] fty)
  return (IRIf (IRUnaryOp OpIsAny y) (IRConst VAny)
                 (IRIf (planIsCtorRaw nm y) (IRApply (IRVar f) y) (IRConst dummy)))

-- | Some well-formed value of an RType, used only as a discarded placeholder
-- (see 'planSafeField'). For an ADT it prefers a nullary constructor, which is
-- what makes this terminate on recursive types; @seen@ breaks any remaining
-- cycle by refusing rather than looping.
planCanonicalValue :: [ADTDecl] -> [String] -> RType -> Maybe IRValue
planCanonicalValue adtDecls' seen ty = case ty of
  TFloat      -> Just (VFloat 0)
  TInt        -> Just (VInt 0)
  TBool       -> Just (VBool False)
  TUnit       -> Just VUnit
  TSymbol     -> Just (VSymbol "")
  ListOf _    -> Just (VList EmptyList)
  TTensor sh e -> VTensor sh . replicate (shapeNumel sh) <$> rec e
  Tuple a b   -> VTuple <$> rec a <*> rec b
  TEither l _ -> (VEither . Left) <$> rec l
  TADT n | n `notElem` seen -> do
    decl <- find ((== n) . dataName) adtDecls'
    let ctors = constructors decl
    (cn, fields) <- listToMaybe ([c | c@(_, []) <- ctors] ++ ctors)
    VADT cn <$> mapM (planCanonicalValue adtDecls' (n : seen) . snd) fields
  _ -> Nothing
  where rec = planCanonicalValue adtDecls' seen

-- | Generate-mode IR for a subtree that is deterministic given scope.
-- Inside a specialized callee body, occurrences of det-bound parameters
-- compile to @IRVar <param>@, which is unbound in the generated program --
-- rewrite them to their call-site values. (A blind name rewrite is safe:
-- callee bodies reference only their own parameters and top-level names, and
-- the substituted values are either constants or fresh compiler-generated
-- variables, which can collide with neither.)
planGenDet :: CompilerMetadata -> PlanEnv -> Expr -> PlanM IRExpr
planGenDet meta env e = do
  ir <- lift (toIRGenerate meta e)
  let substs = [(n, v) | (_, PBDet n v) <- env]
  if null substs
    then return ir
    else return (irMap (\x -> case x of IRVar n | Just v <- lookup n substs -> v; _ -> x) ir)

-- | Symbolically evaluate an accessor chain over an occurrence of a
-- plan-bound variable into a plan slice. Nothing: the expression is not such
-- a chain (the caller tries other rules). Just (Left why): it is, but the
-- plan shape does not support it. Descending an ADT field accessor
-- additionally emits the implied constructor-flag constraint (accessing a
-- field of C is only meaningful on the C branch of the distribution; the
-- accessor's mass is the flag's).
planEvalRef :: CompilerMetadata -> PlanEnv -> Expr -> Maybe (Either String (PlanRef, [PLeafCon]))
planEvalRef meta env = go
  where
    go e | Just b <- planEnvLookup env (chainName (getTypeInfo e)) = case b of
      PBPlan ref -> Just (Right (ref, []))
      PBDet _ _  -> Nothing
    go (Expr _ (InjF (Named "fst") [e])) = descend e $ \(PlanRef sub off) cons -> case sub of
      TuplePlan a _ -> Right (PlanRef a off, cons)
      _ -> Left "fst applied to a non-tuple plan slice"
    go (Expr _ (InjF (Named "snd") [e])) = descend e $ \(PlanRef sub off) cons -> case sub of
      TuplePlan a b -> Right (PlanRef b (off + getSize a), cons)
      _ -> Left "snd applied to a non-tuple plan slice"
    go (Expr _ (InjF (Named nm) [e]))
      | Just (cName, fj) <- lookupADTAccessor (adtDecls meta) nm =
          descend e $ \(PlanRef sub off) cons -> case sub of
            ADTPlan _ ctorPlans
              | Just ci <- elemIndex cName (map fst ctorPlans) ->
                  let fieldPlans = snd (ctorPlans !! ci)
                      fBase = (adtCtorBases off ctorPlans !! ci) + sum (map getSize (take fj fieldPlans))
                      -- a lone constructor has no flag region to pin ('adtFlagSlots')
                      cons' | adtFlagSlots ctorPlans == 0 = cons
                            | otherwise = insertLeafCon (PLeafCon off [(ci, constTrueIR)]) cons
                  in Right (PlanRef (fieldPlans !! fj) fBase, cons')
              | otherwise -> Left ("accessor " ++ nm ++ ": constructor " ++ cName ++ " is not present in the plan (depth-pruned)")
            _ -> Left ("accessor " ++ nm ++ " applied to a non-ADT plan slice")
    go _ = Nothing
    descend e k = fmap (>>= uncurry k) (go e)

-- | Worlds constraining a plan slice to lie in the target: Discretes leaves
-- (point and upto), component-wise tuple decomposition against a point, ADT
-- regions against a point, and Continuous leaves.
--
-- A nullary-constructor ADT region stays a single world, its flag slots each
-- guarded by is<Ctor> on the observed value. With *fields* that no longer
-- suffices -- each constructor carries different field constraints -- so the
-- region splits into one world per constructor, which is a partition (the
-- observation has exactly one constructor, and the guards are mutually
-- exclusive) and so sums correctly. Note the cost: c constructors per level of
-- a recursive ADT is c^depth worlds, the scaling rule recorded for plan leaves
-- in general. Marginalising the untaken constructors' field regions into one
-- world instead would remove the exponent; it is not attempted here.
--
-- A component's sub-observation (a tuple component, an ADT field) may be a
-- wildcard at run time: a partial-@ANY@ query such as @Scene Nil ANY@ against
-- a passed-through slice, which is what writeLogits asks for every
-- constructor flag. Each component is therefore split on it ('planAnySplit'),
-- as a constructed value's fields are. The components are crossed here, not
-- collapsed ('planFieldProduct'): collapsing bakes a field's leaves into one
-- mass, and an enclosing @if@ that tests one of them (@if isRed (color o) then
-- .. else o@) then clashes and reruns the whole traversal unfactored. A product
-- region's fields are kept factored one level up instead ('planRefConj').
-- The slice's own observation is never a wildcard: a whole @ANY@ is answered
-- before the traversal, and an enclosing component split guards it.
planRefWorlds :: [ADTDecl] -> PlanRef -> [PLeafCon] -> PTarget -> Either String [PlanWorld]
planRefWorlds _ (PlanRef (Discretes rty (MultiDiscretes vals)) off) cons tgt =
  Right [pw1 (insertLeafCon (con [ (i, planDetGuard rty (IRConst (valueToIR v)) tgt) | (i, v) <- zip [0..] vals ]) cons)]
  where con = case tgt of
          PTPoint s -> discreteEqCon off vals s True
          PTUpTo _  -> PLeafCon off
planRefWorlds adtDecls' (PlanRef (TuplePlan a b) off) cons (PTPoint s) = do
  wa <- component (PlanRef a off) (IRDestruct AcFst s)
  wb <- component (PlanRef b (off + getSize a)) (IRDestruct AcSnd s)
  return [ intersectPlanW x y | x <- [pw1 cons], y <- liveIntersects wa wb ]
  where
    component ref sub = planAnySplit sub <$> planRefWorlds adtDecls' ref [] (PTPoint sub)
planRefWorlds _ (PlanRef (ADTPlan _ ctorPlans) off) cons (PTPoint s)
  | all (null . snd) ctorPlans =
      Right (adtFlagWorlds off ctorPlans [ (i, planIsCtor cn s) | (i, (cn, _)) <- zip [0..] ctorPlans ] cons)
planRefWorlds adtDecls' (PlanRef (ADTPlan adtName ctorPlans) off) cons (PTPoint s) =
  concat <$> mapM ctorWorlds (zip3 [0 ..] ctorPlans (adtCtorBases off ctorPlans))
  where
    ctorWorlds (ci, (cn, fps), cbase) = do
      fields <- maybe (Left (missing cn)) Right (lookupADTConstructor adtDecls' cn)
      -- The flag slot carries the guard, so a world for the wrong constructor
      -- measures zero; the field reads below are individually safe anyway
      -- ('planSafeField'), since floated bindings escape the guard.
      let flagWorlds = adtFlagWorlds off ctorPlans [(ci, planIsCtor cn s)] cons
      fieldWorlds <- mapM (fieldW cn cbase fps) (zip3 [0 ..] fps fields)
      return (foldl liveIntersects flagWorlds fieldWorlds)
    fieldW cn cbase fps (j, fp, (fname, fty)) = do
      sub <- planSafeField adtDecls' cn fname fty s
      planAnySplit sub <$> planRefWorlds adtDecls' (PlanRef fp (cbase + sum (map getSize (take j fps)))) [] (PTPoint sub)
    missing cn = "constructor " ++ cn ++ " of ADT " ++ adtName ++ " is in the partition plan "
                 ++ "but not among the declared constructors"
planRefWorlds _ (PlanRef Continuous off) cons (PTPoint s) =
  Right [pw1 (insertLeafCon (PLeafPt off s const1 []) cons)]
planRefWorlds _ (PlanRef Continuous off) cons (PTUpTo s) =
  Right [pw1 (insertLeafCon (PLeafIvl off WNegInf (WFinite s)) cons)]
planRefWorlds _ (PlanRef sub _) _ _ =
  Left ("this plan slice cannot be matched against the observation directly: " ++ head (words (show sub)))

-- | One peeled step of a monotone chain over a continuous plan leaf, in the
-- direction the observation travels: observed value -> the step's operand.
data PeelStep = PeelStep
  { peelInv   :: IRExpr -> IRExpr  -- ^ the forward step's inverse
  , peelCov   :: IRExpr -> IRExpr  -- ^ |d operand / d observed| at the observed value
  , peelImage :: Image             -- ^ the forward step's image ('injFImage')
  }

-- | Peel invertible monotone float transforms off a plan-dependent operand
-- down to a Continuous plan slice (milestone 3). Supports the same static
-- envelope as ForwardChaining.stepMonotonicity: plus/neg/double/exp/log
-- unconditionally, mult only by a literal constant (any other deterministic
-- operand has no statically known direction). Yields the slice, its accessor
-- constraints, the chain's steps outermost first (compose them with
-- 'peelPoint' or 'peelBound'), and the chain's net monotonicity. Nothing:
-- not such a chain over a continuous slice -- the caller tries its other
-- rules (in particular, this deliberately declines chains bottoming out at
-- discrete slices, which the value-enumeration path already covers).
planPeelSlice :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Maybe (Either String (PlanRef, [PLeafCon], [PeelStep], Monotonicity)))
planPeelSlice meta env = go
  where
    go e | Just refE <- planEvalRef meta env e = return $ case refE of
      Right (ref@(PlanRef Continuous _), cons) ->
        Just (Right (ref, cons, [], MonInc))
      _ -> Nothing
    go (Expr _ (InjF (Named "neg") [a]))    = chain a "neg" (IRUnaryOp OpNeg) (const const1) MonDec
    go (Expr _ (InjF (Named "double") [a])) = chain a "double" (\b -> IROp OpDiv b (IRConst (VFloat 2))) (const (IRConst (VFloat 0.5))) MonInc
    go (Expr _ (InjF (Named "exp") [a]))    = chain a "exp" (IRUnaryOp OpLog) (\b -> IROp OpDiv const1 b) MonInc
    go (Expr _ (InjF (Named "log") [a]))    = chain a "log" (IRUnaryOp OpExp) (IRUnaryOp OpExp) MonInc
    go (Expr _ (InjF (Named "plus") [a, b]))
      | pdep a, pfree b = plusStep a b
      | pdep b, pfree a = plusStep b a
    go (Expr _ (InjF (Named "mult") [a, b]))
      | pdep a, pfree b = multStep a b
      | pdep b, pfree a = multStep b a
    go _ = return Nothing
    pdep = subtreeHasOcc (planEnvOccs env)
    pfree x = not (pdep x) && pType (getTypeInfo x) == Deterministic
    plusStep pe de = do
      d <- planGenDet meta env de
      chain pe "plus" (\b -> IROp OpSub b d) (const const1) MonInc
    multStep pe de = do
      d <- planGenDet meta env de
      case d of
        IRConst (VFloat f) | f /= 0 ->
          chain pe "mult" (\b -> IROp OpDiv b d) (const (IRConst (VFloat (1 / abs f))))
                   (if f > 0 then MonInc else MonDec)
        _ -> return (Just (Left "multiplication of a continuous plan leaf by a non-literal deterministic operand has no statically known monotonicity direction"))
    -- Prepend one peeled step (observed -> operand space) to the rest of
    -- the chain (operand space -> leaf space).
    chain pe name stepF covF stepDir = do
      innerM <- go pe
      return $ fmap (fmap (\(ref, cons, steps, dir) ->
        ( ref, cons
        , PeelStep stepF covF (injFImage name) : steps
        , if stepDir == MonDec then flipDir dir else dir ))) innerM
    flipDir MonInc = MonDec
    flipDir MonDec = MonInc

-- | Transport an observed POINT down a peeled chain: (leaf-space point,
-- |d leaf-space point / d observed point| change-of-variables factor, image
-- guards). A step whose forward image is not the whole line ('injFImage')
-- contributes 'imageGuards' on its own input -- a point the step can never
-- produce makes the world impossible rather than reaching the partial
-- inverse (@log@ of a negative observation is NaN, which used to become a
-- NaN probability; task set-witness-interval-partial-inverse). Such a step's
-- input is let-bound first so the guards, the inverse and the factor share
-- one evaluation; a full-image step binds nothing, keeping the emitted IR of
-- the pre-existing corpus unchanged.
peelPoint :: [PeelStep] -> IRExpr -> PlanM (IRExpr, IRExpr, [IRExpr])
peelPoint [] b = return (b, const1, [])
peelPoint (s : ss) b0 = do
  b <- bindPeelInput s b0
  (bi, covI, gs) <- peelPoint ss (peelInv s b)
  return (bi, mulCov (peelCov s b) covI, imageGuards (peelImage s) b ++ gs)
  where
    mulCov x y | x == const1 = y
               | y == const1 = x
               | otherwise   = IROp OpMult x y

-- | Transport an observed interval ENDPOINT down a peeled chain: the
-- leaf-space endpoint. Each step's input is clamped into the step's image
-- first ('clampToImage'), the same per-step discipline as
-- 'ForwardChaining.toSeededMonotoneInvExpr' -- a bound outside the image is
-- moved onto its boundary, which the inverse carries to the leaf's own
-- infinity, so an always-true comparison measures 1 and an always-false one
-- 0 instead of NaN. No change-of-variables factor: interval mass needs none.
peelBound :: [PeelStep] -> IRExpr -> PlanM IRExpr
peelBound [] b = return b
peelBound (s : ss) b0 = do
  b <- bindPeelInput s b0
  peelBound ss (peelInv s (clampToImage (peelImage s) b))

-- Let-bind a step's input when the step will read it more than once (only
-- a step with a proper sub-image does), unless it already is a variable.
bindPeelInput :: PeelStep -> IRExpr -> PlanM IRExpr
bindPeelInput s b
  | peelImage s == fullImage = return b
  | IRVar _ <- b = return b
  | otherwise = do
      v <- lift (mkVariable "peel_in")
      lift (setVariables [(v, b)])
      return (IRVar v)

-- | Diagnostic for a factor refused by 'planFactorExternals'.
planSharedSourceWhy :: String -> [String] -> Expr -> String
planSharedSourceWhy what vs sub = what
  ++ " is independent of the plan-bound variables but reads the enclosing random binding"
  ++ (if length vs > 1 then "s " else " ") ++ intercalate ", " (map show vs)
  ++ ": factorizing it would treat that shared draw as independent of its other uses ("
  ++ planNodeName sub ++ ")"

-- | Factorize a plan-free subtree that draws fresh randomness (task
-- plan-free-stochastic-subtree-not-factorized).
--
-- @subtreeHasOcc occs sub == False@ says the subtree mentions no plan-bound
-- variable. Every random draw in SPLL is a syntactic leaf, and the plan
-- traversal only ever descends into an inlined expression tree (a shared
-- @let@-bound draw would be an 'Apply' of a 'Lambda' and would be plan-free as
-- a WHOLE, reaching this case at that node instead), so a plan-free subtree
-- shares no draw with the plan leaves: it is genuinely independent, not merely
-- occurrence-free. Under independence the joint factorizes, so the subtree is
-- handed to the ordinary probability compiler against the same target and its
-- 'PResult' multiplied into the world ('prodP' in 'measureWorlds': dims and
-- branch counts add, so a continuous factor's dimension is accounted for
-- rather than assumed zero).
--
-- The sub-inference is compiled into a self-contained block (its own writer
-- scope folded in via 'generateLetInBlock'), exactly as 'residueFactor' does
-- for the set-witness path, so it may be evaluated under the world's guards.
planFactorFree :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planFactorFree meta env sub target
  -- see 'planEnvDetOccs': no rewrite of a specialized callee's parameters is
  -- available through a full inference compile
  | subtreeHasOcc (planEnvDetOccs env) sub =
      return (Left ("a subtree independent of the plan-bound variables draws fresh randomness and also reads a specialized parameter: "
                    ++ planNodeName sub))
  -- see 'planFactorExternals': refuse rather than silently assume independence
  | (vs@(_:_)) <- planFactorExternals (typeEnv meta) (recoveredVars meta) sub =
      return (Left (planSharedSourceWhy "a subtree" vs sub))
  | otherwise = do
      let (cumulative, sample) = case target of
            PTPoint s -> (False, s)
            PTUpTo  s -> (True,  s)
      block <- lift (scoped (toIRInference meta cumulative sub sample))
                 <&> generateLetInBlock meta
      fv <- lift (mkVariable "plan_factor")
      return (Right [(pw1 []) { wFactors = [WFactor (openWith [(fv, block)] (unpackResult fv))] }])

-- | The two polarity factors of a plan-free condition that draws fresh
-- randomness: @(P(c = True), P(c = False))@, each a self-contained compiled
-- block bound as the factor's one binding (as 'planFactorFree' binds its).
-- Same independence argument as 'planFactorFree' -- @c@ mentions no
-- plan-bound variable and shares no draw with the branches, so the if is a
-- mixture whose weights factor out of the plan measure.
planFactorBool :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String (WFactor, WFactor))
planFactorBool meta env c
  | subtreeHasOcc (planEnvDetOccs env) c =
      return (Left ("an if condition independent of the plan-bound variables draws fresh randomness and also reads a specialized parameter: "
                    ++ planNodeName c))
  | (vs@(_:_)) <- planFactorExternals (typeEnv meta) (recoveredVars meta) c =
      return (Left (planSharedSourceWhy "an if condition" vs c))
  | otherwise = do
      t <- polarity constTrueIR
      f <- polarity (IRConst (VBool False))
      return (Right (t, f))
  where
    polarity v = do
      block <- lift (scoped (toIRInference meta False c v))
                 <&> generateLetInBlock meta
      fv <- lift (mkVariable "plan_cond_factor")
      return (WFactor (openWith [(fv, block)] (unpackResult fv)))

-- | Attach an independent factor to a world.
planAddFactor :: WFactor -> PlanWorld -> PlanWorld
planAddFactor f w = w { wFactors = f : wFactors w }

-- | Invert the observation @body ∈ target@ into plan-leaf constraint worlds.
-- The plan-backed analogue of 'invertToWorlds'. Left carries a diagnostic
-- naming the unsupported node; the caller falls through to set-witnesses.
planInvert :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planInvert meta env planBody target
  -- Plan-free subtree: deterministic given scope reduces to a membership
  -- guard of its value against the target; anything else draws fresh
  -- randomness. (Det-bound parameter occurrences are deterministic here.)
  | not (subtreeHasOcc (planEnvOccs env) planBody) =
      if pType (getTypeInfo planBody) == Deterministic
        then do
          bIR <- planGenDet meta env planBody
          return (Right [planAddGuard (planDetGuard (rType (getTypeInfo planBody)) bIR target) (pw1 [])])
        else planFactorFree meta env planBody target
planInvert meta env planBody target
  | Just refE <- planEvalRef meta env planBody = case (refE, target) of
      (Left why, _) -> return (Left why)
      -- A point observation of a product region whose fields each split into
      -- several worlds: summed field by field, not crossed ('conjFlatten').
      (Right (ref, cons), PTPoint y) -> case planRefConj (adtDecls meta) ref cons y of
        Left why -> return (Left why)
        Right ks
          | conjMultiCount ks > 1 -> Right <$> conjFlatten ks
          | otherwise -> return (Right (foldl liveIntersects [pw1 []] ks))
      (Right (ref, cons), _) -> return (planRefWorlds (adtDecls meta) ref cons target)
-- A plan-dependent value shared by several children of this node is
-- enumerated once and the node traversed per value ('planShareSplit').
--
-- Only at a scalar node. After the split a case's body may be plan-free and is
-- then compared against the target whole ('planDetGuard'), which deliberately
-- has no wildcard checks below the top ('equalityGuardStatic'). A scalar
-- target is a value or a whole @ANY@ (short-circuited by 'planWitnessApply'),
-- but a structured one can be a partial wildcard, @(ANY, 1.0)@, that only the
-- field-by-field inversion ('planAnySplit') handles. A structured node is
-- therefore not a split point; a value shared inside one of its fields is
-- still split there, and value enumeration (no target) splits anywhere.
planInvert meta env planBody target = do
  shared <- if planScalarType (rType (getTypeInfo planBody))
    then planShareSplit meta env planBody (\m' env' b' -> fmap (map ((,) ())) <$> planInvert m' env' b' target)
    else return Nothing
  case shared of
    Just r  -> return (map snd <$> r)
    Nothing -> planInvertNode meta env planBody target

-- | 'planInvert' at a plan-dependent node that is neither a plan slice nor
-- split on a shared value: dispatch on the node.
planInvertNode :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planInvertNode meta env planBody target = case planBody of
  Expr _ (IfThenElse c t e)
    | not (subtreeHasOcc occs c) && pType (getTypeInfo c) == Deterministic -> do
        g <- planGenDet meta env c
        wsT <- planInvert meta env t target
        wsE <- planInvert meta env e target
        return ((\ts es -> map (planAddGuard g) ts ++ map (planAddGuard (IRUnaryOp OpNot g)) es) <$> wsT <*> wsE)
    -- A branch whose observation factors over the plan (a scene returned
    -- whole, or rebuilt field by field): see 'planInvertIfConj'.
    | subtreeHasOcc occs c, PTPoint _ <- target
    , planConjShape meta env t || planConjShape meta env e -> planInvertIfConj meta env c t e target
    | subtreeHasOcc occs c -> do
        cb <- planInvertBool meta env c
        case cb of
          Left why -> return (Left why)
          Right (cts0, cfs0) -> do
            -- Statically dead condition worlds gate their branch's traversal
            -- entirely; at the plan's depth boundary (where the recursive
            -- constructors are pruned) this is what terminates recursive
            -- predicate specialization.
            let cts = filter (not . pwUnsat) cts0
            let cfs = filter (not . pwUnsat) cfs0
            wsT <- if null cts then return (Right []) else planInvert meta env t target
            wsE <- if null cfs then return (Right []) else planInvert meta env e target
            return $ do
              ts <- wsT
              es <- wsE
              return (liveIntersects cts ts ++ liveIntersects cfs es)
    -- The condition is plan-free but stochastic: the if is an ordinary
    -- mixture whose two weights are independent of the plan, so each branch's
    -- worlds simply carry the corresponding polarity's mass as a factor.
    | otherwise -> do
        cf <- planFactorBool meta env c
        case cf of
          Left why -> return (Left why)
          Right (fT, fF) -> do
            wsT <- planInvert meta env t target
            wsE <- planInvert meta env e target
            return ((\ts es -> map (planAddFactor fT) ts ++ map (planAddFactor fF) es) <$> wsT <*> wsE)
  Expr _ (InjF (Named "not") [a]) -> do
    ab <- planInvertBool meta env a
    return ((\(t, f) -> planBoolWorlds target f t) <$> ab)
  Expr _ (InjF (Named "and") [a, b]) -> do
    ab <- planInvertBool meta env a
    bb <- planInvertBool meta env b
    return $ do
      (at, af) <- ab
      (bt, bf) <- bb
      let tw = liveIntersects at bt
      let fw = af ++ liveIntersects at bf
      return (planBoolWorlds target tw fw)
  Expr _ (InjF (Named "or") [a, b]) -> do
    ab <- planInvertBool meta env a
    bb <- planInvertBool meta env b
    return $ do
      (at, af) <- ab
      (bt, bf) <- bb
      let tw = at ++ liveIntersects af bt
      let fw = liveIntersects af bf
      return (planBoolWorlds target tw fw)
  Expr _ (InjF (Named nm) [a])
    | Just ctor <- ctorTestName nm -> case planEvalRef meta env a of
        Just (Right (PlanRef (ADTPlan _ ctorPlans) off, cons)) -> do
          let n = length ctorPlans
          let ci = elemIndex ctor (map fst ctorPlans)
          -- a constructor pruned from the plan (depth limit) simply has mass 0
          let inSet  = maybe [] (\i -> [(i, constTrueIR)]) ci
          let outSet = [ (i, constTrueIR) | i <- [0 .. n-1], Just i /= ci ]
          let tw = adtFlagWorlds off ctorPlans inSet  cons
          let fw = adtFlagWorlds off ctorPlans outSet cons
          return (Right (planBoolWorlds target tw fw))
        Just (Left why) -> return (Left why)
        _ -> return (Left (nm ++ " applied to something that is not a plan slice"))
  Expr _ (InjF (Named "eq") [a, b])
    | planDep a, isDetSide b -> planLeafEq a b
    | planDep b, isDetSide a -> planLeafEq b a
  Expr _ (InjF (Named "lt") [a, b]) -> planCmp False a b
  Expr _ (InjF (Named "gt") [a, b]) -> planCmp True  a b
  -- A directly applied literal lambda -- an inner @draw@, or a local function
  -- applied in place -- is beta-reduced away when its argument is
  -- deterministic given the plan ('planBetaReduce'); the reduced body is then
  -- traversed like any other.
  Expr _ (Apply lam@(Expr _ (Lambda x b)) a) -> do
    opened <- planOpenBinding meta env lam x b a
    case opened of
      Left why -> return (Left why)
      Right (env', b', cons) -> fmap (map (addSliceCons cons)) <$> planInvert meta env' b' target
  Expr _ (Apply {}) -> planApplyTarget meta env planBody target
  -- Arithmetic over plan-dependent operands at the observed position
  -- (@numRed scene + 1.0@): enumerate the node's values exactly as value
  -- enumeration already does under a comparison, and guard each against the
  -- target -- the same thing 'planApplyTarget' does for a value-returning call.
  --
  -- A monotone transform chain over a continuous leaf (@px (ob1 sc) - 1.0@,
  -- the moved object of a scene edit) has no values to enumerate; the
  -- observation is transported down the chain instead, as the comparison and
  -- equality cases already do ('planPeelSlice'): a point target pins the leaf
  -- at the inverse-transformed value with the chain's change-of-variables
  -- factor, an up-to target becomes the half-line the chain's direction
  -- selects (task scene-rebuild-with-float-leaf-loses-probability).
  Expr ti (InjF (Named nm) args)
    | nm `elem` ["plus", "mult", "neg", "double", "exp", "log"] || isJust (planArithOp nm (length args)) -> do
        peelM <- if nm `elem` ["plus", "mult", "neg", "double", "exp", "log"]
                   then planPeelSlice meta env planBody
                   else return Nothing
        case peelM of
          Just (Right (PlanRef _ off, cons, steps, dir)) -> case target of
            PTPoint s -> do
              (bnd, cov, imgGs) <- peelPoint steps s
              bv <- lift (mkVariable "obs_bnd")
              lift (setVariables [(bv, bnd)])
              return (Right [pw1 (insertLeafCon (PLeafPt off (IRVar bv) cov imgGs) cons)])
            PTUpTo s -> do
              bnd <- peelBound steps s
              bv <- lift (mkVariable "obs_bnd")
              lift (setVariables [(bv, bnd)])
              let ivl = if dir == MonInc then PLeafIvl off WNegInf (WFinite (IRVar bv))
                                         else PLeafIvl off (WFinite (IRVar bv)) WPosInf
              return (Right [pw1 (insertLeafCon ivl cons)])
          Just (Left why) -> return (Left why)
          Nothing
            | isJust (planArithOp nm (length args)) -> do
                vsE <- planEnumValues meta env planBody
                return ((\pairs -> [ planAddGuard (planDetGuard (rType ti) v target) w | (v, w) <- pairs ]) <$> vsE)
            | otherwise -> return (Left ("unsupported node in plan traversal: " ++ planNodeName planBody))
  -- Structural inversion of a built-in constructor: a tuple, a list cons, or an
  -- 'Either' injection. The user-ADT case below, spelled for the built-in
  -- accessors: the observation must have this shape, and each field's
  -- observation is pushed onto the corresponding argument.
  Expr _ (InjF (Named "TCons") [a, b]) ->
    planInvertFields "tuple" Nothing [(a, IRDestruct AcFst), (b, IRDestruct AcSnd)]
  Expr _ (InjF (Named "Cons") [h, t]) ->
    let nonEmpty y = notIR (IROp OpEq y (IRConst (VList EmptyList)))
    in case planCanonicalValue (adtDecls meta) [] (rType (getTypeInfo h)) of
         Nothing -> return (Left ("no canonical value for list element type " ++ show (rType (getTypeInfo h))))
         Just dummy -> planInvertFields "list cons" (Just nonEmpty)
           [ (h, \y -> IRIf (nonEmpty y) (IRDestruct AcHead y) (IRConst dummy))
           , (t, \y -> IRIf (nonEmpty y) (IRDestruct AcTail y) (IRConst (VList EmptyList))) ]
  Expr _ (InjF (Named inj) [a])
    | Just (test, proj) <- lookup inj [("left", (AcIsLeft, AcFromLeft)), ("right", (AcIsRight, AcFromRight))] ->
        case planCanonicalValue (adtDecls meta) [] (rType (getTypeInfo a)) of
          Nothing -> return (Left ("no canonical value for the payload type " ++ show (rType (getTypeInfo a)) ++ " of " ++ inj))
          Just dummy -> planInvertFields inj (Just (IRDestruct test))
            [ (a, \y -> IRIf (IRDestruct test y) (IRDestruct proj y) (IRConst dummy)) ]
  -- Structural inversion of a *constructed* ADT value. The observation must
  -- carry this constructor, and each field's observation is pushed onto the
  -- corresponding argument, the field worlds intersecting. This is what keeps a
  -- structure-returning body linear in the term: the alternative -- enumerating
  -- the constructed type -- is its whole (depth-unrolled) support.
  -- A wholly deterministic construction never reaches here; it is compared as a
  -- value by the plan-free case at the top of 'planInvert'.
  Expr _ (InjF (Named nm) args)
    | Just fields <- lookupADTConstructor (adtDecls meta) nm
    , length fields == length args -> case target of
        -- A cumulative target orders values; a constructed ADT has no such order
        -- to push through its fields.
        PTUpTo _ -> return (Left ("cumulative target on the constructed ADT value " ++ nm))
        PTPoint y -> case mapM (\(f, fty) -> planSafeField (adtDecls meta) nm f fty y) fields of
          Left why -> return (Left why)
          Right subTargets -> do
            fieldsE <- zipWithM (\a s -> fmap (planAnySplit s) <$> planInvert meta env a (PTPoint s)) args subTargets
            case sequence fieldsE of
              Left why -> return (Left why)
              Right wss -> Right . map (planAddGuard (planIsCtor nm y)) <$> planFieldProduct wss
  _ -> return (Left ("unsupported node in plan traversal: " ++ planNodeName planBody))
  where
    occs = planEnvOccs env
    -- Push a point observation through a built-in constructor: @guardY@ is
    -- the runtime shape test on the observation (none for a tuple), each
    -- component's sub-observation is read off it by a total projection (the
    -- guard only protects the world's mass, not the let-bindings leaf
    -- constraints float out -- see 'planSafeField'), and the component worlds
    -- intersect. A component whose sub-observation is a wildcard at run time
    -- is unconstrained: 'planAnySplit' partitions on that.
    planInvertFields what guardY comps = case target of
      PTUpTo _ -> return (Left ("cumulative target on the constructed " ++ what ++ " value"))
      PTPoint y -> do
        fieldsE <- mapM (\(e, sub) -> fmap (planAnySplit (sub y)) <$> planInvert meta env e (PTPoint (sub y))) comps
        case sequence fieldsE of
          Left why -> return (Left why)
          Right wss -> do
            ws <- planFieldProduct wss
            return (Right (maybe ws (\g -> map (planAddGuard (g y)) ws) guardY))
    planDep = subtreeHasOcc occs
    isDetSide  x = not (subtreeHasOcc occs x) && pType (getTypeInfo x) == Deterministic
    ctorTestName nm
      | "is" `isPrefixOf` nm
      , drop 2 nm `elem` concatMap (map fst . constructors) (adtDecls meta) = Just (drop 2 nm)
      | otherwise = Nothing
    bindDetSide suffix de = do
      d  <- planGenDet meta env de
      dv <- lift (mkVariable suffix)
      lift (setVariables [(dv, d)])
      return dv
    planLeafEq pe de = case planEvalRef meta env pe of
        Just (Right (PlanRef (Discretes rty (MultiDiscretes vals)) off, cons)) -> do
          dv <- bindDetSide "eq_rhs" de
          let eqG v = planDetGuard rty (IRConst (valueToIR v)) (PTPoint (IRVar dv))
          let eqCon pol = discreteEqCon off vals (IRVar dv) pol
          let tw = [pw1 (insertLeafCon (eqCon True  [ (i, eqG v)                    | (i, v) <- zip [0..] vals ]) cons)]
          let fw = [pw1 (insertLeafCon (eqCon False [ (i, IRUnaryOp OpNot (eqG v)) | (i, v) <- zip [0..] vals ]) cons)]
          return (Right (planBoolWorlds target tw fw))
        Just (Right (PlanRef (ADTPlan _ ctorPlans) off, cons)) | all (null . snd) ctorPlans -> do
          dv <- bindDetSide "eq_rhs" de
          let isG cn = IRApply (IRVar ("is" ++ cn)) (IRVar dv)
          let tw = adtFlagWorlds off ctorPlans [ (i, isG cn)                    | (i, (cn, _)) <- zip [0..] ctorPlans ] cons
          let fw = adtFlagWorlds off ctorPlans [ (i, IRUnaryOp OpNot (isG cn)) | (i, (cn, _)) <- zip [0..] ctorPlans ] cons
          return (Right (planBoolWorlds target tw fw))
        -- Continuous leaf pinned to a deterministic value (milestone 3): the
        -- True outcome is a point constraint (dim-1 density); the False
        -- outcome leaves the leaf free -- the complement of a point is a
        -- full-measure set (the point is a null set).
        Just (Right (PlanRef Continuous off, cons)) -> do
          dv <- bindDetSide "eq_rhs" de
          contEqWorlds off cons (IRVar dv) const1 []
        Just (Left why) -> return (Left why)
        _ -> do
          peelM <- planPeelSlice meta env pe
          case peelM of
            -- A monotone transform chain over a continuous leaf (milestone
            -- 3): pin the leaf at the inverse-transformed value, with the
            -- change-of-variables factor of the inverse chain.
            Just (Right (PlanRef _ off, cons, steps, _)) -> do
              dv <- bindDetSide "eq_rhs" de
              (bnd, cov, imgGs) <- peelPoint steps (IRVar dv)
              bv <- lift (mkVariable "eq_bnd")
              lift (setVariables [(bv, bnd)])
              contEqWorlds off cons (IRVar bv) cov imgGs
            Just (Left why) -> return (Left why)
            -- Not a continuous shape: enumerate the plan-dependent side's
            -- values (milestone 2) and guard each against the deterministic
            -- side.
            Nothing -> do
              vsE <- planEnumValues meta env pe
              case vsE of
                Left why -> return (Left why)
                Right pairs -> do
                  dv <- bindDetSide "eq_rhs" de
                  let rt = rType (getTypeInfo pe)
                  let eqG v = planDetGuard rt v (PTPoint (IRVar dv))
                  let tw = [ planAddGuard (eqG v) w                    | (v, w) <- pairs ]
                  let fw = [ planAddGuard (IRUnaryOp OpNot (eqG v)) w | (v, w) <- pairs ]
                  return (Right (planBoolWorlds target tw fw))
    -- @gs@: image guards from 'peelPoint' -- the True outcome is impossible
    -- (its world measures zero, the point never evaluated) when the observed
    -- value lies outside some peeled step's image; the False outcome is the
    -- complement of a null set either way.
    contEqWorlds off cons v cov gs = do
      let tw = [pw1 (insertLeafCon (PLeafPt off v cov gs) cons)]
      let fw = [pw1 cons]
      return (Right (planBoolWorlds target tw fw))
    -- Comparison of an enum leaf against a deterministic bound: each leaf
    -- value is statically known, so the outcome split is a per-slot guard.
    planCmp isGT a b
      | planDep a, isDetSide b = leafCmp a b isGT False
      | planDep b, isDetSide a = leafCmp b a isGT True
      | planDep a, planDep b   = coupleCmp a b isGT
      | otherwise = return (Left "comparison: some side is neither plan-dependent nor deterministic (it draws fresh randomness)")
    leafCmp pe de isGT flipped = case planEvalRef meta env pe of
      Just (Right (PlanRef (Discretes _ (MultiDiscretes vals)) off, cons)) -> do
        dv <- bindDetSide "cmp_rhs" de
        let op = if isGT /= flipped then OpGreaterThan else OpLessThan
        let cmpG v = IROp op (IRConst (valueToIR v)) (IRVar dv)
        let tw = [pw1 (insertLeafCon (PLeafCon off [ (i, cmpG v)                    | (i, v) <- zip [0..] vals ]) cons)]
        let fw = [pw1 (insertLeafCon (PLeafCon off [ (i, IRUnaryOp OpNot (cmpG v)) | (i, v) <- zip [0..] vals ]) cons)]
        return (Right (planBoolWorlds target tw fw))
      -- Continuous leaf against a deterministic bound (milestone 3): the
      -- outcomes are complementary half-lines on the leaf, measured as
      -- Gaussian CDF differences. Interval mass is dim 0, like set-witnesses.
      Just (Right (PlanRef Continuous off, cons)) -> do
        dv <- bindDetSide "cmp_rhs" de
        contCmpWorlds off cons (IRVar dv) (isGT /= flipped)
      Just (Left why) -> return (Left why)
      _ -> do
        peelM <- planPeelSlice meta env pe
        case peelM of
          -- A monotone transform chain over a continuous leaf (milestone 3):
          -- transport the bound through the inverse chain; a net-decreasing
          -- chain flips which half-line the True outcome selects.
          Just (Right (PlanRef _ off, cons, steps, dir)) -> do
            dv <- bindDetSide "cmp_rhs" de
            bnd <- peelBound steps (IRVar dv)
            bv <- lift (mkVariable "cmp_bnd")
            lift (setVariables [(bv, bnd)])
            contCmpWorlds off cons (IRVar bv) ((isGT /= flipped) == (dir == MonInc))
          Just (Left why) -> return (Left why)
          -- Not a continuous shape: enumerate the plan-dependent side's
          -- values (milestone 2 -- the counting-fold-vs-bound shape).
          Nothing -> do
            vsE <- planEnumValues meta env pe
            case vsE of
              Left why -> return (Left why)
              Right pairs -> do
                dv <- bindDetSide "cmp_rhs" de
                let op = if isGT /= flipped then OpGreaterThan else OpLessThan
                let cmpG v = IROp op v (IRVar dv)
                let tw = [ planAddGuard (cmpG v) w                    | (v, w) <- pairs ]
                let fw = [ planAddGuard (IRUnaryOp OpNot (cmpG v)) w | (v, w) <- pairs ]
                return (Right (planBoolWorlds target tw fw))
    -- Worlds of (continuous leaf@off > bound) when gtLeaf, else (leaf < bound).
    contCmpWorlds off cons bnd gtLeaf = do
      let upper = pw1 (insertLeafCon (PLeafIvl off (WFinite bnd) WPosInf) cons)
      let lower = pw1 (insertLeafCon (PLeafIvl off WNegInf (WFinite bnd)) cons)
      let (tw, fw) = if gtLeaf then ([upper], [lower]) else ([lower], [upper])
      return (Right (planBoolWorlds target tw fw))
    -- Comparison of two plan-dependent sides (milestone 3): a single
    -- pairwise coupling of two continuous leaves, measured in closed form
    -- via the difference Gaussian. Transform chains on a coupled side are
    -- out of scope (only bare slices couple); 'pwOverCoupled' refuses any
    -- world that constrains a coupled leaf twice.
    coupleCmp ae be isGT = case (planEvalRef meta env ae, planEvalRef meta env be) of
      (Just (Right (PlanRef Continuous offA, consA)), Just (Right (PlanRef Continuous offB, consB))) -> do
        let cons = foldr insertLeafCon consB consA
        if offA == offB
          -- the same leaf compared against itself: statically False
          then return (Right (planBoolWorlds target [] [pw1 cons]))
          else do
            let mkW pr = planWorld [] cons [pr] [] [] False
            let tw = [mkW (if isGT then (offA, offB) else (offB, offA))]
            let fw = [mkW (if isGT then (offB, offA) else (offA, offB))]
            return (Right (planBoolWorlds target tw fw))
      (Just (Left why), _) -> return (Left why)
      (_, Just (Left why)) -> return (Left why)
      _ -> return (Left "a comparison with both sides plan-dependent is only supported between two continuous plan leaves (single pairwise coupling)")

-- | A conjunction of world disjunctions (task
-- scene-count-conditional-edit-exponential): the worlds of an observation that
-- factors over disjoint parts of the plan, kept factored instead of crossed.
-- Each conjunct is a world list in the usual sense (a partition of its event);
-- the conjunction's worlds are the cross intersection of the conjuncts. Built
-- only through 'conjAdd', which keeps the conjuncts' leaf footprints pairwise
-- disjoint, so the cross product is a product of independent masses.
--
-- Two things use the factored form. 'conjFlatten' sums each conjunct into one
-- world before crossing them -- the distributive law, @prod_i sum_j m_ij@
-- instead of @sum over all combinations@ -- which is what makes a point
-- observation of an N-slot product scene N worlds instead of c^N. And an @if@
-- whose condition counts over the slots absorbs each slot's conjunct into that
-- slot's summand before the count is value-grouped ('planEnumAbsorb'), the DP
-- over (slot, count so far) instead of one world per scene path.
type PlanConj = [[PlanWorld]]

-- | The leaf regions a disjunction reads.
conjLeaves :: [PlanWorld] -> [Int]
conjLeaves = nub . concatMap pwLeaves

-- | Conjoin a disjunction onto a factored conjunction, keeping the conjuncts
-- leaf-disjoint: every conjunct sharing a leaf with it is crossed into it.
conjAdd :: [PlanWorld] -> PlanConj -> PlanConj
conjAdd d ks =
  let ls = conjLeaves d
      overlaps k = any (`elem` ls) (conjLeaves k)
      (hit, miss) = (filter overlaps ks, filter (not . overlaps) ks)
  in miss ++ [foldl liveIntersects d hit]

-- | How many conjuncts split into several worlds: below two, crossing them
-- does not multiply.
conjMultiCount :: PlanConj -> Int
conjMultiCount = length . filter ((> 1) . length)

-- | Conjoin several conjunctions.
conjAll :: [PlanConj] -> PlanConj
conjAll = foldl (foldr conjAdd) []

-- | The flat world list of a factored conjunction: the conjuncts, being
-- leaf-disjoint, are exactly the independent "fields" 'planFieldProduct'
-- collapses one by one before crossing (when two or more split), under its
-- 'psFactor' gate and clash retry.
conjFlatten :: PlanConj -> PlanM [PlanWorld]
conjFlatten = planFieldProduct

-- | Does the observation of this node factor over the plan? A slice of a
-- single-constructor (product) ADT region with several fields, or a
-- user-constructor application with several arguments. Static, so the
-- factored @if@ path is chosen without traversing anything.
planConjShape :: CompilerMetadata -> PlanEnv -> Expr -> Bool
planConjShape meta env e = case planEvalRef meta env e of
  Just (Right (PlanRef (ADTPlan _ [(_, fps)]) _, _)) -> length fps > 1
  Just _ -> False
  Nothing -> case e of
    Expr _ (InjF (Named nm) args) | Just fields <- lookupADTConstructor (adtDecls meta) nm ->
      length fields == length args && length args > 1 && subtreeHasOcc (planEnvOccs env) e
    _ -> False

-- | 'planInvert' in factored form: a point observation of a product region or
-- of a constructed ADT value is one conjunct per field (plus the constructor
-- test), anything else is the single conjunct 'planInvert' returns.
planInvertConj :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String PlanConj)
planInvertConj meta env e target@(PTPoint y)
  | subtreeHasOcc (planEnvOccs env) e
  , Just (Right (ref, cons)) <- planEvalRef meta env e =
      return (planRefConj (adtDecls meta) ref cons y)
  | Expr _ (InjF (Named nm) args) <- e
  , subtreeHasOcc (planEnvOccs env) e
  , Nothing <- planEvalRef meta env e
  , Just fields <- lookupADTConstructor (adtDecls meta) nm
  , length fields == length args =
      case mapM (\(f, fty) -> planSafeField (adtDecls meta) nm f fty y) fields of
        Left why -> return (Left why)
        Right subTargets -> do
          fieldsE <- zipWithM (\a s -> fmap (conjAnySplit s) <$> planInvertConj meta env a (PTPoint s)) args subTargets
          return (conjAll . ([[planAddGuard (planIsCtor nm y) (pw1 [])]] :) <$> sequence fieldsE)
  | otherwise = fmap (: []) <$> planInvert meta env e target
planInvertConj meta env e target = fmap (: []) <$> planInvert meta env e target

-- | 'planRefWorlds' against a point, in factored form: a lone constructor's
-- fields are independent regions, so each is its own conjunct. A field's
-- sub-observation may be a wildcard, so each of its conjuncts is split on it
-- ('conjAnySplit').
planRefConj :: [ADTDecl] -> PlanRef -> [PLeafCon] -> IRExpr -> Either String PlanConj
planRefConj adtDecls' (PlanRef (ADTPlan adtName [(cn, fps)]) off) cons s
  | not (null fps) = do
      fields <- maybe (Left ("constructor " ++ cn ++ " of ADT " ++ adtName ++ " is in the partition plan but not among the declared constructors")) Right
                      (lookupADTConstructor adtDecls' cn)
      let flagWorlds = adtFlagWorlds off [(cn, fps)] [(0, planIsCtor cn s)] cons
          cbase = head (adtCtorBases off [(cn, fps)])
      fieldConjs <- forM (zip3 [0 ..] fps fields) $ \(j, fp, (fname, fty)) -> do
        sub <- planSafeField adtDecls' cn fname fty s
        conjAnySplit sub <$> planRefConj adtDecls' (PlanRef fp (cbase + sum (map getSize (take j fps)))) [] sub
      return (conjAll ([flagWorlds] : fieldConjs))
planRefConj adtDecls' ref cons s = (: []) <$> planRefWorlds adtDecls' ref cons (PTPoint s)

-- | 'planAnySplit' over a factored conjunction, one conjunct at a time. When
-- the sub-observation is a wildcard every conjunct takes its unconstrained
-- world (mass 1 each); otherwise every conjunct takes its own worlds. A
-- combination of the two has contradictory guards and measures 0, so the
-- conjunction still partitions.
conjAnySplit :: IRExpr -> PlanConj -> PlanConj
conjAnySplit s = map (planAnySplit s)

-- | The plan regions a subtree can read, as half-open flat-offset ranges:
-- every maximal plan slice it mentions, plus the accessor constraints on the
-- way to it. Static and conservative. A callee body only reaches the plan
-- through its arguments, so a call's footprint is its arguments'. Nothing
-- when a local binding or lambda could carry the plan somewhere this does not
-- look (the caller then absorbs nothing).
planFootprint :: CompilerMetadata -> PlanEnv -> Expr -> Maybe [(Int, Int)]
planFootprint meta env = go
  where
    occs = planEnvOccs env
    go e
      | not (subtreeHasOcc occs e) = Just []
      | Just r <- planEvalRef meta env e = case r of
          Right (PlanRef p off, cons) -> Just ((off, off + getSize p) : [ (plcBase c, plcBase c + 1) | c <- cons ])
          Left _ -> Nothing
      | otherwise = case e of
          Expr _ (Lambda _ _) -> Nothing
          Expr _ (Apply (Expr _ (Lambda _ _)) _) -> Nothing
          Expr _ (ReadNN _ _) -> Nothing
          _ -> concat <$> mapM go (getSubExprs e)

inRanges :: [(Int, Int)] -> Int -> Bool
inRanges rs b = any (\(lo, hi) -> lo <= b && b < hi) rs

-- | Run a traversal with the value grouping off and fresh specialization
-- memos (so neither ungrouped results leak into the grouped memo nor grouped
-- ones are reused here), restoring both afterwards.
planUngroupedLocally :: PlanM a -> PlanM a
planUngroupedLocally act = do
  st0 <- get
  put st0 { psMerge = False, psFactor = False, psBoolMemo = Map.empty, psEnumMemo = Map.empty }
  r <- act
  st1 <- get
  put st1 { psMerge = psMerge st0, psFactor = psFactor st0, psBoolMemo = psBoolMemo st0, psEnumMemo = psEnumMemo st0 }
  return r

-- | Run a traversal for its result only: its variable bindings are dropped and
-- the plan state and name supply rewound, so it leaves no trace in the IR.
-- The result's worlds may name dropped variables; use only their structure.
planProbe :: PlanM a -> PlanM a
planProbe act = do
  st0 <- get
  sup0 <- lift get
  r <- lift (openValue <$> scoped (fst <$> runStateT act st0))
  lift (put sup0)
  return r

-- | 'planEnumValues' with conjuncts absorbed (task
-- scene-count-conditional-edit-exponential). Each conjunct is pushed down an
-- arithmetic node into the one operand whose static footprint
-- ('planFootprint') holds all of its leaves while no other operand's touches
-- them, and at the bottom it is intersected into that operand's worlds
-- /before/ they are value-grouped. The grouped masses then already carry the
-- conjunct, and the operands stay leaf-disjoint, so nothing clashes: for a
-- count over the slots of a product scene observed slot by slot, this is the
-- DP over (slot, count so far). The operand receiving a conjunct is
-- enumerated ungrouped below that point ('planUngroupedLocally'), since its
-- own grouped masses would bake the leaves the conjunct constrains.
--
-- Returns the (value, world) pairs, the conjuncts not absorbed (to be
-- intersected by the caller as usual), and whether anything was absorbed.
-- Sound for any assignment: a conjunct intersected into some operand's
-- partition still yields a partition of (value, conjunct) outcomes.
planEnumAbsorb :: CompilerMetadata -> PlanEnv -> PlanConj -> Expr -> PlanM (Either String ([(IRExpr, PlanWorld)], PlanConj, Bool))
planEnumAbsorb meta env ks e
  | null ks = fmap (\ps -> (ps, [], False)) <$> planEnumValues meta env e
  | Expr _ (InjF (Named nm) args) <- e
  , Just f <- planArithOp nm (length args)
  , all (subtreeHasOcc (planEnvOccs env)) args
  , Just fps <- mapM (planFootprint meta env) args =
      let owner k = case [ i | (i, fp) <- zip [0 :: Int ..] fps, any (inRanges fp) (conjLeaves k) ] of
            [i] | all (inRanges (fps !! i)) (conjLeaves k), not (null (conjLeaves k)) -> Just i
            _ -> Nothing
          owned = [ (k, owner k) | k <- ks ]
          leftover = [ k | (k, Nothing) <- owned ]
      in if all (isNothing . snd) owned
        then fmap (\ps -> (ps, ks, False)) <$> planEnumValues meta env e
        else do
          rs <- forM (zip [0 :: Int ..] args) $ \(i, a) ->
            planEnumAbsorb meta env [ k | (k, Just j) <- owned, j == i ] a
          case sequence rs of
            Left why -> return (Left why)
            Right parts -> do
              let combos = filter (not . pwUnsat . snd)
                    [ (f (map fst c), foldl1 intersectPlanW (map snd c)) | c <- sequence [ ps | (ps, _, _) <- parts ] ]
              grouped <- planGroupValues combos
              return (Right (grouped, leftover ++ concat [ l | (_, l, _) <- parts ], True))
  | otherwise = do
      rawE <- planUngroupedLocally (planEnumValues meta env e)
      case rawE of
        Left why -> return (Left why)
        Right raw -> do
          let pairs = filter (not . pwUnsat . snd)
                [ (v, foldl intersectPlanW w combo) | (v, w) <- raw, combo <- sequence ks ]
          grouped <- planGroupValues pairs
          return (Right (grouped, [], True))

-- | 'planInvert' of a Bool condition against a polarity target, absorbing
-- conjuncts into it where it is a comparison of an arithmetic value with a
-- deterministic side ('planEnumAbsorb'); anything else is inverted as usual
-- and hands every conjunct back.
planInvertAbsorb :: CompilerMetadata -> PlanEnv -> PlanConj -> Expr -> PTarget -> PlanM (Either String ([PlanWorld], PlanConj, Bool))
planInvertAbsorb meta env ks c target = case c of
  Expr _ (InjF (Named op) [a, b])
    | op `elem` ["gt", "lt", "eq"], absorbable a, isDetSide b -> via op a b False
    | op `elem` ["gt", "lt", "eq"], absorbable b, isDetSide a -> via op b a True
  _ -> plain
  where
    occs = planEnvOccs env
    plain = fmap (\ws -> (ws, ks, False)) <$> planInvert meta env c target
    isDetSide x = not (subtreeHasOcc occs x) && pType (getTypeInfo x) == Deterministic
    absorbable x = case x of
      Expr _ (InjF (Named nm) args) -> isJust (planArithOp nm (length args)) && all (subtreeHasOcc occs) args
      _ -> False
    via op pe de flipped = do
      r <- planEnumAbsorb meta env ks pe
      case r of
        Left why -> return (Left why)
        Right (pairs, left, absorbed) -> do
          d <- planGenDet meta env de
          dv <- lift (mkVariable (if op == "eq" then "eq_rhs" else "cmp_rhs"))
          lift (setVariables [(dv, d)])
          let rt = rType (getTypeInfo pe)
              holds v = case op of
                "eq" -> planDetGuard rt v (PTPoint (IRVar dv))
                _    -> IROp (if (op == "gt") /= flipped then OpGreaterThan else OpLessThan) v (IRVar dv)
              tw = [ planAddGuard (holds v) w                    | (v, w) <- pairs ]
              fw = [ planAddGuard (IRUnaryOp OpNot (holds v)) w | (v, w) <- pairs ]
          return (Right (planBoolWorlds target tw fw, left, absorbed))

-- | The factored inversion of @if c then t else e@ against a point target,
-- for a plan-dependent condition and a branch whose observation factors
-- ('planConjShape'). Each branch's observation is kept as conjuncts, the
-- condition absorbs what it can of them ('planInvertAbsorb'), and the rest is
-- conjoined and flattened ('conjFlatten'). Dead-branch gating is decided on a
-- probe of the condition ('planProbe'), as the unfactored path decides it on
-- the condition's worlds: a branch whose polarity is statically impossible is
-- never traversed.
planInvertIfConj :: CompilerMetadata -> PlanEnv -> Expr -> Expr -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planInvertIfConj meta env c t e target = do
  probe <- planProbe (planInvertBool meta env c)
  case probe of
    Left why -> return (Left why)
    Right (cts0, cfs0) -> do
      let live = not . all pwUnsat
      wsT <- if live cts0 then branch t constTrueIR else return (Right [])
      wsE <- if live cfs0 then branch e constFalseIR else return (Right [])
      return ((++) <$> wsT <*> wsE)
  where
    -- The branch's conjuncts are first built as usual. A conjunct that comes
    -- back value-grouped has baked the leaves the condition's summands read,
    -- so absorbing it clashes; the branch is then rebuilt with its own
    -- grouping off ('planUngroupedLocally') and absorbed again. The grouped
    -- attempt is discarded without trace ('planAttempt').
    branch b pol = do
      r <- planAttempt (absorbInto False b pol)
      maybe (fst <$> absorbInto True b pol) return r
    absorbInto ungrouped b pol = do
      kE <- (if ungrouped then planUngroupedLocally else id) (planInvertConj meta env b target)
      case kE of
        Left why -> return (Left why, True)
        Right ks -> do
          cE <- planInvertAbsorb meta env ks c (PTPoint pol)
          case cE of
            Left why -> return (Left why, True)
            Right (cws, left, _) -> do
              ws <- conjFlatten (conjAdd (filter (not . pwUnsat) cws) left)
              return (Right ws, not (any wClash cws))

-- | Run a traversal that reports whether its result is usable; when it is not,
-- discard it without trace (its bindings dropped, the plan state and name
-- supply rewound) and answer Nothing.
planAttempt :: PlanM (a, Bool) -> PlanM (Maybe a)
planAttempt act = either (const Nothing) Just <$> planAttemptEither ((\(r, ok) -> if ok then Right r else Left ()) <$> act)

-- | 'planAttempt' whose failure carries what the caller needs to retry: a
-- 'Right' is kept, a 'Left' is discarded without trace and returned.
planAttemptEither :: PlanM (Either e a) -> PlanM (Either e a)
planAttemptEither act = do
  st0 <- get
  sup0 <- lift get
  o <- lift (scoped (runStateT act st0))
  let (r, st1) = openValue o
  case r of
    Right _ -> void (lift (inline o)) >> put st1 >> return r
    Left _  -> lift (put sup0) >> put st0 >> return r

-- | Worlds of one constructor component whose sub-observation @s@ may be a
-- wildcard at run time (a partial-@ANY@ query such as @(ANY, 1.0)@): a world
-- leaving the component unconstrained when @s@ is @ANY@, and the component's
-- own worlds, each guarded on @s@ not being @ANY@, otherwise. The two guards
-- partition, and the not-@ANY@ test is the outermost guard of each world, so
-- nothing below it ever compares against the wildcard.
planAnySplit :: IRExpr -> [PlanWorld] -> [PlanWorld]
planAnySplit s ws =
  planAddGuard (IRUnaryOp OpIsAny s) (pw1 [])
    : map (planAddGuard (notIR (IRUnaryOp OpIsAny s))) ws

-- | Arithmetic InjFs that value enumeration ('planEnumValuesRaw') combines
-- pointwise, by name and arity: the IR of the forward function applied to
-- the operands' enumerated values. Every entry is total, so no applicability
-- guard is needed on an enumerated value.
planArithOp :: String -> Int -> Maybe ([IRExpr] -> IRExpr)
-- The arity errors below are invariants: the closures are only ever applied
-- to as many values as the arity they were selected for.
planArithOp nm 2
  | Just op <- lookup nm [("plus", OpPlus), ("plusI", OpPlus), ("mult", OpMult), ("multI", OpMult), ("max", OpMax)] =
      Just (\vs -> case vs of
                     [a, b] -> IROp op a b
                     _      -> error ("planArithOp: binary " ++ nm ++ " applied to " ++ show (length vs) ++ " values"))
planArithOp nm 1
  | nm `elem` ["neg", "negI"] = Just (unary (IRUnaryOp OpNeg))
  | nm == "double"            = Just (unary (\a -> IROp OpMult a (IRConst (VFloat 2))))
  where unary f vs = case vs of
          [a] -> f a
          _   -> error ("planArithOp: unary " ++ nm ++ " applied to " ++ show (length vs) ++ " values")
planArithOp _ _ = Nothing

-- | Is @e@ deterministic once the plan-bound variables are fixed? That is: it
-- draws no randomness of its own, so every copy of it denotes the same value
-- -- the one property that makes substituting it for a bound variable sound
-- under SPLL's eager @draw@ (a copy of a fresh draw would be a second,
-- independent draw). Plan-free subtrees answer from their 'pType'; a plan-bound
-- or specialized-parameter occurrence is deterministic by construction; an
-- InjF or @if@ is deterministic when its operands are; a call to a top-level
-- function is when the function draws nothing given deterministic arguments
-- ('detGenNames', from the call-graph fixpoint of 'SPLL.Typing.Determinism')
-- and its arguments are; a nested directly applied lambda is when its argument
-- is and its reduced body is. Anything else -- a neural read, a bare lambda
-- over the plan -- answers False, which only costs coverage.
planDetGivenPlan :: CompilerMetadata -> PlanEnv -> Expr -> Bool
planDetGivenPlan meta env = go
  where
    occs = planEnvOccs env
    go e
      | isJust (planEnvLookup env (chainName (getTypeInfo e))) = True
      | not (subtreeHasOcc occs e) = pType (getTypeInfo e) == Deterministic
    go (Expr _ (InjF _ args)) = all go args
    go (Expr _ (IfThenElse c t f)) = go c && go t && go f
    go (Expr _ (Apply (Expr _ (Lambda x b)) a)) = go a && go (substituteVar x a b)
    go e@(Expr _ (Apply _ _))
      | (Expr _ (Var n), args@(_:_)) <- flattenApplySpine e
      , isJust (lookup n (functions (compilingProgram meta)))
      , (n ++ "_gen") `Set.member` detGenNames meta = all go args
    go _ = False

-- | Beta-reduce a directly applied literal lambda met by the plan traversal:
-- an inner @draw x = a in b@, or a local function applied in place,
-- @(\\s -> p s) a@. The result is @b[x := a]@, traversed in its place.
--
-- Sound exactly when @a@ is deterministic given the plan ('planDetGivenPlan'):
-- then every copy of @a@ reads the same plan leaves and computes the same
-- value, so the eager binding and its substitution agree. A random @a@ is
-- refused -- two copies of it would be two independent draws.
--
-- This descends into a @draw@, which the traversal otherwise never does, and
-- 'planFactorExternals' relies on that: a factor is refused if it reads a
-- random local of the ambient scope, because the traversal cannot see where
-- else that local's single draw is used. Substitution keeps the guard
-- correct rather than weakening it: @x@ does not survive into the reduced
-- body, so no new local enters the scope any factor could read, and the only
-- bindings reduced are those whose value is not a draw at all.
planBetaReduce :: CompilerMetadata -> PlanEnv -> String -> Expr -> Expr -> Either String Expr
planBetaReduce meta env x b a
  | planDetGivenPlan meta env a = Right (substituteVar x a b)
  | otherwise = Left ("a binding inside the plan traversal is not deterministic given the plan-bound variables "
                      ++ "(substituting it would duplicate its draw): " ++ x ++ " = " ++ planNodeName a)

-- | Open a directly applied literal lambda met by the plan traversal: either
-- beta-reduce it ('planBetaReduce', its argument deterministic given the plan)
-- or, when its argument is a fresh neural read, make that read a second plan
-- of the same traversal (task plan-pairwise-across-separate-neural-reads).
--
-- @draw a = readX s1 in draw b = readX s2 in a < b@ is the shape: one read per
-- object, compared pairwise. Two reads are independent draws, so their joint
-- plan is the concatenation of the two plans and a world's mass is the
-- product over the leaves it constrains, whichever read they belong to. The
-- inner read therefore gets its own disjoint range of flat offsets (from
-- 'psNextOff'), its raw logit vector a binding of its own ('psRaws', read by
-- 'planRawRead'), and its bound variable a 'PBPlan' entry in the environment;
-- the body is then traversed as usual. A comparison of a leaf of each read is
-- the same 'leafPairs' difference Gaussian as one inside a single read, and a
-- world that leaves the inner read unconstrained measures its free marginal of
-- 1.
--
-- Each traversal of the binding opens a fresh range. That matches evaluation:
-- the traversal visits a binding once per world family it builds, and two
-- visits of the same syntax (two arms of an @if@, two values of a split) are
-- alternatives, whose worlds are summed and never intersected.
--
-- Inside a specialized function this holds too (task
-- plan-neural-read-inside-specialized-function): two calls of one helper are
-- two traversals of its body, so each opens its own range, provided neither
-- reuses the other's memoized worlds. 'planSpecializeBool' and
-- 'planSpecializeEnum' therefore never memoize a specialization whose
-- traversal opened a read, and 'planEnterSpec' declines to re-enter a body on
-- the stack once a read was opened below it (the fresh offsets would let a
-- recursion that reads at every level "descend" forever). The symbol argument
-- may read the helper's deterministic parameters: they are bound to
-- call-site values ahead of every world.
--
-- Refused, with a diagnostic, and so falling back exactly as before: a symbol
-- argument that is not plan-free and deterministic, since the read is bound
-- once, ahead of every world.
planOpenBinding :: CompilerMetadata -> PlanEnv -> Expr -> String -> Expr -> Expr -> PlanM (Either String (PlanEnv, Expr, [PLeafCon]))
planOpenBinding meta env lam x b a = case planBetaReduce meta env x b a of
  Right b' -> return (Right (env, b', []))
  Left why
    | Just (nnName, plan, symArg, readNode) <- planProjectedReadOf meta a -> do
        let symFree = not (subtreeHasOcc (planEnvOccs env) symArg)
                      && pType (getTypeInfo symArg) == Deterministic
        if not symFree
            then return (Left ("a nested neural read's argument is not deterministic and free of the plan-bound variables: "
                               ++ x ++ " = " ++ planNodeName a))
            else do
              sym <- planGenDet meta env symArg
              raw <- lift (mkVariable "nn_raw")
              lift (setVariables [(raw, IRApply (IRVar nnName) sym)])
              off <- gets psNextOff
              modify (\st -> st { psRaws = psRaws st ++ [(off, raw)], psNextOff = off + getSize plan })
              let fcd = fcData meta
                  lamCN = chainName (getTypeInfo lam)
                  resolvedCN = case findEquivalentExpression fcd lamCN of
                    Just (rCN, LambdaInfo _ _, _) -> rCN
                    _ -> lamCN
                  occs = fromMaybe [] (Map.lookup resolvedCN (lambdaVarOccurrences fcd))
              -- A projected read binds its slice, the accessors' constructor
              -- flags constraining every world of the body.
              return ((\(ref, cons) -> ((occs, PBPlan ref) : env, b, cons))
                        <$> planProjectedSlice meta plan off readNode a)
    | otherwise -> return (Left why)

-- | Share one plan-dependent value among the children of a node (task
-- plan-fold-disjunction-of-comparisons-blowup).
--
-- A sub-expression that is deterministic given the plan but is not itself a
-- plan slice -- a fold's result, @checksumSum 1 ds@ -- denotes one value
-- however many times it is spelled. Traversed once per spelling, as
-- @(f ds == 0) || (f ds == 10)@ or the copies 'planBetaReduce' makes of
-- @draw s = f ds in (s == 0) || (s == 10)@ would be, each copy enumerates the
-- value separately, and the value grouping bakes the same leaves into both
-- copies' worlds. Intersecting them is then a clash, and the traversal reruns
-- with grouping off -- one world per scene path, exponential in the fold's
-- depth.
--
-- Instead, when such a sub-expression occurs in two or more children of this
-- node (it is shared HERE, not merely inside one child, which splits it at a
-- lower node and keeps the split local), its (value, world) pairs are
-- enumerated once ('planEnumValues'), every occurrence is replaced by a fresh
-- variable (the nodes it frees of the plan re-typed 'Deterministic'), and the node is
-- traversed once per value with that variable bound 'PBDet' to it. This is the
-- value split 'planResolveApply' performs for a helper applied to a fold result
-- (@isValid (checksumSum 1 ds)@), applied to an implicit binding instead of a
-- call argument; soundness is the same. The value worlds partition the
-- outcomes, every occurrence evaluates to that value within a world (it is
-- deterministic given the plan), and given the value the node's worlds
-- partition its own, so intersecting each case's worlds with its value world is
-- again a partition. A node that also reads the value's leaves some other way
-- clashes as before and reruns ungrouped; nothing new is unsound.
--
-- Occurrences are searched and replaced outside lambdas only, so every one
-- sees the same bindings. Candidates are tried outermost first; if the first
-- shared one cannot be enumerated the node is traversed as before (Nothing),
-- so this only ever adds coverage (at worst leaving the failed enumeration's
-- bindings dead in the emitted code).
planShareSplit :: CompilerMetadata -> PlanEnv -> Expr
               -> (CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(a, PlanWorld)]))
               -> PlanM (Maybe (Either String [(a, PlanWorld)]))
planShareSplit meta env e k = case sharedCand of
  Nothing -> return Nothing
  Just s -> do
    vsE <- planEnumValues meta env s
    case vsE of
      Left _ -> return Nothing
      Right pairs -> do
        x <- lift (mkVariable "shared")
        let rty = rType (getTypeInfo s)
        let meta' = meta { typeEnv = (x, (rty, False)) : typeEnv meta }
        let e' = replaceOcc s x e
        rs <- forM pairs $ \(v, w) -> do
          vb <- case v of
            IRConst _ -> return v
            IRVar _   -> return v
            _ -> do
              nm <- lift (mkVariable "shared_val")
              lift (setVariables [(nm, v)])
              return (IRVar nm)
          r <- k meta' (([], PBDet x vb) : env) e'
          return (inCase w <$> r)
        return (Just (concat <$> sequence rs))
  where
    occs = planEnvOccs env
    kids = case e of
      Expr _ (Lambda _ _) -> []
      _ -> getSubExprs e
    -- sub-expressions outside lambdas, outermost first
    subterms (Expr _ (Lambda _ _)) = []
    subterms t = t : concatMap subterms (getSubExprs t)
    isCand t = case t of
      Expr _ (Var _) -> False
      _ -> subtreeHasOcc occs t
           && isNothing (planEvalRef meta env t)
           && not (isArrowT (rType (getTypeInfo t)))
           && planDetGivenPlan meta env t
    isArrowT (TArrow _ _) = True
    isArrowT _            = False
    inKid t kid = any (sameTerm t) (subterms kid)
    -- Two children whose worlds are intersected. An if's two arms are not:
    -- they are alternatives in disjoint worlds, so copies in both arms never
    -- meet and cannot clash, and splitting there only re-traverses the node
    -- once per value. In a recursive fold that branches into the same
    -- recursive call from both arms (planEnumRecJointState's go) that was
    -- the whole recursion's value set enumerated at every level: 2 s -> 36 s.
    meet i j = i /= j && not (isIf && i > 0 && j > 0)
    isIf = case e of
      Expr _ IfThenElse{} -> True
      _ -> False
    sharedCand = listToMaybe
      [ t | (i, kid) <- zip [0 :: Int ..] kids, t <- subterms kid
          , any (\(j, kid') -> meet i j && inKid t kid') (zip [0 ..] kids)
          , isCand t ]
    -- Replace the occurrences by the variable. A node the replacement leaves
    -- free of plan occurrences was deterministic given the plan before it
    -- ('planDetGivenPlan': det InjF/if, a det-generating call, ...), so it is
    -- now deterministic outright and is re-typed as such here, directly, on
    -- 'planDetGivenPlan''s verdict (the syntactic re-typing this module used
    -- to have stopped at a call such as @isValidB x@).
    replaceOcc s x t
      | sameTerm s t = Expr ((getTypeInfo t) { pType = Deterministic }) (Var x)
      | Expr _ (Lambda _ _) <- t = t
      | otherwise =
          let t'@(Expr ti' n') = setSubExprs t (map (replaceOcc s x) (getSubExprs t))
          in if not (subtreeHasOcc occs t') && planDetGivenPlan meta env t
               then Expr (ti' { pType = Deterministic }) n'
               else t'
    inCase w ps
      | planWorldTrivial w = ps
      | otherwise = filter (not . pwUnsat . snd) [ (a, intersectPlanW w bw) | (a, bw) <- ps ]

-- | A type whose observation cannot be a partial wildcard: the node types at
-- which 'planInvert' may split on a shared value ('planShareSplit').
planScalarType :: RType -> Bool
planScalarType rt = rt `elem` [TBool, TInt, TFloat]

-- | Structural equality of two expressions, ignoring every annotation.
sameTerm :: Expr -> Expr -> Bool
sameTerm (Expr _ n1) (Expr _ n2) =
  fmap (const ()) n1 == fmap (const ()) n2
    && and (zipWith sameTerm (foldr (:) [] n1) (foldr (:) [] n2))

-- | Canonical (outcome-True, outcome-False) worlds of a Bool-valued node.
planInvertBool :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String ([PlanWorld], [PlanWorld]))
planInvertBool meta env e = do
  t <- planInvert meta env e (PTPoint constTrueIR)
  f <- planInvert meta env e (PTPoint (IRConst (VBool False)))
  return ((,) <$> t <*> f)

-- | The milestone-4 value-grouped DP ('planGroupValues') applied to the Bool
-- path. A predicate's (True-worlds, False-worlds) pair is already a partition
-- by value -- the same precondition the counting-fold DP relies on -- so each
-- polarity's worlds may be collapsed into one world carrying their summed
-- mass. Without this a per-level DISJUNCTION multiplies the shared recursive
-- continuation instead of summing beside it: a predicate whose per-level test
-- reaches its recursive call through @c@ disjoint worlds (an @Object@ ADT with
-- @c@ constructors, or a @&&@ over two plan leaves) enumerates @c^depth@
-- worlds. Grouping restores the distributive law -- @P(f k) = [sum of the
-- level's local worlds] * P(f (k+1))@ -- making it polynomial.
--
-- Soundness is exactly 'planGroupValues'' (partition, 'commonDiscreteCons'
-- kept live, gated on 'psMerge'); this only supplies Bool-valued pairs to it.
planGroupBool :: ([PlanWorld], [PlanWorld]) -> PlanM ([PlanWorld], [PlanWorld])
planGroupBool (ts, fs) = do
  grouped <- planGroupValues ([(constTrueIR, w) | w <- ts] ++ [(constFalseIR, w) | w <- fs])
  return ( [w | (v, w) <- grouped, v == constTrueIR]
         , [w | (v, w) <- grouped, v /= constTrueIR] )

-- | Fold an IR value expression into a constant Value, when possible.
-- Counting-fold values are always statically foldable (literal increments
-- combined by plus); anything else is left ungrouped by the value DP
-- ('planGroupValues').
--
-- This carries a substitution environment because of how deterministic
-- sub-expressions are GENERATED, not because the language needs one. A fold
-- that threads an automaton STATE through deterministic arguments decides its
-- result with an if-chain over those arguments (@if red then 1 else if met ==
-- 1 then 2 else 0@), and the @==@ InjF emits its operands as let-bindings
-- rather than inline: @let a = 0 in let b = 1 in a == b@. Folding only
-- 'IRConst'/'OpPlus'/'OpMult' therefore returned Nothing for the whole value,
-- 'planGroupValues' classified the pair unmergeable, and the DP never fired at
-- any recursion level -- measured as a CONSTANT number of merges (12) from
-- depth 4 to depth 6 while the pair count grew 22 -> 342, of which 341 were
-- kept ungrouped. Specialization memoization was never the problem there
-- (measured 19 distinct keys at depth 4, 31 at depth 6 -- linear, ~6 per level,
-- exactly the joint states); the pair list was.
--
-- The environment holds let-bound constants met while folding, seeded by the
-- caller with the specialization arguments of known value ('psDetConsts').
foldConstIn :: [(String, IRValue)] -> IRExpr -> Maybe IRValue
foldConstIn _   (IRConst v) = Just v
foldConstIn env (IRVar n)   = lookup n env
foldConstIn env (IRLetIn n v b) = do
  vv <- foldConstIn env v
  foldConstIn ((n, vv) : env) b
foldConstIn env (IRIf c t e) = do
  b <- staticBoolIn env c
  foldConstIn env (if b then t else e)
foldConstIn env (IROp op a b) = do
  va <- foldConstIn env a
  vb <- foldConstIn env b
  case op of
    OpPlus -> num (+) va vb
    OpSub  -> num (-) va vb
    OpMult -> num (*) va vb
    OpEq   -> Just (VBool (va == vb))
    _      -> Nothing
  where
    num f (VFloat x) (VFloat y) = Just (VFloat (f x y))
    num f (VInt  x)  (VInt  y)  = Just (VInt (round (f (fromIntegral x :: Double) (fromIntegral y))))
    num _ _ _                   = Nothing
-- Source subtraction @a - b@ desugars to @plus a (neg b)@, i.e. IR
-- @OpPlus a (OpNeg b)@, so without this case an accumulator updated by
-- subtraction (@checksumSum (4 - w)@) never folds and the M4 grouping merges
-- nothing below the first level (task plan-fold-subtraction-accumulator-blowup).
foldConstIn env (IRUnaryOp OpNeg a) = do
  va <- foldConstIn env a
  case va of
    VFloat x -> Just (VFloat (negate x))
    VInt x   -> Just (VInt (negate x))
    _        -> Nothing
foldConstIn _ _ = Nothing

-- | 'staticBool' under the same environment, so a condition spelled as a
-- let-bound comparison decides just as an inline one does.
staticBoolIn :: [(String, IRValue)] -> IRExpr -> Maybe Bool
staticBoolIn env e = case foldConstIn env e of
  Just (VBool b) -> Just b
  _              -> staticBool e

-- | Milestone-4 value-grouped DP: collapse (value, world) pairs that share a
-- statically-known value into one world carrying the summed mass, bound to a
-- fresh IR variable so the mass is shared rather than re-inlined at every
-- recursion level. This is what turns counting folds from 2^depth enumerated
-- worlds into O(depth) value groups per level -- the
-- [[materialized-marginals-semiring]] idea in its first concrete consumer.
-- Soundness rests on three things: the (value, world) pairs are a partition, so
-- summing a same-value subset is exactly P(value = v); constraints shared
-- identically by every world of a group stay LIVE ('commonDiscreteCons') so an
-- outer re-constraint still dedups; and the residual leaves baked into the
-- mass are recorded ('wBaked'), so anything re-constraining one of them is
-- caught as a clash and the traversal reruns with merging off ('psMerge',
-- 'planWitnessApply'). Only all-dim-0, uncoupled worlds with a foldable value
-- are merged; multi-world groups collapse (a singleton keeps its constraints, so no
-- premature commitment), and anything non-foldable or carrying a point/pair
-- constraint passes through untouched.
planGroupValues :: [(IRExpr, PlanWorld)] -> PlanM [(IRExpr, PlanWorld)]
planGroupValues pairs = do
  merge <- gets psMerge
  raws <- gets psRaws
  consts <- gets psDetConsts
  sr <- gets psSemiring
  let (mergeable, keep) = partitionEithers (map (classify consts) pairs)
      -- group same-value worlds, keeping ascending value-key order for
      -- reproducible IR
      grouped = Map.elems (Map.fromListWith comb mergeable)
  if not merge
    -- unsafe to collapse (the fold shares leaves with a sibling predicate);
    -- keep the milestone-2 world-per-path enumeration unchanged
    then return pairs
    else do
      merged <- mapM (mergeGroup sr raws) grouped
      return (merged ++ keep)
  where
    -- the value may read specialization argument variables of known value
    -- (a threaded deterministic accumulator); see 'psDetConsts'
    classify consts (ve, w)
      | Just v <- foldConstIn consts ve, canMerge w = Left (show v, (v, [w]))
      | otherwise                                   = Right (ve, w)
    -- A world carrying an independent sub-inference factor is never merged:
    -- 'planWorldMass' (which is what a group's collapsed mass is built from)
    -- measures the plan leaves only, so baking a group would silently drop
    -- the factor. Such worlds pass through ungrouped.
    canMerge w = null (leafPairs w) && null (pwSubFactors w) && not (any isPt (leafCons w))
    isPt PLeafPt{} = True
    isPt _         = False
    comb (v, ws1) (_, ws2) = (v, ws1 ++ ws2)
    mergeGroup _ _ (v, [w]) = return (IRConst v, w)
    -- Merge same-value worlds. Constraints shared identically by every world
    -- in the group (a discrete leaf region with the same slots+guards -- in
    -- practice the recursion's accessor/constructor flags) are kept LIVE on the
    -- collapsed world, so an outer context re-constraining that leaf still
    -- dedups via 'intersectLeafCon' instead of double-counting it. Only the
    -- residual (the internal randomness that varies across the group, disjoint
    -- from anything constrained outside) is baked into the summed mass factor.
    mergeGroup sr raws (v, ws) = do
      let common = planCommonDiscreteCons ws
          residual w = withLeafCons (filter (\c -> not (any (planConEq c) common)) (leafCons w)) w
      let groupMass = sumAllSR sr (map (planWorldMass sr raws . residual) ws)
      mv <- lift (mkVariable "cnt_mass")
      lift (setVariables [(mv, groupMass)])
      -- the residual leaves are now hidden inside the mass: record them, with
      -- whatever the members had already baked, so a later constraint on one
      -- of them is caught as a double count ('wBaked')
      let baked = nub (concatMap (\w -> map plcBase (leafCons (residual w)) ++ wBaked w) ws)
      return (IRConst v, planWorld [] common [] [WMass (IRVar mv)] baked (any wClash ws))

-- | Discrete leaf constraints present (identically) in every world's cons:
-- what a collapsed group keeps live ('planGroupValues', 'planFieldProduct').
planCommonDiscreteCons :: [PlanWorld] -> [PLeafCon]
planCommonDiscreteCons (w:ws') =
  [ c | c <- leafCons w, isDiscrete c, all (\w' -> any (planConEq c) (leafCons w')) ws' ]
  where isDiscrete PLeafCon{} = True
        isDiscrete PLeafEq{}  = True
        isDiscrete _          = False
planCommonDiscreteCons [] = []

planConEq :: PLeafCon -> PLeafCon -> Bool
planConEq (PLeafCon b1 s1) (PLeafCon b2 s2) = b1 == b2 && s1 == s2
planConEq (PLeafEq b1 _ _ x1 p1 _) (PLeafEq b2 _ _ x2 p2 _) = b1 == b2 && x1 == x2 && p1 == p2
planConEq _ _ = False

-- | The worlds of a constructed value, from its fields' worlds: their
-- cross-intersection. Each field's worlds partition that field's ways of
-- meeting its sub-observation, so the cross product is a partition of the
-- whole -- but its size is the PRODUCT of the fields' world counts, which for
-- a per-slot edit over an N-slot scene (@Scene (f (o1 sc)) .. (f (oN sc))@,
-- task scene-float-passthrough-edit-exponential) is c^N.
--
-- When two or more fields have several worlds, each such field is instead
-- collapsed to ONE world before intersecting: a field's mass is the sum of
-- its worlds' masses, and since the sum over the cross product of products is
-- the product of the per-field sums (distributivity, which the dimension-
-- aware 'mixP' / 'prodP' pair also satisfies), the measure is unchanged.
-- What a field's worlds share identically ('planCommonDiscreteCons', e.g. the
-- scene's own constructor flag) stays live; the residual is measured once
-- and carried as a factor -- a 'WMass' when every world is dim 0 and
-- uncoupled (so an enclosing value DP can still merge it), else a whole
-- measured 'PResult' ('measureWorlds', which handles point densities and
-- couplings). That is sound exactly when nothing else constrains the residual
-- leaves: they are recorded in 'wBaked', and meeting one again is a clash on
-- which 'planWitnessApply' reruns with 'psFactor' off -- the cross product
-- as before. A field holding an over-coupled world is never collapsed, so
-- 'pwOverCoupled' still sees it at the end.
planFieldProduct :: [[PlanWorld]] -> PlanM [PlanWorld]
planFieldProduct wss = do
  factor <- gets psFactor
  let wss' = map (filter (not . pwUnsat)) wss
      multi = length (filter ((> 1) . length) wss')
  if not factor || multi < 2
    then return (foldl liveIntersects [pw1 []] wss)
    else do
      collapsed <- mapM collapseField wss'
      return (foldl liveIntersects [pw1 []] collapsed)
  where
    collapseField :: [PlanWorld] -> PlanM [PlanWorld]
    collapseField ws
      | length ws <= 1 || any (isJust . pwOverCoupled) ws = return ws
      | otherwise = do
          sr <- gets psSemiring
          raws <- gets psRaws
          modify (\st -> st { psFactored = True })
          let common = planCommonDiscreteCons ws
              residual w = withLeafCons (filter (\c -> not (any (planConEq c) common)) (leafCons w)) w
              rs = map residual ws
              baked = nub (concatMap pwLeaves rs)
              clash = any wClash ws
          if all mergeable rs
            then do
              mv <- lift (mkVariable "field_mass")
              lift (setVariables [(mv, sumAllSR sr (map (planWorldMass sr raws) rs))])
              return [planWorld [] common [] [WMass (IRVar mv)] baked clash]
            else do
              -- Measured in its own scope, its bindings carried by the
              -- factor, so whichever world it joins binds them under that
              -- world's guards ('measureWorlds').
              o <- lift (scoped (measureWorlds sr (planReader raws) rs))
              return [planWorld [] common [] [WFactor o] baked clash]
    mergeable w = null (leafPairs w) && null (pwSubFactors w) && not (any isPt (leafCons w))
    isPt PLeafPt{} = True
    isPt _         = False

-- | Enumerate the possible values of a plan-dependent expression as
-- (value, world) pairs -- the milestone-2 mechanism behind counting folds.
-- The worlds partition the plan-consistent outcomes (every fork below is a
-- partition), so a consumer may guard each value independently and sum.
-- Values are IR expressions, usually constants; arithmetic combines them
-- unfolded (constant folding is left to the optimizer). The result is passed
-- through the milestone-4 value DP ('planGroupValues') so same-value worlds
-- collapse at every level -- without it counting folds are 2^depth.
planEnumValues :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(IRExpr, PlanWorld)])
planEnumValues meta env planBodyExpr = do
  r <- planEnumValuesRaw meta env planBodyExpr
  case r of
    Left why    -> return (Left why)
    Right pairs -> Right <$> planGroupValues pairs

-- | The (value, world) pairs of an arithmetic node's operands, for the caller
-- to cross. Each operand is grouped ('planEnumValues') unless that bakes a
-- leaf a sibling operand also reads: in @(if isA o then 1 else 0) + (if isT o
-- then 1 else 0)@ with @isA o = if isBlue (color o) then isCube (shape o) else
-- False@ and @isT o = isRed (color o)@, @isA@'s False group bakes @color@,
-- which @isT@ constrains. Crossing them used to clash and rerun the whole
-- traversal ungrouped (task count-fold-field-tested-in-two-branches-
-- exponential); now only such an operand is redone with its own grouping off
-- ('planUngroupedLocally'), the grouped attempt discarded without trace
-- ('planAttemptEither'). Operands that do not collide are enumerated exactly
-- as before.
planEnumOperands :: CompilerMetadata -> PlanEnv -> [Expr] -> PlanM (Either String [[(IRExpr, PlanWorld)]])
planEnumOperands meta env args = do
  r <- planAttemptEither $ do
    vssE <- mapM (planEnumValues meta env) args
    return $ case sequence vssE of
      Left why -> Right (Left why)
      Right vss -> case culprits vss of
        [] -> Right (Right vss)
        is -> Left is
  case r of
    Right vssE -> return vssE
    Left is -> fmap sequence . forM (zip [0 :: Int ..] args) $ \(i, a) ->
      (if i `elem` is then planUngroupedLocally else id) (planEnumValues meta env a)
  where
    -- operands with a live world whose baked leaves a sibling's world reads
    culprits vss =
      [ i | (i, ws) <- zip [0 :: Int ..] (map (map snd) vss)
          , any (\(j, ws') -> i /= j && any (\w -> any (collides w) ws') ws) (zip [0 ..] (map (map snd) vss)) ]
    collides w w' = not (null (wBaked w)) && touchesBaked (wBaked w) w'
                    && not (pwUnsat (intersectPlanW w w'))

planEnumValuesRaw :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(IRExpr, PlanWorld)])
planEnumValuesRaw meta env bodyExpr
  | not (subtreeHasOcc occs bodyExpr) =
      if pType (getTypeInfo bodyExpr) == Deterministic
        then do
          ir <- planGenDet meta env bodyExpr
          return (Right [(ir, pw1 [])])
        else return (Left ("a subtree independent of the plan-bound variables draws fresh randomness: " ++ planNodeName bodyExpr))
  | Just refE <- planEvalRef meta env bodyExpr = return $ case refE of
      Left why -> Left why
      Right (PlanRef (Discretes _ (MultiDiscretes vals)) off, cons) ->
        Right [ (IRConst (valueToIR v), pw1 (insertLeafCon (PLeafCon off [(i, constTrueIR)]) cons))
              | (i, v) <- zip [0..] vals ]
      Right _ -> Left "value enumeration is only supported for enum plan leaves"
  | otherwise = do
      shared <- planShareSplit meta env bodyExpr planEnumValuesRaw
      maybe (planEnumValuesNode meta env bodyExpr) return shared
  where
    occs = planEnvOccs env

-- | 'planEnumValuesRaw' at a plan-dependent node that is neither a plan slice
-- nor split on a shared value: dispatch on the node.
planEnumValuesNode :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(IRExpr, PlanWorld)])
planEnumValuesNode meta env bodyExpr = case bodyExpr of
      Expr _ (IfThenElse c t e)
        | not (subtreeHasOcc occs c) && pType (getTypeInfo c) == Deterministic -> do
            g <- planGenDet meta env c
            vsT <- planEnumValues meta env t
            vsE <- planEnumValues meta env e
            return ((\ts es -> [ (v, planAddGuard g w)                    | (v, w) <- ts ]
                            ++ [ (v, planAddGuard (IRUnaryOp OpNot g) w) | (v, w) <- es ]) <$> vsT <*> vsE)
        | subtreeHasOcc occs c -> do
            cb <- planInvertBool meta env c
            case cb of
              Left why -> return (Left why)
              Right (cts0, cfs0) -> do
                -- same dead-branch gating as in planInvert
                let cts = filter (not . pwUnsat) cts0
                let cfs = filter (not . pwUnsat) cfs0
                vsT <- if null cts then return (Right []) else branchValues cts t
                vsE <- if null cfs then return (Right []) else branchValues cfs e
                return $ do
                  ts <- vsT
                  es <- vsE
                  return (livePairs [ (v, intersectPlanW cw w) | cw <- cts, (v, w) <- ts ]
                       ++ livePairs [ (v, intersectPlanW cw w) | cw <- cfs, (v, w) <- es ])
        | otherwise -> return (Left "an if condition independent of the plan-bound variables draws fresh randomness")
      Expr _ (InjF (Named nm) [a, b]) | Just op <- arithOp nm -> do
        vsE <- planEnumOperands meta env [a, b]
        return ((\vs -> livePairs [ (IROp op va vb, intersectPlanW wa wb) | [(va, wa), (vb, wb)] <- sequence vs ]) <$> vsE)
      -- The remaining arithmetic ('planArithOp'), combined the same way: the
      -- cross product of the operands' value worlds.
      Expr _ (InjF (Named nm) args) | Just f <- planArithOp nm (length args) -> do
        vssE <- planEnumOperands meta env args
        return (map (\combo -> (f (map fst combo), foldl1 intersectPlanW (map snd combo)))
                  . filter (not . pwUnsat . foldl1 intersectPlanW . map snd) . sequence <$> vssE)
      Expr _ (Apply lam@(Expr _ (Lambda x b)) a) -> do
        opened <- planOpenBinding meta env lam x b a
        case opened of
          Left why -> return (Left why)
          Right (env', b', cons) -> fmap (map (fmap (addSliceCons cons))) <$> planEnumValues meta env' b'
      Expr _ (Apply {}) -> do
        specsE <- planResolveApply meta env bodyExpr
        case specsE of
          Left why -> return (Left why)
          Right specs -> fmap concat . sequence <$> mapM enumSpec specs
      _ -> return (Left ("unsupported node in plan value enumeration: " ++ planNodeName bodyExpr))
  where
    occs = planEnvOccs env
    arithOp n = lookup n [("plus", OpPlus), ("mult", OpMult)]
    livePairs = filter (not . pwUnsat . snd)
    -- A branch's values under a plan-dependent condition. Grouped, a branch
    -- may bake a leaf the condition's worlds constrain again: in
    -- @if isBlue (color o) then .. else (if isRed (color o) then (if isX0 (xb
    -- o) then 1 else 0) else 0)@ the else branch's value-0 group bakes
    -- @color@, the outer condition's False worlds re-constrain it, and the
    -- clash used to rerun the whole traversal ungrouped (exponential in a
    -- count fold's depth; task count-fold-field-tested-in-two-branches-
    -- exponential). Such a branch is taken with its own top level ungrouped
    -- instead, so the enclosing grouping runs after the condition is in; the
    -- grouped attempt is discarded without trace ('planAttempt'). A branch
    -- that does not clash is enumerated as before.
    branchValues cws b = do
      r <- planAttempt (do
             vs <- planEnumValues meta env b
             return (vs, either (const True) (not . any (clashesWith cws . snd)) vs))
      maybe (planEnumValuesRaw meta env b) return r
    clashesWith cws w =
      any (\cw -> let iw = intersectPlanW cw w
                  in wClash iw && not (wClash cw || wClash w || pwUnsat iw)) cws
    -- one case of the call's argument value split ('planResolveApply'): the
    -- callee's (value, world) pairs, each intersected with the case's world
    enumSpec (spec, splitW)
      | rType (getTypeInfo bodyExpr) == TBool = do
          r <- planSpecializeBool spec
          return ((\(tw, fw) -> live ([ (constTrueIR, inCase w)          | w <- tw ]
                                   ++ [ (IRConst (VBool False), inCase w) | w <- fw ])) <$> r)
      | otherwise = do
          r <- planSpecializeEnum spec
          return ((\pairs -> live [ (v, inCase w) | (v, w) <- pairs ]) <$> r)
      where
        -- an unsplit call is left exactly as before (no intersection, no
        -- filtering), so its IR does not change
        split = not (planWorldTrivial splitW)
        inCase w = if split then intersectPlanW splitW (addSpecCons spec w) else addSpecCons spec w
        live = if split then livePairs else id

-- | A resolved user-function application, ready to specialize: the callee's
-- parameter frame, its body, the memo key, the plan-descent measure, the
-- call-site accessor constraints of its arguments, and the metadata extended
-- with the callee's parameters (so det subtrees inside the body compile).
data PlanSpec = PlanSpec
  { spEnv   :: PlanEnv
  , spBody  :: Expr
  , spKey   :: PlanSpecKey
  , spDepth :: Int
  , spCons  :: [PLeafCon]
  , spMeta  :: CompilerMetadata
  }

-- | Fold the call-site accessor constraints (e.g. the SCons flag implied by
-- @f (rest s)@) into a world produced by the callee.
addSpecCons :: PlanSpec -> PlanWorld -> PlanWorld
addSpecCons spec w = (withLeafCons (foldr insertLeafCon (leafCons w) (spCons spec)) w)
                         { wClash = wClash w || any ((`elem` wBaked w) . plcBase) (spCons spec) }

-- | Resolve a user-function application into a specialization: the callee
-- must be a directly-applied (saturated) top-level function, and each
-- argument either an accessor chain into the plan (bound 'PBPlan') or
-- deterministic given scope (generated at the call site, bound 'PBDet').
--
-- A third kind of argument -- plan-dependent but not an accessor chain, such
-- as a fold's result passed to a helper (@isValid (checksumSum 1 ds)@) -- is
-- handled by a case split on its value (task
-- plan-fold-result-through-helper-crashes): the argument's (value, world)
-- pairs are enumerated ('planEnumValues'), and the callee is specialized once
-- per value combination with the argument bound as that deterministic value.
-- The value worlds partition the argument's outcomes and, given the value, the
-- callee's worlds partition its own, so pairing each specialization with its
-- value world (by intersection) is again a partition. The consumer intersects
-- the returned world into every world of the matching specialization. A call
-- whose arguments need no split returns one specialization under the
-- unconstrained world, so its IR is unchanged.
planResolveApply :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(PlanSpec, PlanWorld)])
planResolveApply meta env planBodyExpr = do
  r0 <- planResolveApplyWith meta env [] planBodyExpr
  case r0 of
    Left why -> return (Left why)
    Right (Right spec) -> return (Right [(spec, pw1 [])])
    Right (Left splits) -> do
      vssE <- mapM enumArg splits
      case sequence vssE of
        Left why -> return (Left why)
        Right vss -> do
          let combos = [ (map fst c, foldl intersectPlanW (pw1 []) (map snd c)) | c <- sequence vss ]
          rs <- mapM specAt (filter (not . pwUnsat . snd) combos)
          return (sequence rs)
  where
    enumArg (i, argE) = do
      vs <- planEnumValues meta env argE
      return $ case vs of
        Left why -> Left ("call argument is neither a plan slice (accessor chain) nor deterministic given scope: "
                          ++ planNodeName argE ++ ", and its values could not be enumerated: " ++ why)
        Right pairs -> Right [ ((i, v), w) | (v, w) <- pairs ]
    specAt (overrides, w) = do
      r <- planResolveApplyWith meta env overrides planBodyExpr
      return $ case r of
        Left why         -> Left why
        Right (Right sp) -> Right (sp, w)
        -- every split argument has an override, so none can be left over
        Right (Left _)   -> Left "internal: a call argument still needs a value split after splitting"

-- | 'planResolveApply' for one fixed assignment of the value-split arguments:
-- @overrides@ binds an argument position to the deterministic value it takes
-- in this case of the split. Returns @Left positions@ (without generating
-- anything) when some argument not in @overrides@ needs a split.
planResolveApplyWith :: CompilerMetadata -> PlanEnv -> [(Int, IRExpr)] -> Expr
                     -> PlanM (Either String (Either [(Int, Expr)] PlanSpec))
planResolveApplyWith meta env overrides planBodyExpr = case collectApply planBodyExpr [] of
  Nothing -> return (Left ("unsupported callee in plan traversal (only directly-applied top-level functions can be specialized): " ++ planNodeName planBodyExpr))
  Just (fname, args) -> case lookup fname (functions (compilingProgram meta)) of
    Nothing -> return (Left ("call to '" ++ fname ++ "': not a top-level function (higher-order callees are not specializable)"))
    Just decl -> do
      let (params, calleeBody) = unwrapCalleeLambdas decl
      let splits = [ (i, a) | (i, a) <- zip [0..] args, isNothing (lookup i overrides), needsSplit a ]
      if length params /= length args
        then return (Left ("call to '" ++ fname ++ "': partial application is not specializable (expected "
                           ++ show (length params) ++ " arguments, got " ++ show (length args) ++ ")"))
        else if not (null splits) then return (Right (Left splits)) else do
          classesE <- mapM classifyArg (zip [0..] args)
          case sequence classesE of
            Left why -> return (Left why)
            Right classes -> do
              frame <- mapM bindParam (zip params classes)
              let planOffs = [ off | ArgPlan (PlanRef _ off) _ <- classes ]
              let detKeys  = [ show ir | ArgDet ir <- classes ]
              let key = (chainName (getTypeInfo calleeBody), planOffs, detKeys)
              let callCons = concat [ cons | ArgPlan _ cons <- classes ]
              let meta' = foldl (\m (pname, pti, _) -> extendMetaForLambda m pti pname) meta params
              return (Right (Right (PlanSpec frame calleeBody key (sum planOffs) callCons meta')))
  where
    collectApply (Expr _ (Apply f a)) acc = collectApply f (a : acc)
    collectApply v@(Expr _ (Var n)) acc
      -- a callee bound in the traversal env is a higher-order parameter, not
      -- a top-level function of the same name
      | isJust (planEnvLookup env (chainName (getTypeInfo v))) = Nothing
      | otherwise = Just (n, acc)
    collectApply _ _ = Nothing
    unwrapCalleeLambdas (Expr ti (Lambda n sub)) =
      let (ps, b) = unwrapCalleeLambdas sub in ((n, ti, chainName ti) : ps, b)
    unwrapCalleeLambdas e = ([], e)
    -- plan-dependent, but not an accessor chain: split on its value
    needsSplit argE = isNothing (planEvalRef meta env argE) && subtreeHasOcc (planEnvOccs env) argE
    classifyArg (i, argE)
      | Just v <- lookup i overrides = return (Right (ArgDet v))
      | Just refE <- planEvalRef meta env argE = return (fmap (uncurry ArgPlan) refE)
      | not (subtreeHasOcc (planEnvOccs env) argE) && pType (getTypeInfo argE) == Deterministic =
          Right . ArgDet <$> planGenDet meta env argE
      | otherwise = return (Left ("call argument is neither a plan slice (accessor chain) nor deterministic given scope: " ++ planNodeName argE))
    -- Bind a non-trivial det argument to a fresh variable once; constants and
    -- variables pass through (also keeps memo keys small and collision-free).
    -- A bound argument that folds to a constant under the already-known
    -- argument values is recorded in 'psDetConsts', so the value grouping can
    -- see through it (the variable is still emitted as before).
    bindParam :: ((String, TypeInfo, ChainName), ArgClass) -> PlanM ([ChainName], PlanBinding)
    bindParam ((pname, _, pcn), cls) = case cls of
      ArgPlan ref _ -> return (occsOf pcn, PBPlan ref)
      ArgDet ir -> do
        v <- case ir of
          IRConst _ -> return ir
          IRVar _   -> return ir
          _ -> do
            nm <- lift (mkVariable "spec_arg")
            lift (setVariables [(nm, ir)])
            consts <- gets psDetConsts
            case foldConstIn consts ir of
              Just c  -> modify (\s -> s { psDetConsts = (nm, c) : psDetConsts s })
              Nothing -> return ()
            return (IRVar nm)
        return (occsOf pcn, PBDet pname v)
    occsOf cn = fromMaybe [] (Map.lookup cn (lambdaVarOccurrences (fcData meta)))

data ArgClass = ArgPlan PlanRef [PLeafCon] | ArgDet IRExpr

-- | Push a specialization onto the stack for the duration of the action,
-- declining first if it would re-enter an active body without strictly
-- descending the plan. Plan offsets are bounded by the plan size, so strictly
-- increasing re-entry terminates; anything else (self-recursion at the same
-- slice, mutual recursion cycles, det-arg-only "recursion") is declined.
planEnterSpec :: PlanSpec -> PlanM (Either String a) -> PlanM (Either String a)
planEnterSpec spec act = do
  st <- get
  let (bodyCN, _, _) = spKey spec
  if any (\(cn, d, _) -> cn == bodyCN && d >= spDepth spec) (psStack st)
    then return (Left ("recursive specialization of the function at " ++ bodyCN
                       ++ " does not strictly descend the plan (non-terminating recursion shape)"))
    else if any (\(cn, _, off) -> cn == bodyCN && psNextOff st > off) (psStack st)
    then return (Left ("recursive specialization of the function at " ++ bodyCN
                       ++ " re-enters it after opening a neural read (its fresh plan offsets do not bound the recursion)"))
    else do
      put st { psStack = (bodyCN, spDepth spec, psNextOff st) : psStack st }
      r <- act
      modify (\s -> s { psStack = drop 1 (psStack s) })
      return r

-- | Specialize a Bool-valued callee at its arguments: canonical
-- (outcome-True, outcome-False) worlds of its body under the argument frame,
-- memoized. NOTE: the returned worlds do not include the call-site accessor
-- constraints -- the caller applies 'addSpecCons'.
planSpecializeBool :: PlanSpec -> PlanM (Either String ([PlanWorld], [PlanWorld]))
planSpecializeBool spec = do
  st <- get
  case Map.lookup (spKey spec) (psBoolMemo st) of
    Just r  -> return (Right r)
    Nothing -> planEnterSpec spec $ do
      r <- planInvertBool (spMeta spec) (spEnv spec) (spBody spec)
      case r of
        Left why -> return (Left why)
        Right tf0 -> do
          -- Collapse each polarity's worlds (milestone-4 DP on the Bool path):
          -- this is what keeps a per-level disjunction -- an extra Object
          -- constructor, a two-leaf test -- from multiplying the recursive
          -- continuation. See 'planGroupBool'.
          tf <- planGroupBool tf0
          -- A traversal that opened a neural read placed it at fresh offsets:
          -- another call must open its own, so it is not memoized.
          opened <- gets ((/= psNextOff st) . psNextOff)
          unless opened $
            modify (\s -> s { psBoolMemo = Map.insert (spKey spec) tf (psBoolMemo s) })
          return (Right tf)

-- | Specialize a value-valued callee at its arguments: (value, world) pairs
-- of its body under the argument frame, memoized. Same call-site-constraint
-- note as 'planSpecializeBool'.
planSpecializeEnum :: PlanSpec -> PlanM (Either String [(IRExpr, PlanWorld)])
planSpecializeEnum spec = do
  st <- get
  case Map.lookup (spKey spec) (psEnumMemo st) of
    Just r  -> return (Right r)
    Nothing -> planEnterSpec spec $ do
      r <- planEnumValues (spMeta spec) (spEnv spec) (spBody spec)
      case r of
        Left why -> return (Left why)
        Right pairs -> do
          opened <- gets ((/= psNextOff st) . psNextOff)
          unless opened $
            modify (\s -> s { psEnumMemo = Map.insert (spKey spec) pairs (psEnumMemo s) })
          return (Right pairs)

-- | Specialize a structure-returning callee directly against the observation:
-- invert its body with the target pushed in, rather than enumerating its result
-- values. Deliberately NOT memoized -- unlike the Bool and enum specializations,
-- the result depends on the target, and a structural recursion descends into a
-- fresh accessor chain (@tl (tl y)@) at every level, so a memo keyed on it could
-- never hit. Termination therefore rests entirely on 'planEnterSpec''s
-- strict-plan-descent guard, exactly as it does for the memoized paths.
planSpecializeTarget :: PlanSpec -> PTarget -> PlanM (Either String [PlanWorld])
planSpecializeTarget spec target = planEnterSpec spec $ do
  r <- planInvert (spMeta spec) (spEnv spec) (spBody spec) target
  case r of
    Left why -> return (Left why)
    -- The worlds are the disjoint ways this call's observation can be met, i.e.
    -- a partition all carrying the same outcome ("matched"). That is exactly
    -- 'planGroupValues'' precondition, with a constant standing in for the
    -- value, so the milestone-4 DP applies unchanged: the level's shared
    -- constructor flags stay live via commonDiscreteCons and only the deeper
    -- levels' residual mass is baked. Without this a c-constructor ADT costs
    -- c^depth worlds -- the same collapse 'planGroupBool' does for predicates.
    Right ws -> Right . map snd <$> planGroupValues [ (constTrueIR, w) | w <- ws ]

-- | Observation target applied to a user-function application (milestone 2):
-- specialize the callee at its arguments and match its outcome against the
-- target. Bool results go through the canonical two-polarity specialization
-- (so both polarities share one memo entry); anything else through value
-- enumeration.
planApplyTarget :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planApplyTarget meta env planBodyExpr target = do
  specsE <- planResolveApply meta env planBodyExpr
  case specsE of
    Left why -> return (Left why)
    Right [(spec, splitW)] | planWorldTrivial splitW -> applySpec spec
    -- a value split of a call argument ('planResolveApply'): each case's
    -- worlds are intersected with that case's argument world
    Right specs -> do
      rs <- mapM (\(spec, splitW) -> fmap (filter (not . pwUnsat) . map (intersectPlanW splitW)) <$> applySpec spec) specs
      return (concat <$> sequence rs)
  where
   applySpec spec = case rType (getTypeInfo planBodyExpr) of
      TBool -> do
        r <- planSpecializeBool spec
        return ((\(tw, fw) -> map (addSpecCons spec) (planBoolWorlds target tw fw)) <$> r)
      rt -> do
        r <- planSpecializeEnum spec
        case r of
          Right pairs ->
            return (Right [ addSpecCons spec (planAddGuard (planDetGuard rt v target) w) | (v, w) <- pairs ])
          -- Value enumeration declines a callee that *builds* a value rather than
          -- choosing among a few (a structure-returning recursion is the case in
          -- point: its result set is the whole depth-unrolled support). Such a
          -- body can still be inverted structurally, pushing the observation onto
          -- the constructor's fields. Tried second, so no program that enumerates
          -- today changes path. When both decline, both reasons are reported: for
          -- a structure-returning body the enum diagnostic alone names the
          -- constructor it could not enumerate, which reads like the whole story
          -- but is only the path that was never going to work.
          Left whyEnum
            | TADT _ <- rt -> do
                s <- planSpecializeTarget spec target
                return (either (\whyStruct -> Left (whyEnum ++ "; and structurally: " ++ whyStruct))
                               (Right . map (addSpecCons spec)) s)
            | otherwise -> return (Left whyEnum)

-- | Entry point of the plan-guided dispatch, tried from the probabilistic
-- Apply arm after point inversion failed and before the set-witness fallback.
-- Right: the compiled result. Left Nothing: not applicable (the argument is
-- not a plan-backed ReadNN, or the application shape is out of scope). Left
-- (Just why): applicable, but the body traversal hit an unsupported node --
-- the diagnostic is appended to the set-witness refusal.
--
-- Entered from an untagged application (a @draw@ / @let@, whose lambda sits
-- lexically in the caller) and from a /tagged invocation of a closed callee/:
-- a top-level function applied straight to the read, @sevens (readDigits s)@ or
-- @match (readAttrs s1) ++ match (readAttrs s2)@ (tasks
-- plan-engine-not-entered-for-inline-neural-read,
-- of-annotation-continuous-leaf-disables-enumeration). The invocation tag only
-- names forward chaining's per-call-site inversion variables, which this
-- AST-level traversal never reads; what the tagged case does need is that the
-- callee's body is meaningful in the caller's scope, and a top-level
-- function's own outermost lambda has no free local variables. An inner lambda
-- of a curried callee, @match c (readAttrs s)@, does: @c@ is the outer lambda's
-- parameter, unbound at the call site. That shape is taken when the call spine
-- supplies every outer parameter with an argument deterministic given the
-- enclosing recovered variables ('bindScope', bound by 'enterBindingScope').
-- A lambda whose body reads a scope this call site never entered stays
-- declined.
planWitnessApply :: CompilerMetadata -> Bool -> RType -> Binding -> IRExpr -> CompilerMonad (Either (Maybe String) PResult)
planWitnessApply meta0 cumulative rt binding sample
  | Just (nnName, plan, symArg, readNode) <- planApplicable meta0 rt binding
  , Right (sliceRef, sliceCons) <- planProjectedSlice meta0 plan 0 readNode (bindArg binding)
  = do
      -- Bind the curried callee's leading parameters (none for a draw or a
      -- one-parameter callee) under fresh names, in the caller's scope.
      entered <- enterBindingScope meta0 binding
      let (meta, scopedBody) = fromMaybe (error "planWitnessApply: bindScope was checked") entered
      -- Re-typed after the fetch, as the point-witness fold does: the fetch
      -- returns original annotations, but a variable fixed by an enclosing
      -- construct (a recovered witness, or an enumeration's loop variable when
      -- this is reached from an over-budget nested application) is
      -- Deterministic here and must dispatch as such.
      let bodyExpr = reinferRecovered meta (recoveredVars meta) scopedBody
      let occs = bindOccs binding
      -- A projected read (@draw a = ob1 (readScene sym)@) binds the slice;
      -- its accessors' constructor flags constrain every world.
      let env = [(occs, PBPlan sliceRef)]
      let target = if cumulative then PTUpTo sample else PTPoint sample
      -- Bind the raw logit vector up front: the milestone-4 value grouping
      -- measures collapsed worlds during the traversal, so it needs the name.
      nnRaw <- mkVariable "nn_raw"
      sym <- toIRGenerate meta symArg
      setVariables [(nnRaw, IRApply (IRVar nnName) sym)]
      -- The milestone-4 value grouping ('planGroupValues') bakes a value
      -- group's leaves into one summed mass. That is sound exactly when no
      -- other part of the body constrains those leaves again, which is what
      -- 'wBaked' / 'wClash' track: grouping is tried first, and only if some
      -- surviving world met a baked leaf again (two readers asking about the
      -- same slice: @(numRed scene, numRed scene)@, a helper reading its
      -- parameter twice, @draw n = numRed scene in (n, n)@) is the traversal
      -- redone without grouping -- the world-per-path enumeration the old
      -- reader-count gate gave every multi-reader body. Readers of DISJOINT slices -- a flat sum over the fields
      -- of a product scene -- never clash, so each keeps its grouping and the
      -- compile stays linear in the field count (task
      -- plan-flat-sum-over-product-exponential). A clash in a world that is
      -- statically unsatisfiable is harmless: it measures 0.
      -- The abandoned grouped attempt leaves no trace: its variable bindings
      -- are dropped ('pass') and the name supply is rewound, so a body that
      -- clashes emits exactly what the ungrouped traversal alone would.
      -- The traversal may open further neural reads ('planOpenBinding'); the
      -- final state says where each one's logits live.
      -- Field factoring ('planFieldProduct', 'psFactor') bakes leaves the same
      -- way, so it is tried first and dropped on a clash -- before grouping
      -- is: the second attempt is exactly the traversal that ran before field
      -- factoring existed. An attempt that never factored is not repeated.
      let runPlan merge factor = do
            (ws, st) <- runStateT (planInvert meta env bodyExpr target) (emptyPlanState (semiringOf meta) nnRaw (getSize plan) merge factor)
            return ((filter (not . pwUnsat) . map (addSliceCons sliceCons) <$> ws, psRaws st), psFactored st)
          attempt merge factor = do
            supply <- get
            o <- scoped (runPlan merge factor)
            let (r, factored) = openValue o
                c = either (const False) (any wClash) (fst r)
            unless c (void (inline o))
            return (r, c, factored, supply)
      (factoredR, clashed1, didFactor, supply0) <- attempt True True
      (groupedR, clashed2, supply1) <-
        if clashed1 && didFactor
          then put supply0 >> attempt True False >>= \(r, c, _, sp) -> return (r, c, sp)
          else return (factoredR, clashed1, supply0)
      (worldsE, raws) <- if clashed2 then put supply1 >> (fst <$> runPlan False False) else return groupedR
      case worldsE of
        Left why -> return (Left (Just why))
        Right worlds -> do
          case mapMaybe pwOverCoupled worlds of
           (why:_) -> return (Left (Just why))
           [] -> do
            measured <- measureWorlds (semiringOf meta) (planReader raws) worlds
            -- Full-ANY marginal short-circuit, mirroring setWitnessApply.
            if cumulative
              then return (Right measured)
              else return (Right (zipResult (\anyVal e -> IRIf (IRUnaryOp OpIsAny sample) anyVal e)
                                    (mass (srOne (semiringOf meta))) measured))
  | otherwise = return (Left Nothing)

-- | The neural read an expression is, when the plan engine can traverse it
-- ('SPLL.AutoNeural.planReadOf' in this compile's program).
planReadOf :: CompilerMetadata -> Expr -> Maybe (String, PartitionPlan, Expr)
planReadOf meta = AutoNeural.planReadOf (compilingProgram meta)

-- | A neural read seen through field accessors, @ob1 (readScene sym)@
-- ('SPLL.AutoNeural.planProjectedReadOf'): also answers the read node.
planProjectedReadOf :: CompilerMetadata -> Expr -> Maybe (String, PartitionPlan, Expr, Expr)
planProjectedReadOf meta = AutoNeural.planProjectedReadOf (compilingProgram meta)

-- | The slice a projected read binds ('planProjectedReadOf'), with the
-- constructor-flag constraints its accessors imply: the accessor chain
-- evaluated with the read node itself bound to the whole plan at @off@.
planProjectedSlice :: CompilerMetadata -> PartitionPlan -> Int -> Expr -> Expr -> Either String (PlanRef, [PLeafCon])
planProjectedSlice meta plan off readNode arg =
  fromMaybe (Left ("not an accessor chain over a neural read: " ++ planNodeName arg))
            (planEvalRef meta [([chainName (getTypeInfo readNode)], PBPlan (PlanRef plan off))] arg)

-- | Fold a projected binding's accessor constraints into a world (the
-- call-site analogue is 'addSpecCons'); a constraint on a leaf the world
-- already baked is a clash.
addSliceCons :: [PLeafCon] -> PlanWorld -> PlanWorld
addSliceCons cons w = (withLeafCons (foldr insertLeafCon (leafCons w) cons) w)
                          { wClash = wClash w || any ((`elem` wBaked w) . plcBase) cons }

-- | The plan-guided engine's applicability to a binding: its argument is a
-- plan read ('planReadOf', the predicate the modality engine reads too), its
-- body is meaningful at this call site ('bindScope'), and it is not
-- function-valued.
planApplicable :: CompilerMetadata -> RType -> Binding -> Maybe (String, PartitionPlan, Expr, Expr)
planApplicable meta rt binding
  | isJust (bindScope binding), not (isTArrowType rt) = planProjectedReadOf meta (bindArg binding)
  | otherwise = Nothing
