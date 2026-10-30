-- | The worlds algebra and set-witness inversion: guarded witness sets,
-- their intersection and measure ('measureWorld'), and inverting a body into
-- worlds ('invertToWorlds').
module SPLL.IRCompiler.Worlds (
  WBound(..),
  WFactor(..),
  boundGuards,
  maxWBound,
  minWBound,
  subtreeHasOcc,
  setWitnessApply,
  planFactorExternals
) where

import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Typing.PType
import Data.Maybe
import Data.List (nub)
import Data.Functor ((<&>))
import SPLL.Typing.ForwardChaining
import SPLL.Semiring
import Control.Monad (foldM, forM)
import qualified Data.Map.Strict as Map
import Data.Char (isUpper)
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Gaussian

-- ===== Set-valued witnesses (design set-valued-witnesses) =====
--
-- When the bound variable of a probabilistic let cannot be point-recovered from
-- the observation ('toInvExprMaybe' = Nothing), the observation may still carve
-- out a measurable SET of its values: a comparison observed True confines it to
-- an interval, an if-then-else case-splits on its condition, and multiple
-- occurrences intersect their constraints. A "world" is a guarded constraint
-- set; p(sample) = sum over worlds of (product of guards) * mu_v(set), where a
-- point set is measured by v's density (with change-of-variables factor) and an
-- interval by a CDF difference (mass needs no change-of-variables correction).

data WBound = WNegInf | WPosInf | WFinite IRExpr

-- | A constraint set over the bound variable's (scalar) domain.
data WSet = WPoint IRExpr IRExpr     -- witness value, |d inverse / d observation|
          | WInterval WBound WBound
          | WFull
          | WEmpty
          -- | Runtime choice of constraint set: the Bool-valued IR condition
          -- picks the first set, else the second. Needed because whether a
          -- constraint is a point or an interval can depend on the query
          -- SAMPLE rather than on the program -- a marginal wildcard sitting
          -- in a constructor slot (@p(Right ANY)@) leaves the tag pinned but
          -- the payload unconstrained, which is an interval where a concrete
          -- payload would have been a point. Unlike the ANY that N6's
          -- 'irRuntimeContainsAny' handles (injected at compile time by a
          -- lossy inverse, hence syntactically visible in the witness
          -- template), this one has no static trace at all, so it cannot be
          -- resolved into a single 'WSet' at compile time.
          | WChoice IRExpr WSet WSet
          -- | A set with one point removed: every value of the first set
          -- other than the given one. What the False polarity of an @==@ (or
          -- of an ADT constructor test) says about its operand. It used to
          -- travel as a 'WPoint' holding the 'VAnyExcept' sentinel -- a point
          -- that was really a set -- and every consumer that treats a point's
          -- value as a value (a second comparison's membership guards, a
          -- point-point intersection's 'OpEq') applied raw arithmetic to the
          -- sentinel and crashed (task
          -- sampling-matches-pdf-continuous-equality-density). The excepted
          -- point may itself carry nested 'VAny' fields (a constructor test's
          -- @Foo ANY@): it then removes that whole constructor's values.
          --
          -- Measured as the set's measure minus the point's in the semiring's
          -- sense ('mixSubP'): a continuous point is a density and a mass
          -- minus a density is the mass, so removing one point from a
          -- continuous set leaves its measure unchanged; a discrete point's
          -- mass is subtracted. See 'measureSet'.
          | WExcept WSet IRExpr

-- | Mirrors an inverse-witness expression's structure to build a runtime Bool
-- expression that evaluates to True iff the value that expression produces
-- (under the SAME runtime branching) contains a placeholder VAny introduced by
-- a lossy inverse reconstruction -- e.g. isLeft's inverse (always: @if tag then
-- Left VAny else Right VAny@), the Nothing arm of fromLeft's total inverse
-- (@if isRight m then Left (fromRight m) else Right VAny@, only ANY-tainted on
-- one branch), or a tuple projection's inverse (fst's: @IRConstruct TgTuple [b, VAny]@, tainted
-- only in the second slot). A single static "is this any-tainted" flag can't
-- capture either of the latter two -- one depends on which branch is taken,
-- the other differs per field of a composite value -- so this produces a
-- same-shaped runtime expression instead of a compile-time Bool, queried fresh
-- per (sub)value by 'mergeWitnessValue' rather than computed once for a whole
-- witness. Recognises the specific shapes this module's inverse FDecls build
-- (IRConst/IRIf/IRConstruct TgLeft or TgRight/IRLetIn); anything else falls back to a
-- shallow runtime OpIsAny check on the whole subexpression (safe: OpIsAny only
-- misses ANY nested below the top level, under-approximating "any-tainted",
-- which only affects which side 'mergeWitnessValue' prefers -- its OpEq guard
-- independently catches a genuine structural mismatch either way).
irRuntimeContainsAny :: IRExpr -> IRExpr
irRuntimeContainsAny (IRConst v) = if valueContainsAny v then constTrueIR else IRConst (VBool False)
irRuntimeContainsAny (IRIf c t e) = IRIf c (irRuntimeContainsAny t) (irRuntimeContainsAny e)
irRuntimeContainsAny (IRConstruct TgLeft [a]) = irRuntimeContainsAny a
irRuntimeContainsAny (IRConstruct TgRight [a]) = irRuntimeContainsAny a
irRuntimeContainsAny (IRLetIn n v b) = IRLetIn n v (irRuntimeContainsAny b)
irRuntimeContainsAny e = IRUnaryOp OpIsAny e

-- | Guards are Bool-valued IR over the sample and deterministic scope; a world
-- contributes only when all guards hold. The factors are independent
-- probability results multiplied into the world's measure ('prodP': dims
-- and branch counts add) -- each one the residue of a subtree that
-- 'transportDirect' inverted through a field constructor, compiled with the
-- bound variable fixed at its witness (see 'residueFactor'), or an x-free
-- subtree drawing fresh randomness (see 'worldFactorFree'). They are
-- evaluated under the world's guards, never before them.
data WWorld = WWorld [IRExpr] WSet [WFactor]

-- | A world factor: a result, plus bindings its fields read. A residue
-- factor's block and an x-free factor's are each a whole sub-inference (the
-- latter often itself a set-witness world sum), so each is bound ONCE and its
-- fields project that variable ('unpackResult'): folding it into each of the
-- four fields copied it four times per nesting level, which made a nested
-- fresh draw's unoptimized IR grow 4^depth (23MB for a two-level fuzz program)
-- and its optimized compile 6x slower. 'measureWorld' and
-- 'measurePlanWorlds' emit the bindings under the world's guards.
--
-- A factor carried by several worlds ('intersectW', 'intersectPlanW',
-- 'planAddFactor') is still emitted once per world: binding it once above the
-- worlds would evaluate it outside their guards, and is part of the
-- world-grouping design in task budget-zero-exponential-in-nested-enum-ifs.
--
-- 'WMass' is the other kind of factor: a pre-measured dim-0 mass, already in
-- the ambient semiring, multiplied into the world's constraint mass with no
-- bookkeeping of its own (no dimension, no branch count, never impossible by
-- itself). It is what the plan engine's value grouping collapses a group of
-- same-value worlds into (see 'planGroupValues'); the set-witness engine
-- builds none.
data WFactor = WFactor (Open PResult)
             | WMass IRExpr

addGuard :: IRExpr -> WWorld -> WWorld
addGuard g (WWorld gs s fs) = WWorld (g:gs) s fs

intersectW :: WWorld -> WWorld -> WWorld
intersectW (WWorld g1 s1 f1) (WWorld g2 s2 f2) =
  let (g3, s3) = intersectSet s1 s2 in WWorld (g1 ++ g2 ++ g3) s3 (f1 ++ f2)

-- Two constraints on the SAME draw. Point-point must agree: the compatibility
-- guard is a single 'OpEq' on the whole, undecomposed values -- deliberately
-- NOT computed field-by-field. 'OpEq' is already deep, VAny-wildcard-aware in
-- the interpreter, but only where VAny is *nested inside* a container
-- comparison (IRInterpreter.hs's cmp: 'VTuple'/'VEither' cases treat a nested
-- VAny as a wildcard); a *bare* top-level VAny compares False against
-- anything (the `(VAny, _) -> False` / `(_, VAny) -> False` fallback). Calling
-- OpEq on a decomposed leaf (e.g. comparing a recovered field directly against
-- a bare `IRConst VAny` placeholder) would hit that fallback and wrongly
-- reject an otherwise-valid world -- so the guard stays a single check at this
-- level, and only the VALUE selection ('mergeWitnessValue') recurses.
intersectSet :: WSet -> WSet -> ([IRExpr], WSet)
intersectSet WFull s = ([], s)
intersectSet s WFull = ([], s)
intersectSet WEmpty _ = ([], WEmpty)
intersectSet _ WEmpty = ([], WEmpty)
intersectSet (WChoice c a b) s = distributeChoice c (intersectSet a s) (intersectSet b s)
intersectSet s (WChoice c a b) = distributeChoice c (intersectSet s a) (intersectSet s b)
-- (s minus p) meet t is (s meet t) minus p: intersect first, then remove the
-- point from whatever came out ('exceptPoint').
intersectSet (WExcept s p) t = let (g1, st) = intersectSet s t
                                   (g2, r)  = exceptPoint p st
                               in (g1 ++ g2, r)
intersectSet t (WExcept s p) = let (g1, ts) = intersectSet t s
                                   (g2, r)  = exceptPoint p ts
                               in (g1 ++ g2, r)
-- A point that is the bare marginal wildcard at runtime (the witness recovered
-- from an ANY slot: @fromRight@ of @Right ANY@) constrains nothing, so the
-- other point alone survives ('mergeWitnessValue' already picks it); the bare
-- 'OpEq' answered False there and dropped the world, so
-- @draw x = .. in if x == 1 then right x else left ()@ at @Right ANY@ was
-- impossible (task materialization-budget-zero-observe-any-wrong).
intersectSet (WPoint p1 c1) (WPoint p2 c2) =
  ([tolerateAny p1 (tolerateAny p2 (IROp OpEq p1 p2))], WPoint (mergeWitnessValue p1 p2) (IROp OpMult c1 c2))
intersectSet (WPoint p c) (WInterval lo hi) = pointInInterval p c lo hi
intersectSet (WInterval lo hi) (WPoint p c) = pointInInterval p c lo hi
intersectSet (WInterval lo1 hi1) (WInterval lo2 hi2) =
  ([], WInterval (maxWBound lo1 lo2) (minWBound hi1 hi2))

-- | Remove the point @p@ from a set, simplifying where the result is again a
-- plain set. Removing a point from a point is a disequality guard on the
-- remaining one -- the same undecomposed 'OpEq' 'intersectSet' uses for two
-- points, and wildcard-aware for the same reason: a nested 'VAny' in @p@ (a
-- constructor test's @Foo ANY@) matches every value of that constructor, which
-- is exactly the set being removed. A marginal-wildcard remaining point
-- constrains nothing, so there the result is the point's full set minus @p@,
-- decided at runtime as in 'pointInInterval'. Everything else keeps the
-- 'WExcept' and leaves the subtraction to 'measureSet'.
exceptPoint :: IRExpr -> WSet -> ([IRExpr], WSet)
exceptPoint _ WEmpty = ([], WEmpty)
-- A remaining point that is itself only partly known -- a constructor test's
-- @C ANY@ -- is a set, not a point, and removing a point from it leaves the
-- rest of it: @C ANY@ minus @C 7@ is every @C@ but @C 7@. The disequality
-- guard read the two as equal and dropped the whole world (@if isC x then (if
-- d x == 7 then 1 else 0) else 0@ lost P(C 1) from p(0); found with
-- fuzz-admission-oracle-bugs item 9). That shape keeps the subtraction, of the
-- two points' meet, for 'measureSet' (whose membership guard checks they
-- meet at all).
exceptPoint p (WPoint q c)
  | staticallyPartial q = ([], WExcept (WPoint q c) (mergeWitnessValue q p))
exceptPoint p (WPoint q c) =
  ( [tolerateAny q (notIR (IROp OpEq q p))]
  , WChoice (IRUnaryOp OpIsAny q) (WExcept (WPoint q c) p) (WPoint q c) )
exceptPoint p (WChoice c a b) = distributeChoice c (exceptPoint p a) (exceptPoint p b)
exceptPoint p s = ([], WExcept s p)

-- | A point constraint meeting an interval one. The point normally wins (it is
-- the strictly smaller set), guarded by membership -- but when the point is the
-- marginal wildcard at runtime it constrains nothing, and the intersection is
-- the interval alone: @p(Right ANY)@ on a truncated Normal must answer the
-- CDF mass of the truncation interval (dim 0), not a density at an unknown
-- point. Which of the two it is cannot be decided at compile time, hence the
-- 'WChoice'; the membership guards are made wildcard-tolerant to match, so the
-- comparison that would crash on a 'VAny' operand is never reached.
pointInInterval :: IRExpr -> IRExpr -> WBound -> WBound -> ([IRExpr], WSet)
pointInInterval p c lo hi =
  ( [tolerateAny p g | g <- boundGuards p lo hi]
  , WChoice (IRUnaryOp OpIsAny p) (WInterval lo hi) (WPoint p c) )

-- | @g@, but automatically satisfied when @p@ is the marginal wildcard.
-- Spelled as a nested 'IRIf', never 'orIR': both operands of an IR boolean op
-- are evaluated, and @g@ is exactly the comparison that errors on a 'VAny'
-- operand (the same rule 'equalityGuard' and 'impossibleWhen' follow).
tolerateAny :: IRExpr -> IRExpr -> IRExpr
tolerateAny p g = IRIf (IRUnaryOp OpIsAny p) constTrueIR g

-- | Lifts an intersection performed separately on each side of a 'WChoice'
-- back into one. The two sides' guard lists are conjoined branch-locally --
-- again as nested 'IRIf', so a guard still protects the ones after it, the
-- property 'guardP' relies on at the world level.
distributeChoice :: IRExpr -> ([IRExpr], WSet) -> ([IRExpr], WSet) -> ([IRExpr], WSet)
distributeChoice c (ga, sa) (gb, sb) = ([IRIf c (conjIR ga) (conjIR gb)], WChoice c sa sb)
  where conjIR = foldr (\g acc -> IRIf g acc constFalseIR) constTrueIR

-- | Picks, field-by-field, whichever side of two witnesses for the same
-- variable is not ANY-tainted (checked fresh via 'irRuntimeContainsAny' at
-- each position, since informativeness can differ per field of a composite
-- witness -- e.g. one side recovers only a tuple's first field via fst's
-- inverse, the other only its second via snd's). Recurses through
-- @IRConstruct TgTuple@ so such complementary partial witnesses combine into
-- a single fully concrete value instead of one silently overriding the other
-- -- mirrors the equivalent merge already used on the ordinary, non-set-witness
-- point-inversion path, ForwardChaining.hs's 'mergeExpr2' @IRConstruct
-- TgTuple@/VAny cases.
-- Compatibility is 'intersectSet's job (a single guard on the whole value,
-- not per field -- see there for why); this function never rejects, only
-- chooses.
mergeWitnessValue :: IRExpr -> IRExpr -> IRExpr
mergeWitnessValue p1 p2 = mergeWitnessFields (exposeConstructIR p1) (exposeConstructIR p2)

-- | 'mergeWitnessValue' on witnesses whose tuples are syntactic. A witness
-- read through a structural wrapper (@fst (e, 0.0)@) is a projection of a
-- let-bound tuple instead, which the runtime pick below took whole over the
-- sibling's complementary field (task
-- fst-of-pair-wrapper-loses-structured-draw-constraint), hence
-- 'exposeConstructIR' first.
mergeWitnessFields :: IRExpr -> IRExpr -> IRExpr
mergeWitnessFields (IRConstruct TgTuple [a1, b1]) (IRConstruct TgTuple [a2, b2]) =
  IRConstruct TgTuple [mergeWitnessFields a1 a2, mergeWitnessFields b1 b2]
-- A user-ADT constructor, field by field, as a tuple: @isDCons ds@ witnesses
-- @DCons ANY ANY@, @dig ds * 3 == 21@ witnesses @DCons 7 ANY@, and taking the
-- first whole (it is no wildcard at its root) answered P(DCons) with the digit
-- never constrained (fuzz-admission-oracle-bugs item 9). A witness built
-- under let-bindings (an inverse's own temporaries) is merged under them;
-- chain-named binders are unique, so nothing is captured.
mergeWitnessFields (IRLetIn n v b) p2 = IRLetIn n v (mergeWitnessFields b p2)
mergeWitnessFields p1 (IRLetIn n v b) = IRLetIn n v (mergeWitnessFields p1 b)
mergeWitnessFields p1 p2
  | Just (c1, fs1) <- ctorSpineIR p1, Just (c2, fs2) <- ctorSpineIR p2
  , c1 == c2, length fs1 == length fs2 =
  foldl IRApply (IRVar c1) (zipWith mergeWitnessFields fs1 fs2)
-- A bare wildcard on the second side is the least informative witness of all,
-- so the first wins even when it is only partly known: @isRight m@ witnesses
-- @Right ANY@, @right m@ at @Right ANY@ witnesses a bare @ANY@, and taking the
-- latter measured the draw at a sentinel (a type error in its @isLeft@).
mergeWitnessFields p1 p2 = IRIf (IRUnaryOp OpIsAny p2) p1 (IRIf (irRuntimeContainsAny p1) p2 p1)

-- | A witness built with a wildcard inside a constructor (not at its root):
-- statically a set of values rather than one.
staticallyPartial :: IRExpr -> Bool
staticallyPartial (IRLetIn _ _ b) = staticallyPartial b
staticallyPartial (IRConstruct TgTuple fs) = any anyOrPartial fs
staticallyPartial e | Just (_, fs) <- ctorSpineIR e = any anyOrPartial fs
staticallyPartial _ = False

anyOrPartial :: IRExpr -> Bool
anyOrPartial (IRConst VAny) = True
anyOrPartial e = staticallyPartial e

-- | A saturated user-ADT constructor application in the IR: the constructor's
-- (capitalised) name applied to its fields.
ctorSpineIR :: IRExpr -> Maybe (String, [IRExpr])
ctorSpineIR e = go e []
  where go (IRApply f x) acc = go f (x : acc)
        go (IRVar c@(h:_)) acc@(_:_) | isUpper h = Just (c, acc)
        go _ _ = Nothing

-- Membership guards of a point against interval bounds. Every interval is
-- closed, @[lo, hi]@: for a continuous variable strictness has measure zero,
-- and the closed form gives boundary queries like p(0) for |Normal| the
-- density instead of an arbitrary 0; a strict comparison on an Int is closed
-- by moving its bound one step inward ('comparisonWorlds'), and 'measureSet'
-- counts the atom at a closed lower end.
boundGuards :: IRExpr -> WBound -> WBound -> [IRExpr]
boundGuards p lo hi =
     [IRUnaryOp OpNot (IROp OpLessThan p e) | WFinite e <- [lo]]
  ++ [IRUnaryOp OpNot (IROp OpGreaterThan p e) | WFinite e <- [hi]]
  ++ [IRConst (VBool False) | WPosInf <- [lo]]
  ++ [IRConst (VBool False) | WNegInf <- [hi]]

maxWBound :: WBound -> WBound -> WBound
maxWBound WNegInf b = b
maxWBound b WNegInf = b
maxWBound WPosInf _ = WPosInf
maxWBound _ WPosInf = WPosInf
maxWBound (WFinite a) (WFinite b) = WFinite (IRIf (IROp OpGreaterThan a b) a b)

minWBound :: WBound -> WBound -> WBound
minWBound WPosInf b = b
minWBound b WPosInf = b
minWBound WNegInf _ = WNegInf
minWBound _ WNegInf = WNegInf
minWBound (WFinite a) (WFinite b) = WFinite (IRIf (IROp OpLessThan a b) a b)

-- | Bool-valued IR: is @val@ (a deterministic value) inside the target set?
-- The point case is the wildcard-aware 'equalityGuard', not the static one:
-- the point of a target set is a projection of the query sample, so a
-- marginal wildcard can sit in it at any depth (@p((ANY, 0.3))@ against an
-- x-free arm @(0.0, 0.0)@), where a static float comparison errors and a
-- static discrete one silently answers False; a wildcard slot constrains
-- nothing, so the membership holds there, as it does for the interval case
-- through 'tolerateAny'.
memberGuard :: RType -> IRExpr -> WSet -> IRExpr
memberGuard rt val (WPoint p _) = equalityGuard rt p val
memberGuard _ val (WInterval lo hi) = case boundGuards val lo hi of
  [] -> constTrueIR
  gs -> foldr1 (IROp OpAnd) gs
memberGuard _ _ WFull  = constTrueIR
memberGuard _ _ WEmpty = IRConst (VBool False)
memberGuard rt val (WChoice c a b) = IRIf c (memberGuard rt val a) (memberGuard rt val b)
-- Nested 'IRIf', not 'OpAnd', so the disequality is only reached once
-- membership of the underlying set has held; a wildcard @val@ constrains
-- nothing and is a member, as in the other cases.
memberGuard rt val (WExcept s p) =
  IRIf (memberGuard rt val s)
       (tolerateAny val (notIR (equalityGuard rt p val)))
       (IRConst (VBool False))

subtreeCNs :: Expr -> [ChainName]
subtreeCNs e = chainName (getTypeInfo e) : concatMap subtreeCNs (getSubExprs e)

subtreeHasOcc :: [ChainName] -> Expr -> Bool
subtreeHasOcc occs e = let cns = subtreeCNs e in any (`elem` cns) occs

-- | Entry point of the fallback, called from the probabilistic Apply arm after
-- 'toInvExprMaybe' failed. Builds the constraint worlds for the observation and
-- measures them against the bound distribution @v@.
setWitnessApply :: CompilerMetadata -> Bool -> RType -> Binding -> Maybe String -> IRExpr -> CompilerMonad PResult
setWitnessApply meta0 cumulative rt binding planDiag sample = do
  let sr = semiringOf meta0
  let Binding{bindHead = l, bindArg = v, bindLambda = lResolvedCN} = binding
  let userVar = case l of Expr _ (Lambda n _) -> n; _ -> bindVar binding
  let refuseSW why = refuse lResolvedCN $ init $ unlines $
        [ "set-valued witness construction failed for the binding of '" ++ userVar ++ "' (lambda at " ++ lResolvedCN ++ "):"
        , why
        , "No occurrence of the bound variable is point-invertible either (forward"
        , "chaining found no inversion path). See design set-valued-witnesses." ]
        ++ maybe [] (\d ->
             [ "Plan-guided lazy enumeration was applicable but could not compile the body:"
             , d
             , "(design plan-guided-lazy-enumeration)" ]) planDiag
  case rt of
    TArrow _ _ -> refuseSW "the body returns a function."
    _ -> return ()
  -- The worlds are built over the resolved lambda's own body, so it has to
  -- mean in this scope what it means in the callee ('bindScope').
  entered <- enterBindingScope meta0 binding
  (meta, bodyExpr) <- case entered of
    Just e -> return e
    Nothing -> refuseSW ("the lambda's body reads a variable this call site does not bind"
      ++ " (a leading parameter of the callee whose argument is random, or a variable of"
      ++ " a scope the lambda closes over).")
  let occs = bindOccs binding
  let target = if cumulative
        then WInterval WNegInf (WFinite sample)
        else WPoint sample const1
  -- Attempted in its own scope: a failed inversion's bindings are
  -- dropped, and a successful one's are re-emitted unchanged, in order.
  -- A sub-compile inside the inversion that refuses is a refusal of the
  -- inversion as a whole.
  -- An interval is a set of SCALARS: a cumulative query of a structured value
  -- (a list, an Either, an ADT) has no interval to transport, and the
  -- membership guards compared structured values with @<@ -- @head (draw v0 =
  -- Normal in if v0 < -0.575 then [-2] else [4]) < -5@ reached here through
  -- @head@'s inverse as the interval @(-inf, -5 : ANY]@ on the list, and the
  -- constant folder crashed on @[-2] > -5 : ANY@ (task
  -- optimizer-folds-comparison-on-lists). Such a query takes the
  -- no-inverse path below: the cumulative refusal.
  let intervalTarget = case rt of
        TFloat -> True
        TInt   -> True
        TBool  -> True
        _      -> False
  worldsM <- if cumulative && not intervalTarget then return Nothing else
    scoped (invertToWorlds meta occs bodyExpr target) >>= inlineIfJust
  case worldsM of
    -- A cumulative query the engine cannot invert (e.g. the multivariate CDF of
    -- a correlated tuple) is refused like any other shape: only the integrate
    -- variant goes, so the probability variant of the same program is
    -- unaffected (it used to be a runtime IRError for exactly that reason,
    -- before a static refusal was an absent variant rather than a crash).
    Nothing | cumulative -> refuseSW ("the observation has no set-valued inverse in cumulative mode"
          ++ " (e.g. the multivariate CDF of a correlated tuple).")
    Nothing -> refuseSW ("the observation cannot be propagated onto the bound variable: the body"
      ++ " contains a node that is neither point-invertible, a comparison against a"
      ++ " deterministic bound, an if-then-else case split, a tuple of such parts, nor"
      ++ " deterministic given scope (e.g. it draws fresh randomness).")
    Just worlds -> do
      measured <- mapM (measureWorld meta v) worlds
      -- The worlds partition the observation, so they mix; here (unlike the
      -- IfThenElse mixture) each world really was traversed, so counts sum.
      summed <- case measured of
        -- no worlds can only mean an impossible observation
        []     -> return (impossibleP sr)
        (m:ms) -> foldM (\a b -> mixP sr (IROp OpPlus (rBranches a) (rBranches b)) a b) m ms
      -- Full-ANY marginal short-circuit: guards and transported bounds are not
      -- ANY-aware, but the marginal of the whole observation is simply 1.
      if cumulative
        then return summed
        else return (zipResult (\anyVal e -> IRIf (IRUnaryOp OpIsAny sample) anyVal e)
                       (mass (srOne sr)) summed)

-- | Measure one world against the bound distribution. The measure is compiled
-- in its own scope and kept under the world's guards, so bindings whose
-- evaluation is only valid when the guards hold are not hoisted past them.
measureWorld :: CompilerMetadata -> Expr -> WWorld -> CompilerMonad PResult
measureWorld meta v (WWorld guards set factors) = do
  let sr = semiringOf meta
  setO <- scoped (measureSet meta v set)
  -- The set's measure and the residue factors are independent: the product
  -- rule, exactly as the point-witness path's body-factor fold applies it.
  let factorOs = [o | WFactor o <- factors]
  let world = foldl (prodP sr) <$> setO <*> sequenceA factorOs
  -- A world whose guards fail is not part of the observation at all.
  if all openIsEmpty factorOs
    -- The set measure's own bindings, under the guards: inline in the one
    -- field that reads them, else bound once ('guardedResult'). Re-wrapped
    -- around every field, they were copied up to four times per world.
    then guardedResult sr "world" guards world
    -- Factor bindings are read by several fields, so the world's result is
    -- packed and bound once, under the guards ('closeResult'), rather than
    -- copying the bindings into each field. The set measure's own bindings
    -- join them in that one block instead of being wrapped per field.
    else closeResult sr "world" guards world

measureSet :: CompilerMetadata -> Expr -> WSet -> CompilerMonad PResult
measureSet meta v (WPoint p cov) = do
  -- change-of-variables correction only for continuous results, mirroring the
  -- point-witness path
  scaleCoV (semiringOf meta) False cov <$> toIRInference meta False v p
-- The interval is closed, @[lo, hi]@, as 'boundGuards' tests membership. For a
-- continuous variable that is @CDF(hi) - CDF(lo)@, below. An Int variable has
-- an atom at @lo@ that belongs to the set: 'measureIntInterval'.
measureSet meta v (WInterval lo hi)
  | rType (getTypeInfo v) == TInt = measureIntInterval meta v lo hi
measureSet meta v (WInterval lo hi) = do
  let sr = semiringOf meta
  (cdfHi, bcHi) <- cdfAtBound meta v hi
  (cdfLo, bcLo) <- cdfAtBound meta v lo
  -- The CDF difference, let-bound because both the measure and its
  -- impossibility flag read it, and it is two full inference compiles. An
  -- empty runtime intersection shows up as a non-positive linear difference.
  -- In log space the difference ('measureDiffSR') is only defined for a
  -- non-empty interval -- the log of a negative number is not a probability,
  -- and Python's math.log raises on it -- so there the emptiness test reads
  -- the two (let-bound) CDF values instead, and the difference is taken only
  -- under it.
  diffVar <- mkVariable "ivl_mass"
  nonEmpty <- if srLogSpace sr
    then do
      hiVar <- mkVariable "cdf_hi"
      loVar <- mkVariable "cdf_lo"
      let nonEmpty = IROp OpGreaterThan (IRVar hiVar) (IRVar loVar)
      setVariables [ (hiVar, cdfHi), (loVar, cdfLo)
                   , (diffVar, IRIf nonEmpty (measureDiffSR sr (IRVar hiVar) (IRVar loVar)) (srZero sr)) ]
      return nonEmpty
    else do
      setVariables [(diffVar, measureDiffSR sr cdfHi cdfLo)]
      return (IROp OpGreaterThan (IRVar diffVar) (srZero sr))
  let diff = IRVar diffVar
  let clamped = IRIf nonEmpty diff (srZero sr)
  let bc = case (hi, lo) of
        (WFinite _, _) -> bcHi
        (_, WFinite _) -> bcLo
        _              -> const1
  -- An interval that came out empty at runtime carries no possibility.
  return (impossibleWhen (notIR nonEmpty)
            (mkPResult (sealP clamped) dim0 bc constFalseIR))
measureSet meta _ WFull  = return (mass (srOne (semiringOf meta)))
measureSet meta _ WEmpty = return (impossibleP (semiringOf meta))
-- The set's measure minus the removed point's, where the point lies in the
-- set at all (otherwise nothing was removed: the subtrahend is impossible and
-- 'mixWith' drops it). The subtraction is 'mixSubP''s, so dimensions decide
-- it: a continuous set is a mass and the point a density, and the mass wins
-- untouched -- a single point of a continuous variable has measure zero; a
-- discrete point is a mass at the same dim and is subtracted. This is the one
-- rule the InjF 'hasAnyExcept' combinator and the 'IfThenElse' complement also
-- follow, so the letfree and let-bound spellings of a program agree. The
-- point is measured with no change-of-variables factor: when it matters (a
-- density), 'mixWith' discards it anyway. Both operands are compiled in their
-- own scope, the point's under its membership guard, which is what
-- keeps a density at a point outside an interval from being evaluated.
--
-- Both operands of the subtraction are compiled 'unpruned' (see there: a
-- pruned subtrahend inflates the difference). The complement of a point in the
-- whole domain -- the only shape the 'VAnyExcept' sentinel used to express --
-- is measured exactly as that sentinel was ('toIRInference''s
-- marginal-minus-point split). A proper subset minus a point subtracts the
-- point's measure from the set's, both in the ambient semiring like every
-- other world measure.
measureSet meta v (WExcept WFull p) = do
  let metaSub = unpruned meta
  anyRes    <- anyMarginal metaSub False v
  exceptRes <- toIRInferenceSave metaSub False v p
  mixSubP (semiringOf meta) (rBranches exceptRes) anyRes exceptRes
measureSet meta v (WExcept s p) = do
  let metaSub = unpruned meta
  sRes <- scopedMeasureSet metaSub v s
  let rt = rType (getTypeInfo v)
  ptO <- scoped (measureSet metaSub v (WPoint p const1))
  ptRes <- guardedResult (semiringOf meta) "except_pt" [memberGuard rt p s] ptO
  mixSubP (semiringOf meta) (rBranches sRes) sRes ptRes
-- Each side is measured in its own scope and keeps its own bindings, so
-- the untaken side's work sits under the selecting 'IRIf' rather than being
-- hoisted in front of it -- the same reason 'measureWorld' scopes a world's
-- measure under its guards. It matters here: the point side evaluates a
-- density at the witness value, which is precisely the 'VAny' this choice
-- exists to avoid touching.
--
-- Where a side's bindings are read by more than one field, the choice is bound
-- once as a packed result instead of folding them into every field: a side
-- that is itself a set-witness compile (the x-free factor of
-- @draw x = Normal in if x < 0.0 then (draw y = ...) else 2.0@ measures the
-- inner draw on its point side) was copied four times per nesting level, and
-- the -O0 IR grew ~9x per level (task slow-fuzz-seed-findings-2026-10-06,
-- SharedDrawInvariants seed 825059). The binding still selects with the same
-- 'IRIf', so only the taken side is evaluated; it lands in the caller's
-- scope, which every caller keeps under its own guards.
-- The bound closure ('closeNullExcept') decides only whether a point query at
-- the bound is a member; the set's measure is the interval minus the point's,
-- which is the interval's own for a continuous point. Measuring it once, from
-- the excepted side, keeps one CDF difference rather than two.
measureSet meta v s@(WChoice _ _ b) | isBoundClosure s = measureSet meta v b
measureSet meta v (WChoice c a b) = do
  oa <- scoped (measureSet meta v a)
  ob <- scoped (measureSet meta v b)
  let readers o = length (filter (openReads o) (resultFields (openValue o)))
  -- At most one reading field per side: each side's block goes inline into
  -- the one field that reads it, which copies nothing.
  if readers oa <= 1 && readers ob <= 1
    -- unsafeDistributeBlock: each side's block has at most one reader, so it
    -- is placed once, not copied.
    then return (zipResult (IRIf c) (unsafeDistributeBlock oa) (unsafeDistributeBlock ob))
    else do
      w <- mkVariable "choice"
      setVariables [(w, IRIf c (closeExpr oa packResult) (closeExpr ob packResult))]
      return (unpackResult w)
  where resultFields r = [unP (rProb r), rDim r, rBranches r, rImposs r]

-- | 'measureSet' in its own scope, its bindings re-attached to the
-- result: inline in the one field that reads them, else bound once
-- ('guardedResult' with no guards) rather than copied into every field.
scopedMeasureSet :: CompilerMetadata -> Expr -> WSet -> CompilerMonad PResult
scopedMeasureSet meta v s = do
  o <- scoped (measureSet meta v s)
  guardedResult (semiringOf meta) "scoped_set" [] o

cdfAtBound :: CompilerMetadata -> Expr -> WBound -> CompilerMonad (IRExpr, IRExpr)
cdfAtBound meta _ WNegInf = return (srZero (semiringOf meta), const1)
cdfAtBound meta _ WPosInf = return (srOne (semiringOf meta), const1)
cdfAtBound meta v (WFinite e) = do
  -- An interval's mass is a CDF difference, so both bounds are 'unpruned'.
  res <- toIRInference (unpruned meta) True v e
  return (unP (rProb res), rBranches res)

-- | The measure of the closed interval @[lo, hi]@ of an Int variable: @P(v <=
-- hi)@ minus @P(v <= lo - 1)@, the endpoints being integers
-- ('comparisonWorlds'). Measuring @CDF(hi) - CDF(lo)@ as the continuous case
-- does is @(lo, hi]@ and drops the atom at @lo@ (task
-- set-witness-int-comparison-boundary-non-strict).
--
-- The two CDFs are whole results, subtracted by 'mixSubP', not raw numbers.
-- An Int variable can hold an atom whose weight is a density: @if x == 0.0
-- then 0 else 2@ with @x@ a Normal, where @x == 0.0@ answers the density at
-- 0 at dim 1. Its CDF at 1 is that density, at dim 1, and @[2, inf]@ is
-- the mass 1 minus a density, which is the mass. The raw difference read the
-- density as a mass and answered 0.601 there. An unbounded end contributes
-- the certain mass (above) or nothing (below; 'mixWith' drops an impossible
-- subtrahend).
--
-- As in the continuous case, an empty interval is impossible: statically for
-- an infinite end on the wrong side, by a bounds test when both ends are
-- finite (the CDFs are evaluated only under it, so log space never takes the
-- log of a negative difference), and when the measure comes out a zero mass.
measureIntInterval :: CompilerMetadata -> Expr -> WBound -> WBound -> CompilerMonad PResult
measureIntInterval meta _ WPosInf _ = return (impossibleP (semiringOf meta))
measureIntInterval meta _ _ WNegInf = return (impossibleP (semiringOf meta))
measureIntInterval meta v lo hi = do
  let sr = semiringOf meta
  let cdfAt e = toIRInference (unpruned meta) True v e
  o <- scoped $ do
    hiRes <- case hi of
      WFinite e -> cdfAt e
      _         -> return (mass (srOne sr))
    loRes <- case lo of
      WFinite e -> cdfAt (IROp OpSub e (IRConst (VInt 1)))
      _         -> return (impossibleP sr)
    let bc = case (hi, lo) of
          (WFinite _, _) -> rBranches hiRes
          (_, WFinite _) -> rBranches loRes
          _              -> const1
    diff <- mixSubP sr bc hiRes loRes
    pVar <- mkVariable "ivl_mass"
    dVar <- mkVariable "ivl_dim"
    setVariables [(pVar, unP (rProb diff)), (dVar, rDim diff)]
    let zeroMass = IRIf (IROp OpEq (IRVar dVar) dim0)
                        (notIR (IROp OpGreaterThan (IRVar pVar) (srZero sr)))
                        constFalseIR
    return (impossibleWhen zeroMass diff { rProb = sealP (IRVar pVar), rDim = IRVar dVar })
  let nonEmpty = [notIR (IROp OpGreaterThan l h) | WFinite l <- [lo], WFinite h <- [hi]]
  closeResult sr "int_ivl" nonEmpty o

-- | Invert the observation @body ∈ target@ into constraint worlds on the bound
-- variable (occurrences @occs@). Nothing when some node on the way is not
-- supported — the caller refuses with a diagnostic.
--
-- Every world it returns is closed under the null-set convention of a
-- continuous variable ('closeNullExcept').
invertToWorlds :: CompilerMetadata -> [ChainName] -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
invertToWorlds meta occs exprBody target = do
  ws <- invertToWorldsStep meta occs exprBody target
  return (case occurrenceType occs exprBody of
    Just TFloat -> map closeWorld <$> ws
    _           -> ws)
  where closeWorld (WWorld gs s fs) = WWorld gs (closeNullExcept s) fs

-- | The type of the bound variable, read off one of its occurrences.
occurrenceType :: [ChainName] -> Expr -> Maybe RType
occurrenceType occs e = case e of
  Expr ti (Var _) | chainName ti `elem` occs -> Just (rType ti)
  _ -> listToMaybe (mapMaybe (occurrenceType occs) (getSubExprs e))

-- | The null-set convention of a continuous (Float) variable, applied to a
-- constraint set: an interval with one of its own bounds taken out is the
-- interval. Every interval is closed at its bounds ('boundGuards') so that a
-- boundary query answers the density, and removing the bound point is only
-- another spelling of the strict side of the same comparison: @v > 1.0@ is
-- @[1, inf]@ and answers the density at 1, but its negated spelling
-- @not ((v < 1.0) || (v == 1.0))@ came out as @[1, inf]@ minus the point 1
-- and answered impossible there (task
-- null-set-conventions-not-preserved-under-negation). The convention only
-- decides a point query's membership: 'measureSet' measures the closed shape
-- from its excepted side, which for a continuous point is the interval's
-- mass ('mixSubP'). Whether the point is a bound is decided at run time, as a
-- 'WChoice': a bound may be a transported or intersected expression. Like
-- 'boundGuards' it does not ask whether the bound is an atom of a mixed
-- Float variable (@if flip then 1.0 else Normal@), where a closed bound is
-- not a null set (task set-witness-null-set-boundary-conventions).
--
-- A point removed from the inside of an interval, or from the whole domain,
-- stays removed: there it is an event of its own, and @x == 0.0@ meeting the
-- complement of @x == 0.0@ is empty (set-witness/setWitnessContinuousEqualsTwice).
-- Float only: a removed point of a discrete variable is an atom, and a
-- removed point of a composite one may be a whole constructor
-- ('exceptPoint').
--
-- Idempotent: 'invertToWorlds' applies it at every level, so an already
-- closed set is recognised and left alone.
closeNullExcept :: WSet -> WSet
closeNullExcept s | isBoundClosure s = s
closeNullExcept (WExcept s p) = case closeNullExcept s of
  WChoice c a b -> WChoice c (closeNullExcept (WExcept a p)) (closeNullExcept (WExcept b p))
  ivl@(WInterval lo hi) | Just c <- boundTest p lo hi -> WChoice c ivl (WExcept ivl p)
  s' -> WExcept s' p
closeNullExcept (WChoice c a b) = WChoice c (closeNullExcept a) (closeNullExcept b)
closeNullExcept s = s

-- | The shape 'closeNullExcept' builds: an interval, or that interval minus
-- the point @p@ unless @p@ is one of its bounds.
isBoundClosure :: WSet -> Bool
isBoundClosure (WChoice c ivl@(WInterval lo hi) (WExcept ivl' p)) =
  ivl `sameIntervalAs` ivl' && Just c == boundTest p lo hi
isBoundClosure _ = False

-- | Is @p@ one of the interval's finite bounds? Nothing when it has none.
boundTest :: IRExpr -> WBound -> WBound -> Maybe IRExpr
boundTest p lo hi = case [IROp OpEq p e | WFinite e <- [lo, hi]] of
  [] -> Nothing
  ts -> Just (foldr1 (IROp OpOr) ts)

sameIntervalAs :: WSet -> WSet -> Bool
sameIntervalAs (WInterval lo1 hi1) (WInterval lo2 hi2) = sameBound lo1 lo2 && sameBound hi1 hi2
  where sameBound WNegInf WNegInf = True
        sameBound WPosInf WPosInf = True
        sameBound (WFinite a) (WFinite b) = a == b
        sameBound _ _ = False
sameIntervalAs _ _ = False

invertToWorldsStep :: CompilerMetadata -> [ChainName] -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
invertToWorldsStep meta occs exprBody target
  -- x-free subtree: deterministic given scope reduces to a membership test of
  -- its value against the target; anything else draws fresh randomness, which
  -- is independent of the bound draw and so becomes a factor of the world
  -- ('worldFactorFree', task world-residual-factor-delegation).
  | not (subtreeHasOcc occs exprBody) =
      if pType (getTypeInfo exprBody) == Deterministic
        then do
          bIR <- toIRGenerate meta exprBody
          return (Just [WWorld [memberGuard (rType (getTypeInfo exprBody)) bIR target] WFull []])
        else worldFactorFree meta exprBody target
-- A continuous or discrete @==@ whose bound-variable operand is not the bare
-- occurrence itself (@exp x == 1.0@, @x + 1.0 == 1.0@) is split here, before
-- 'transportDirect' can see it. The point transport would seed forward
-- chaining at the @==@ node, whose inverse on the False polarity is the
-- 'VAnyExcept' sentinel ("any value other than c") -- and every further
-- inverse step on the way down to the bound variable then applies its own
-- arithmetic and applicability guard to that sentinel (@log@, @b > 0@,
-- @b - 1.0@), which is undefined on a set and crashed both the optimizer and
-- the interpreter (task set-witness-exp-equality-guard-vanyexcept-crash).
-- The bare @x == c@ shape needs no inverse step below the sentinel, so it is
-- left on the path it already answers correctly.
invertToWorldsStep meta occs (Expr _ (InjF (Named "eq") [lop, rop])) target@(WPoint _ _)
  | Just (side, other) <- eqOperands
  , not (isBareOcc side) = equalityWorlds meta occs side other target
  where
    eqOperands
      | subtreeHasOcc occs lop && not (subtreeHasOcc occs rop) && pType (getTypeInfo rop) == Deterministic = Just (lop, rop)
      | subtreeHasOcc occs rop && not (subtreeHasOcc occs lop) && pType (getTypeInfo lop) == Deterministic = Just (rop, lop)
      | otherwise = Nothing
    isBareOcc (Expr ti (Var _)) = chainName ti `elem` occs
    isBareOcc _ = False
-- A constructor test @isC e@ whose operand reaches the bound variable through
-- further inverse steps (@isRed (col (head scene))@) is split the same way, and
-- for the same reason: its inverse on the False polarity is the 'VAnyExcept'
-- sentinel "any value but @C _ ..@", and the steps below it (a field accessor
-- building @Obj sentinel@, @head@ building a list around that) bury it inside a
-- structure no set reads back out. Observed True it is @e@ at the point @C@
-- with every field the wildcard -- the inverse's own True arm -- and observed
-- False the complement of that point ('complementWorlds'). A bare occurrence
-- (@isC x@) keeps the path that already answers it ('witnessSet').
invertToWorldsStep meta occs (Expr _ (InjF (Named name) [side])) target@(WPoint _ _)
  | name /= "eq", hasAnyExcept (adtDecls meta) name
  , subtreeHasOcc occs side, not (isBareOcc side)
  , FPair _ [FDecl {body = IRIf _ pos (IRConst (VAnyExcept _))}] <- lookupFPair (adtDecls meta) name =
      complementWorlds meta occs side pos target
  where
    isBareOcc (Expr ti (Var _)) = chainName ti `elem` occs
    isBareOcc _ = False
invertToWorldsStep meta occs exprBody target = do
  direct <- transportDirect meta occs exprBody target
  case direct of
    Just ws -> return (Just ws)
    Nothing -> case exprBody of
      Expr _ (IfThenElse c t e)
        | not (subtreeHasOcc occs c) && pType (getTypeInfo c) == Deterministic -> do
            g <- toIRGenerate meta c
            wsT <- invertToWorlds meta occs t target
            wsE <- invertToWorlds meta occs e target
            case (wsT, wsE) of
              (Just ts, Just es) -> return (Just (map (addGuard g) ts ++ map (addGuard (IRUnaryOp OpNot g)) es))
              _ -> return Nothing
        | otherwise -> do
            -- the condition constrains the same draw: case split and intersect.
            -- An x-free condition that draws fresh randomness takes the same
            -- split: each polarity inverts through the x-free clause into one
            -- unconstrained world carrying P(c = polarity) as its factor
            -- ('worldFactorFree'), so the arms are weighted by the condition's
            -- two masses -- the set-witness twin of 'planFactorBool'.
            cT <- invertToWorlds meta occs c (WPoint constTrueIR const1)
            cF <- invertToWorlds meta occs c (WPoint (IRConst (VBool False)) const1)
            wsT <- invertToWorlds meta occs t target
            wsE <- invertToWorlds meta occs e target
            case (cT, cF, wsT, wsE) of
              (Just cts, Just cfs, Just ts, Just es) ->
                return (Just ([intersectW cw tw | cw <- cts, tw <- ts]
                           ++ [intersectW cw ew | cw <- cfs, ew <- es]))
              _ -> return Nothing
      Expr _ (InjF (Named "lt") [lop, rop]) -> comparisonWorlds meta occs False lop rop target
      Expr _ (InjF (Named "gt") [lop, rop]) -> comparisonWorlds meta occs True lop rop target
      -- Boolean connectives: invert each leaf at both canonical polarities
      -- (via 'invertBoolToWorlds', which is exactly the device the
      -- IfThenElse condition case above already uses on itself), then
      -- recombine. 'and'/'or' observed at their "natural" polarity (and+True,
      -- or+False) are a plain intersection; the other polarity needs the
      -- disjoint decomposition from the task sketch --
      -- not(a&&b) = not(a) or (a&&not(b)), a||b = a or (not(a)&&b) -- so the
      -- two (generally overlapping) sets of worlds are never both measured.
      -- 'not' just swaps which list is which. Mirrors 'planInvert's
      -- "not"/"and"/"or" cases, the plan-guided engine's analogous fold over
      -- (True-worlds, False-worlds) pairs.
      Expr _ (InjF (Named "not") [a]) -> do
        ab <- invertBoolToWorlds meta occs a
        return (case ab of
          Just (at, af) -> Just (boolWorlds target af at)
          Nothing       -> Nothing)
      Expr _ (InjF (Named "and") [a, b]) -> do
        ab <- invertBoolToWorlds meta occs a
        bb <- invertBoolToWorlds meta occs b
        case (ab, bb) of
          (Just (at, af), Just (bt, bf)) ->
            let tw = [intersectW aw bw | aw <- at, bw <- bt]
                fw = af ++ [intersectW aw bw | aw <- at, bw <- bf]
            in return (Just (boolWorlds target tw fw))
          _ -> return Nothing
      Expr _ (InjF (Named "or") [a, b]) -> do
        ab <- invertBoolToWorlds meta occs a
        bb <- invertBoolToWorlds meta occs b
        case (ab, bb) of
          (Just (at, af), Just (bt, bf)) ->
            let tw = at ++ [intersectW aw bw | aw <- af, bw <- bt]
                fw = [intersectW aw bw | aw <- af, bw <- bf]
            in return (Just (boolWorlds target tw fw))
          _ -> return Nothing
      Expr _ (InjF (Named "TCons") [pa, pb]) -> case target of
        WPoint s _ -> do
          wsA <- invertToWorlds meta occs pa (WPoint (IRDestruct AcFst s) const1)
          wsB <- invertToWorlds meta occs pb (WPoint (IRDestruct AcSnd s) const1)
          case (wsA, wsB) of
            (Just as, Just bs) -> return (Just [intersectW a b | a <- as, b <- bs])
            _ -> return Nothing
        -- a multivariate CDF over correlated components is not defined here
        _ -> return Nothing
      -- Nested let (`let y = e in b`, which the parser desugars to this Apply
      -- of a literal lambda): invert in two stages (task
      -- set-witness-nested-let-classifier). Every structural case above only
      -- fires when it sits DIRECTLY under the bound let, so an intermediate
      -- named binding between the random source and the comparison that
      -- constrains it -- `let x = Normal in let y = x + 1.0 in if y > 0.0 ...`,
      -- even the trivial rename `let y = x in ...` -- used to fall to the
      -- catch-all. The occurrence of x sits in `e`, so `e` is never x-free and
      -- the deterministic-given-scope admission cannot apply; the fix is to
      -- invert THROUGH the binding rather than to look past it.
      -- An inner binding the body reads once, with no binder on the way
      -- ('readOnceInPlace'), where x is in the body (with or without `e`):
      -- the read has the value's own law, so the body is inverted with the
      -- value in place, as 'worldsShape' walks it (task
      -- dispatch-on-law-certificates). The two-stage inversion below keeps
      -- the case of x in `e` alone.
      Expr _ (Apply (Expr _ (Lambda y b)) e)
        | subtreeHasOcc occs b, entersInPlace isValue y e b ->
            invertToWorlds meta occs (enterInPlace isValue exprBody) target
      Expr _ (Apply (Expr lamTI (Lambda y b)) e)
        -- x in `e` only. With x in `b` as well, x-sets from `e` and y-sets
        -- from `b` would have to be mixed in one intersection, and with x in
        -- `b` alone the worlds on `b` would reference the inner binding's
        -- value, which is not in scope where the worlds are measured; both
        -- keep today's refusal.
        | subtreeHasOcc occs e && not (subtreeHasOcc occs b) -> do
            -- The lambda is literal, so its own chain name is the key (no
            -- 'equivalentLambda' resolution of a Var to a top-level function
            -- is involved).
            let occsY = fromMaybe [] (Map.lookup (chainName lamTI) (lambdaVarOccurrences (fcData meta)))
            twoStage <- invertThroughBinding meta occs occsY b e target
            -- Where the two stages do not invert (a body projecting the
            -- bound pair, @draw v = (x, 0.0) in fst v@), a binding read in
            -- place is entered in place, as 'worldsShape' falls back to.
            case twoStage of
              Nothing | entersInPlace isValue y e b -> invertToWorlds meta occs (enterInPlace isValue exprBody) target
              _ -> return twoStage
      -- A call -- of a named function, a function parameter, a let-bound
      -- lambda -- is the same binding as a @let@ (task
      -- binding-resolver-one-application-rule): the observation is inverted
      -- through the callee's body onto its parameter, then through the
      -- argument onto x. 'callBindingAt' resolves which parameter x reaches
      -- and binds the others.
      Expr _ (Apply _ _) -> do
        cb <- callBindingAt meta occs exprBody
        case cb of
          Nothing -> return Nothing
          Just (meta', occsY, b, e) -> invertThroughBinding meta' occs occsY b e target
      -- A projection of a literal pair is that field, in distribution: the
      -- other field's value is discarded, so its randomness marginalises to
      -- one and its reads of x constrain nothing. Reached only where the
      -- whole subtree did not transport ('transportDirect' has no interval
      -- step through @fst@, and none for several occurrences). An inner
      -- binding read in place that holds the pair is entered first
      -- ('enterInPlace'), as 'worldsShape' does.
      Expr _ (InjF (Named "fst") [p])
        | Expr _ (InjF (Named "TCons") [a, _]) <- enterInPlace isValue p -> invertToWorlds meta occs a target
      Expr _ (InjF (Named "snd") [p])
        | Expr _ (InjF (Named "TCons") [_, b]) <- enterInPlace isValue p -> invertToWorlds meta occs b target
      Expr _ (InjF (Named op) args)
        | op `notElem` structuralInjFs, not (isFieldConstructor (adtDecls meta) op)
        , [a] <- filter (subtreeHasOcc occs) args
        , all (\o -> subtreeHasOcc occs o || pType (getTypeInfo o) == Deterministic) args
        -> invertThroughStep meta occs exprBody a target
      _ -> return Nothing
  where
    -- The variables an inner binding may alias and be entered in place at
    -- every read, as 'worldsShape' enters it ('entersInPlace').
    isValue = valueVar (WorldsCtx (fcData meta) (adtDecls meta) (functions (compilingProgram meta)) permissiveDet)

-- | The InjFs 'invertToWorldsStep' and 'worldsShape' invert structurally
-- rather than as one step of a transport.
structuralInjFs :: [String]
structuralInjFs = ["eq", "lt", "gt", "not", "and", "or", "TCons"]

-- | One InjF step @f (.., a, ..)@ whose operand @a@ alone reads x (@occs@)
-- but does not transport as a whole -- an @if@-mixture, several occurrences
-- -- wrapped in an invertible step: @(if x < 0.0 then 0.0 - x else x) +
-- 0.0@. The step is the binding @let y = a in f (.., y, ..)@ without the
-- @let@: the observation is transported through the step alone, seeded at
-- the node and stopping at @a@ ('transportDirect' with @a@ in the variable's
-- role, so a point picks up the step's change of variables and an interval
-- the step's direction), and each resulting set is the target for inverting
-- @a@ onto x ('invertOntoValue'). Field constructors are not steps here: their
-- inverse consults no sibling field, which a residue factor at a bare
-- occurrence makes up for ('residueFactor'), not at an operand.
invertThroughStep :: CompilerMetadata -> [ChainName] -> Expr -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
invertThroughStep meta occs stepNode a target = do
  ws <- transportDirect meta [chainName (getTypeInfo a)] stepNode target
  maybe (return Nothing) (invertOntoValue meta occs a) ws

-- | The two-stage inversion through one binding of @y@ to @e@ over body @b@,
-- with x (@occs@) in @e@ only (task set-witness-nested-let-classifier): the
-- observation is inverted onto y's occurrences @occsY@ in @b@, and each
-- resulting y-set is the target for inverting @e@ onto x.
invertThroughBinding :: CompilerMetadata -> [ChainName] -> [ChainName] -> Expr -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
invertThroughBinding meta occs occsY b e target = do
            -- Stage 1: invert the body onto y, using y's own occurrence list
            -- exactly as 'setWitnessApply' does for the outer variable. Every
            -- structural case -- if-splits, comparisons,
            -- connectives, tuples, multiple occurrences of y -- works here
            -- unchanged; a dead y makes `b` y-free and reduces to the
            -- membership test of a deterministic body.
            wsY <- invertToWorlds meta occsY b target
            maybe (return Nothing) (invertOntoValue meta occs e) wsY

-- | Stage 2 of 'invertThroughBinding': each world's set on the value of @e@
-- (the bound value of an inner binding, or the operand of an 'InjF' step,
-- 'invertThroughStep') becomes the target for inverting @e@ onto x
-- (@occs@).
invertOntoValue :: CompilerMetadata -> [ChainName] -> Expr -> [WWorld] -> CompilerMonad (Maybe [WWorld])
invertOntoValue meta occs e ys = do
                -- Stage 2: each y-set is the target for inverting `e` onto x.
                -- 'invertToWorlds' takes an arbitrary target set, so an
                -- interval on y becomes an interval on x through
                -- 'transportDirect''s existing monotone transport (decreasing
                -- case included) and a point on y through its point transport,
                -- whose change-of-variables factor composes with the one the
                -- y-world already carries (chain rule). Stage-1 guards only
                -- arise from y-free deterministic subtrees or the target, so
                -- they never mention y's value and need no rebinding.
                -- A 'WFull'/'WEmpty' y-set says nothing about y's value, hence
                -- nothing about x's, and `e` is not consulted at all
                -- ('transportDirect' has no case for those targets). A
                -- fresh-randomness `e` is refused where a single let refuses
                -- it: 'transportDirect' finds no seeded inverse through the
                -- extra draw.
                let through gY fY setY = case setY of
                      WFull  -> return (Just [WWorld gY WFull fY])
                      WEmpty -> return (Just [WWorld gY WEmpty fY])
                      -- A runtime choice of y-set -- what every point
                      -- constraint meeting an interval constraint produces
                      -- ('pointInInterval'), i.e. the `if y > 0.0 then right
                      -- y else left ()` shape -- transports side by side.
                      -- Since a LIST of worlds is returned here, the choice
                      -- becomes two mutually exclusive guard groups rather
                      -- than a 'WChoice' on x: a side may transport to
                      -- several worlds, and there is no single 'WSet' to put
                      -- those into. 'guardP' nests a world's guards in list
                      -- order, so this measures the same as 'measureSet''s
                      -- 'IRIf c' over the two sides -- provided the choice
                      -- condition sits AFTER the y-guards (it reads the
                      -- witness value, e.g. @isAny (fromRight s)@, which is
                      -- only safe to evaluate once the applicability guard
                      -- @isRight s@ among them has held) and BEFORE the
                      -- x-guards (whose transport of that same value is only
                      -- meaningful on the chosen side).
                      WChoice c sa sb -> do
                        wa <- through (gY ++ [c]) fY sa
                        wb <- through (gY ++ [notIR c]) fY sb
                        return ((++) <$> wa <*> wb)
                      -- An alias, @y = x@: the y-set is the x-set, whatever
                      -- its shape (a point transport has no case for an
                      -- exclusion set, which an @==@ observed False makes).
                      _ | Expr eTI (Var _) <- e, chainName eTI `elem` occs ->
                            return (Just [WWorld gY setY fY])
                      _ -> do
                        wsX <- invertToWorlds meta occs e setY
                        -- A y-world's residue factors read y at its observed
                        -- value, a function of the sample alone, so they
                        -- carry over to the x-worlds unchanged.
                        return (map (\(WWorld gX setX fX) -> WWorld (gY ++ gX) setX (fY ++ fX)) <$> wsX)
                xs <- forM ys $ \(WWorld gY setY fY) -> through gY fY setY
                -- The y-worlds partition the observation and each one's
                -- x-worlds partition that y-set's preimage, so the result is
                -- their union with guards concatenated -- the same rule the
                -- 'TCons' and if-condition cases use.
                return (concat <$> sequence xs)

-- | The binding a set-witness traversal enters at a call node @node@ whose
-- value x (@occs@) reaches through exactly one argument: the metadata with
-- every other parameter bound (each renamed to a fresh variable let-bound to
-- its argument, which must be deterministic given scope), the bound
-- parameter's occurrences, the callee body, and the argument x flows through.
--
-- A saturated call of a top-level function binds whichever parameter x
-- reaches, in any position. A recursive callee is declined: entering its body
-- would meet the call again, and the traversal would not terminate. Any other
-- callee is resolved as one application ('resolveBinding') and taken when its
-- body is meaningful in this scope and x is in the argument only.
callBindingAt :: CompilerMetadata -> [ChainName] -> Expr -> CompilerMonad (Maybe (CompilerMetadata, [ChainName], Expr, Expr))
callBindingAt meta occs callNode
  | (Expr _ (Var f), args@(_:_)) <- flattenApplySpine callNode
  , Just decl <- lookup f fs
  , let lams = lambdaSpine decl
  , length lams == length args
  , not (isRecursiveFunction (compilingProgram meta) f)
  , [k] <- [ i | (i, a) <- zip [0 :: Int ..] args, subtreeHasOcc occs a ]
  , and [ pType (getTypeInfo a) == Deterministic | (i, a) <- zip [0..] args, i /= k ]
  = do
      let calleeBody = finalBody decl
          (lamK, pK) = lams !! k
          others = [ (p, a) | (i, (_, p), a) <- zip3 [0..] lams args, i /= k ]
      renames <- forM others $ \(p, a) -> do
        fresh <- mkVariable p
        aIR <- toIRGenerate meta a
        setVariables [(fresh, aIR)]
        return (p, fresh, rType (getTypeInfo a))
      let meta' = enteredScope calleeBody [ (p, fresh) | (p, fresh, _) <- renames ]
                    (bindRenamed meta [ (fresh, rty, a) | ((_, a), (_, fresh, rty)) <- zip others renames ])
          freshNames = [ fresh | (_, fresh, _) <- renames ]
          calleeBody' = reinferRecovered meta' freshNames
                    (foldr (\(p, fresh, _) -> renameFreeVar p fresh) calleeBody renames)
          occsK = fromMaybe [] (Map.lookup lamK (lambdaVarOccurrences (fcData meta)))
      -- A later parameter of the same name shadows this one in the body.
      if pK `elem` [ p | (_, p) <- drop (k + 1) lams ] then return Nothing
        else return (Just (meta', occsK, calleeBody', args !! k))
  -- A function parameter bound to a lambda this compile can see.
  | Expr _ (Apply (Expr _ (Var g)) e) <- callNode
  , Just (Expr lamTI (Lambda y lamBody)) <- lookup g (boundLambdas meta)
  , readsOnlyScope meta [y] lamBody
  = return (Just (meta, fromMaybe [] (Map.lookup (chainName lamTI) (lambdaVarOccurrences (fcData meta))), lamBody, e))
  | Expr _ (Apply l e) <- callNode
  , isJust (Map.lookup (chainName (getTypeInfo l)) (chainNameInfo (fcData meta)))
  , Just (_, LambdaInfo{}, _) <- findEquivalentExpression (fcData meta) (chainName (getTypeInfo l))
  , not (subtreeHasOcc occs l)
  , let b = resolveBinding meta l e
  , bindInline b
  = return (Just (meta, bindOccs b, bindBody b, e))
  | otherwise = return Nothing
  where
    fs = functions (compilingProgram meta)
    lambdaSpine (Expr ti (Lambda p b)) = (chainName ti, p) : lambdaSpine b
    lambdaSpine _ = []
    finalBody (Expr _ (Lambda _ b)) = finalBody b
    finalBody e = e

-- | Point/interval transport of a whole subtree onto its single occurrence of
-- the bound variable, via forward chaining seeded at the subtree root. Only
-- fires for exactly one occurrence: with several, a point inversion through
-- one of them would silently drop the others' constraints — the structural
-- cases above split those instead.
--
-- One occurrence is not enough for the transport to carry the whole
-- observation, though. Every step of the inverse path consumes its sibling
-- operands as premises (`x + c` is inverted as `s - c`), EXCEPT a field
-- constructor's: the deconstructing inverse of `(x, e)` is `fst s`, and `e`
-- is never looked at -- so `(x, 1.0)` observed at `(0.7, 0.0)` transported
-- to `x = 0.7` with full density, and `(s, Normal)` lost the sibling's
-- density altogether (task set-witness-transport-drops-sibling-field-
-- constraint). A spine that crosses a field constructor therefore also
-- carries the subtree's residue as a world factor: the subtree compiled
-- against the same target with the bound variable fixed at its witness
-- ('residueFactor'), which is the point-witness path's body-factor fold
-- applied per world. For a residue that is deterministic given the witness
-- that factor is the missing consistency indicator (dim 0); for one that
-- draws fresh randomness it is the sibling's own density (dims add). The
-- factor is omitted where no field constructor (or call, 'isNamedCallNode')
-- is crossed, because there
-- the inverse path already consumed every sibling and the indicator would
-- be an always-true tautology on every transported subtree in the corpus.
transportDirect :: CompilerMetadata -> [ChainName] -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
transportDirect meta occs exprBody target = case filter (`elem` subtreeCNs exprBody) occs of
  [occ] -> case target of
    WPoint s c0 -> case toSeededInvExpr (fcData meta) (adtDecls meta) bodyCN occ of
      Nothing -> return Nothing
      Just InvChain{invValue = g0, invCoV = cov0, invGuard = guard0, invReadsAny = ra0} -> do
        g     <- pruneDeadLetIns <$> materializeAnchors meta g0
        cov   <- pruneDeadLetIns <$> materializeAnchors meta cov0
        guard <- pruneDeadLetIns <$> materializeAnchors meta guard0
        ra    <- pruneDeadLetIns <$> materializeAnchors meta ra0
        let applyTo e arg = IRApply (IRLambda bodyCN e) arg
        -- A step of the chain reading a marginal wildcard ('invReadsAny'):
        -- @x + 0.0@ observed at ANY. The step has no value to compute -- its
        -- arithmetic on the wildcard was a raw type error (@Minus (VAny, 0.0)@,
        -- or the comparison of a condition evaluated at the witness) -- and
        -- the observation says nothing about the bound variable through this
        -- occurrence: the set is 'WFull', as the bare @x@ in the same slot
        -- recovers the wildcard itself, and no guard, value or change of
        -- variables of the chain is evaluated on that side. The world's
        -- domain guard holds there, as the point-witness fold's does
        -- ('pointInvert'). Task any-slot-through-injf-inverse-reaches-condition.
        -- Decided statically where the target is a literal (an if's
        -- canonical True/False target): no wildcard there, and the set keeps
        -- the shape its consumers match on.
        let readsAny = case foldWildcardTest (substIRVar bodyCN s ra) of
              IRConst (VBool False) -> Nothing
              r -> Just r
            unlessAny e = maybe e (\r -> IRIf r constTrueIR e) readsAny
            wildcardSide set = maybe set (\r -> WChoice r WFull set) readsAny
            wildValue rt v = maybe v (\r -> IRIf r (IRConst (anyOfType rt)) v) readsAny
        -- The inversion may pass through a deconstructing InjF (e.g.
        -- fromLeft/fromRight) only applicable on one arm; fold that as an
        -- extra world guard so measureWorld zeroes this world instead of
        -- evaluating the (crashing on the wrong arm) point value -- see
        -- observe-partials-umbrella N1b.
        -- Substitute eagerly (rather than leaving an IRApply/IRLambda shell
        -- for the interpreter to beta-reduce at runtime) so the witness value
        -- is a genuinely literal expression -- e.g. @IRConstruct TgTuple
        -- [IRDestruct AcFst sample, IRConst VAny]@ rather than that same tree hidden behind an
        -- application -- for 'mergeWitnessValue' (see 'intersectSet') to
        -- pattern-match on directly when this witness is later intersected
        -- with another occurrence's.
        let value = substIRVar bodyCN s g
        factors <- case pathToCN occ exprBody of
          Just spine@(_:_)
            | any (\n -> isFieldCtorNode meta n || isNamedCallNode n || letHidesField meta n) (init spine)
            , Expr occTI (Var boundName) <- last spine -> do
                f <- residueFactor meta exprBody boundName (rType occTI) (wildValue (rType occTI) value) s
                return [f]
          _ -> return []
        -- A path through an '==' (or constructor test) observed False
        -- recovers "any value but this one" as a 'VAnyExcept' sentinel.
        -- 'witnessSet' turns the shapes it recognises into an exclusion set;
        -- one it does not stays a point world, which measured the sentinel as
        -- a point (@w@ through @draw v = w in v == 1@ at False answered 0).
        -- That transport is declined: the structural cases invert through
        -- the binding instead.
        --
        -- The residue factor is the subtree compiled with the bound variable
        -- fixed at 'value', so it, too, is only defined where the witness is
        -- a point. With an exclusion set on the other side, it bound the
        -- variable to the sentinel itself, which no backend can render
        -- (@draw v = Normal in if True then (0.0, v == 1.0) else (0.0, True)@;
        -- task slow-fuzz-seed-findings-2026-10-06, BackendsAgree seed 801831).
        -- Measuring the set against a residue would take the complement of a
        -- product, which 'equalityWorlds' declines for the same reason.
        case witnessSet value (IROp OpMult c0 (applyTo cov s)) of
          WPoint v _ | hasAnyExceptExpr v -> return Nothing
          _ | not (null factors), hasAnyExceptExpr value -> return Nothing
          set -> return (Just [WWorld [unlessAny (applyTo guard s)] (wildcardSide set) factors])
    WInterval lo hi -> case toSeededMonotoneInvExpr (fcData meta) (adtDecls meta) bodyCN occ of
      Nothing -> return Nothing
      Just (g0, dir) -> do
        g <- pruneDeadLetIns <$> materializeAnchors meta g0
        let tr (WFinite e) = WFinite (IRApply (IRLambda bodyCN g) e)
            tr b = b
        -- a decreasing inverse swaps the endpoints, infinities included
        let flipInf WNegInf = WPosInf
            flipInf WPosInf = WNegInf
            flipInf b = b
        let (lo', hi') = case dir of
              MonInc -> (tr lo, tr hi)
              MonDec -> (flipInf (tr hi), flipInf (tr lo))
        -- No residue factor: the monotone table has no field-constructor
        -- step, so an interval never transports through one.
        return (Just [WWorld [] (WInterval lo' hi') []])
    _ -> return Nothing
  _ -> return Nothing
  where bodyCN = chainName (getTypeInfo exprBody)

-- | Folds a wildcard test ('invReadsAny' applied to a target) as far as its
-- literals decide it: 'OpIsAny' of a constant, a projection of a constant
-- tuple, an 'IRIf' on a constant, a let of a constant.
foldWildcardTest :: IRExpr -> IRExpr
foldWildcardTest = pruneDeadLetIns . irMap step
  where
    step e = case e of
      IRUnaryOp OpIsAny (IRConst v) -> IRConst (VBool (isHole v))
      IRDestruct AcFst (IRConst (VTuple a _)) -> IRConst a
      IRDestruct AcSnd (IRConst (VTuple _ b)) -> IRConst b
      IRIf (IRConst (VBool b)) t f -> if b then t else f
      IRLetIn n _ b@(IRConst _) | not (freeInIR n b) -> b
      -- A constant side operand (@==@'s compared value) is let-bound.
      IRLetIn n c@(IRConst _) b -> foldWildcardTest (substIRVar n c b)
      _ -> e
    isHole VAny = True
    isHole (VList AnyList) = True
    isHole _ = False

-- | The nodes from @e@'s root down to (and including) the node carrying chain
-- name @cn@, root first; Nothing when no node in @e@ carries it.
pathToCN :: ChainName -> Expr -> Maybe [Expr]
pathToCN cn e
  | chainName (getTypeInfo e) == cn = Just [e]
  | otherwise = listToMaybe (mapMaybe (fmap (e :) . pathToCN cn) (getSubExprs e))

-- | Is this node a multi-field constructor application (tuple, cons, user
-- ADT constructor)? These are the InjFs whose inverse for one field is
-- deconstructing -- it reads the sample's projection and consults no sibling
-- field -- so they are exactly the steps a point transport can pass through
-- while dropping constraints ('transportDirect').
isFieldCtorNode :: CompilerMetadata -> Expr -> Bool
isFieldCtorNode meta (Expr _ (InjF (Named n) _)) = isFieldConstructor (adtDecls meta) n
isFieldCtorNode _ _ = False

-- | A @let@ (an application of a lambda in place) whose bound variable reaches a
-- field constructor in its body. A spine down to an occurrence in the bound
-- value is inverted through that body by forward chaining, which crosses its
-- field constructors just as a syntactic one would: @draw y = x in (y, y +
-- 1.0)@ is inverted onto @x@ as @fst s@, and the second field was dropped
-- (found once a named helper with such a body reached this engine, task
-- binding-resolver-one-application-rule).
letHidesField :: CompilerMetadata -> Expr -> Bool
letHidesField meta (Expr _ (Apply (Expr _ (Lambda y b)) _)) =
  occursUnderFieldCtor (adtDecls meta) y b || any isNamedCallNode (universeExpr b)
  where universeExpr e = e : concatMap universeExpr (getSubExprs e)
letHidesField _ _ = False

-- | An application whose callee is not a literal lambda: a call of a named (or
-- otherwise resolved) function. Forward chaining inverts through such a call
-- by a per-invocation tagged copy of the callee's body, which crosses that
-- body's field constructors just as a syntactic one would -- `h x` with
-- `h x = (x, 1.0)` is inverted as `fst s` -- so a spine through one carries
-- the same residue factor (task named-function-list-head-witness-not-recovered).
isNamedCallNode :: Expr -> Bool
isNamedCallNode (Expr _ (Apply (Expr _ (Lambda {})) _)) = False
isNamedCallNode (Expr _ (Apply _ _)) = True
isNamedCallNode _ = False

-- | The residue factor of a transported subtree: @subtree@ compiled as an
-- ordinary point observation against @target@, with the bound variable
-- @boundName@ fixed at its transported witness @value@. The variable is
-- re-typed 'Deterministic' for dispatch ('reinferRecovered', as the
-- point-witness fold does for the recovered variable) and bound by an
-- 'IRLetIn' around the compiled block, so the block is self-contained: its
-- floated bindings stay under that binding (they may read it, and evaluation
-- is strict), and the result can be multiplied into a world's measure
-- anywhere under the world's guards. The block is the factor's one binding
-- and its fields project that variable, like 'worldFactorFree''s factor:
-- 'measureWorld' emits it once, under the world's guards. Unpacked inline, each
-- of the four fields carried its own copy of the block, which compounds through
-- a residue whose subtree holds another field constructor of a witnessed let
-- (task presult-unbound-block-copied-per-field).
residueFactor :: CompilerMetadata -> Expr -> String -> RType -> IRExpr -> IRExpr -> CompilerMonad WFactor
residueFactor meta subtree boundName boundRT value target = do
  let recovered = boundName : recoveredVars meta
  let retyped = reinferRecovered meta recovered subtree
  let fMeta = recoverVars [boundName] meta { typeEnv = (boundName, (boundRT, False)) : typeEnv meta }
  block <- scoped (toIRInference fMeta False retyped target) <&> generateLetInBlock fMeta
  fv <- mkVariable "residue_factor"
  return (WFactor (openWith [(fv, IRLetIn boundName value block)] (unpackResult fv)))

-- | An x-free subtree that draws fresh randomness, measured as a factor of an
-- otherwise unconstrained world (task world-residual-factor-delegation). It
-- mentions no occurrence of the bound variable, and every random draw in SPLL
-- is a syntactic leaf, so it is independent of the bound draw: inside a world
-- it contributes an independent factor, the product rule the point-witness
-- body-factor fold and 'residueFactor' already apply ('measureWorld' folds it
-- in with 'prodP'; dims and branch counts add).
--
-- "Measure the subtree against the target set" is exactly what 'measureSet'
-- does for the bound distribution, so it is reused with the subtree in that
-- role: a point is the subtree's density or mass there (with the target's
-- change-of-variables factor, which is not 1 when the target is a nested
-- let's transported y-point), an interval its CDF difference (both bounds
-- unpruned), 'WFull' certainty and a 'WChoice' either side at runtime. It
-- runs in its own scope folded into a self-contained block, so the
-- factor is evaluated under the world's guards and never hoisted past them.
--
-- Two refusals, both answering Nothing (the caller's refusal, or the runtime
-- 'IRError' of a cumulative query):
--
-- * An interval target on a non-scalar subtree: its CDF would be a
--   multivariate one, which nothing provides.
-- * A subtree reading a random local of the ambient scope -- an enclosing
--   eager @draw@ is ONE draw shared by every use, so the subtree would not be
--   independent of the bound draw's other readers. The same local,
--   conservative check the plan engine's factors make ('planFactorExternals').
worldFactorFree :: CompilerMetadata -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
worldFactorFree meta sub target
  | not (null (planFactorExternals (typeEnv meta) (recoveredVars meta) sub)) = return Nothing
  | hasInterval target && not (isScalar (rType (getTypeInfo sub))) = return Nothing
  | otherwise = do
      block <- scoped (measureSet meta sub (wildcardTolerant target)) <&> generateLetInBlock meta
      fv <- mkVariable "xfree_factor"
      return (Just [WWorld [] WFull [WFactor (openWith [(fv, block)] (unpackResult fv))]])
  where
    hasInterval (WInterval _ _) = True
    hasInterval (WChoice _ a b) = hasInterval a || hasInterval b
    hasInterval (WExcept s _) = hasInterval s
    hasInterval _ = False
    -- A point target is a projection of the query sample, so it can be the
    -- marginal wildcard at runtime (the @ANY@ of @p((-2.0, ANY))@ reaching the
    -- x-free @exp Uniform@ of @(h1, exp Uniform)@). The subtree is measured by
    -- 'toIRInference', whose inverse steps apply arithmetic to their sample
    -- and are not wildcard-safe below the top level ('toIRInferenceSave'
    -- guards only there), so a wildcard point would reach @log ANY@. A
    -- wildcard constrains nothing: the factor is the subtree's marginal, a
    -- certain world ('WFull'). The runtime choice keeps the density side under
    -- its own 'IRIf' ('measureSet''s 'WChoice' scopes each side), which is
    -- also what keeps batched mode, whose world guards are eager selects,
    -- from evaluating it on an @ANY@ bucket.
    wildcardTolerant (WPoint p c) = WChoice (IRUnaryOp OpIsAny p) WFull (WPoint p c)
    wildcardTolerant s = s
    isScalar TFloat = True
    isScalar TInt = True
    isScalar _ = False

-- | Combine the canonical (outcome-True, outcome-False) worlds of a
-- Bool-valued node against the actual target: True-worlds apply when the
-- target requires True, False-worlds when it requires False -- exactly
-- 'comparisonWorlds's original inline construction, now shared with the
-- boolean-connective cases of 'invertToWorlds'.
--
-- A literal polarity target -- the canonical targets 'invertBoolToWorlds'
-- inverts an @if@'s condition at -- selects its side statically. The other
-- side's worlds used to be kept behind a guard that is always False, and
-- they were still compiled: every arm factor of an @if@ nested under a draw
-- was built twice per level (task slow-fuzz-seed-findings-2026-10-06).
boolWorlds :: WSet -> [WWorld] -> [WWorld] -> [WWorld]
boolWorlds (WPoint (IRConst (VBool b)) _) ts fs = if b then ts else fs
boolWorlds target ts fs =
     map (addGuard (memberGuard TBool constTrueIR target)) ts
  ++ map (addGuard (memberGuard TBool (IRConst (VBool False)) target)) fs

-- | (worlds where @e@ observes True, worlds where it observes False), for a
-- Bool-valued node reached while inverting a boolean connective. Reuses
-- 'invertToWorlds' itself at each canonical polarity target -- the same
-- device the 'IfThenElse' case above already uses to invert its own
-- condition.
invertBoolToWorlds :: CompilerMetadata -> [ChainName] -> Expr -> CompilerMonad (Maybe ([WWorld], [WWorld]))
invertBoolToWorlds meta occs e = do
  wsT <- invertToWorlds meta occs e (WPoint constTrueIR const1)
  wsF <- invertToWorlds meta occs e (WPoint (IRConst (VBool False)) const1)
  return ((,) <$> wsT <*> wsF)

-- | Worlds of a comparison node: the side carrying the bound variable is
-- confined to a half-line whose direction depends on the observed boolean;
-- the other side must be deterministic.
comparisonWorlds :: CompilerMetadata -> [ChainName] -> Bool -> Expr -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
comparisonWorlds meta occs isGT lop rop target
  | subtreeHasOcc occs lop && not (subtreeHasOcc occs rop) && pType (getTypeInfo rop) == Deterministic = do
      b <- toIRGenerate meta rop
      splitOn lop b False
  | subtreeHasOcc occs rop && not (subtreeHasOcc occs lop) && pType (getTypeInfo lop) == Deterministic = do
      b <- toIRGenerate meta lop
      splitOn rop b True
  | otherwise = return Nothing
  where
    -- With the bound-variable side on the LEFT of `<`, True means side < bound;
    -- each of `>` and the side being on the right flips the direction.
    --
    -- Every interval is closed, @[lo, hi]@ (see 'boundGuards' and
    -- 'measureSet'), so a strict comparison on an Int side moves its bound one
    -- step inward: @side < b@ True is @[-inf, b - 1]@ and False @[b, inf]@,
    -- @side > b@ True is @[b + 1, inf]@ and False @[-inf, b]@. The bound has
    -- the side's type (@lt@/@gt@ are @a -> a -> Bool@), and the monotone
    -- transport onto the bound variable keeps an Int side Int with integer
    -- endpoints (its Int steps are @plusI@/@negI@ only). A continuous side
    -- keeps @b@ on both halves: the boundary point has measure zero, and the
    -- non-strict guards answer a boundary query with the density (task
    -- set-witness-int-comparison-boundary-non-strict).
    splitOn side b flipped = do
      let discrete = rType (getTypeInfo side) == TInt
          step op = if discrete then IROp op b (IRConst (VInt 1)) else b
          -- (side below b, side at or above b) and (side at or below b, side above b)
          ltT = WInterval WNegInf (WFinite (step OpSub))
          ltF = WInterval (WFinite b) WPosInf
          gtT = WInterval (WFinite (step OpPlus)) WPosInf
          gtF = WInterval WNegInf (WFinite b)
      let (setT, setF) = if isGT /= flipped then (gtT, gtF) else (ltT, ltF)
      wsT <- invertToWorlds meta occs side setT
      wsF <- invertToWorlds meta occs side setF
      return (boolWorlds target <$> wsT <*> wsF)

-- | The constraint set a transported witness value stands for. Normally the
-- point itself; but a seeded @==@ or constructor-test inverse observed on its
-- False polarity yields the 'VAnyExcept' sentinel -- bare, or still inside the
-- 'IRIf' on the observed Bool that selects it ('anyExceptSampleShape') -- and
-- that is the complement of a point, not a point, so it becomes a 'WExcept'
-- (a runtime 'WChoice' where the polarity is still an 'IRIf'). Its peeled
-- bindings are re-wrapped around every piece that may read them.
witnessSet :: IRExpr -> IRExpr -> WSet
witnessSet value cov = case anyExceptSampleShape value of
  Nothing -> WPoint value cov
  Just (binds, shape) ->
    let wrap = generateLetInExpr binds
    in case shape of
      Left ex -> WExcept WFull (wrap ex)
      Right (IRConst (VBool b), isPosAny, non, ex)
        | b == isPosAny -> WExcept WFull (wrap ex)
        | otherwise     -> WPoint (wrap non) cov
      -- The polarity is the observed Bool, which a marginal query can leave
      -- as the wildcard: it then constrains nothing, and branching on it was
      -- the interpreter's "Condition is not a boolean: VAny" (@draw v =
      -- Normal in if Uniform < 0.5 then (0.0, v == 1.0) else (1.0, True)@ at
      -- @(0.0, ANY)@; task slow-fuzz-seed-findings-2026-10-06).
      Right (cond, isPosAny, non, ex) ->
        let exceptSide = WExcept WFull (wrap ex)
            pointSide  = WPoint (wrap non) cov
            byPolarity = if isPosAny then WChoice (wrap cond) exceptSide pointSide
                                     else WChoice (wrap cond) pointSide exceptSide
        in WChoice (IRUnaryOp OpIsAny (wrap cond)) WFull byPolarity

-- | Worlds of an @==@ node against a deterministic operand @other@ (value
-- @b@), the bound variable reaching @side@ through at least one inverse step.
-- The True outcome is @side@ observed at the point @b@, inverted onto the
-- bound variable like any point target -- the witness @x_b@, its
-- applicability guard @g@ (is @b@ in @side@'s image at all?) and its
-- change-of-variables factor. The False outcome is the complement of that
-- point, transported as a complement rather than as a point: where @g@ holds
-- it is "any value but @x_b@" -- @'WExcept' 'WFull' x_b@ on the bound variable
-- itself, measured as the marginal minus the excepted point (so a continuous
-- variable answers mass 1, a discrete one @1 - p(x_b)@) -- and where @g@
-- fails no value of the bound variable produces @b@, so the False outcome is
-- certain ('WFull'). The complement therefore never meets a forward
-- function's inverse. Mirrors the
-- plan engine's 'contEqWorlds', whose False outcome is likewise the full
-- world minus the point.
--
-- The complement is only taken of a single plain point world: a residue
-- factor or a split into several worlds would need the complement of a
-- product or a union, which this does not attempt (answering Nothing, the
-- engine's refusal, rather than a wrong number).
equalityWorlds :: CompilerMetadata -> [ChainName] -> Expr -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
equalityWorlds meta occs side other target = do
  b <- toIRGenerate meta other
  complementWorlds meta occs side b target

-- | The worlds of a test "@side@ is the point @b@" observed at @target@: the
-- True outcome inverts @side@ at @b@, the False one is that point world's
-- complement ('equalityWorlds', which states the rule). @b@ may hold field
-- wildcards (a constructor test's @C ANY ..@), and the excepted mass is then
-- the marginal mass of the pattern.
complementWorlds :: CompilerMetadata -> [ChainName] -> Expr -> IRExpr -> WSet -> CompilerMonad (Maybe [WWorld])
complementWorlds meta occs side b target = do
  wsT <- invertToWorlds meta occs side (WPoint b const1)
  return $ case wsT of
    -- A transport that may read a wildcard target ('transportDirect') wraps
    -- its point in that runtime choice; @b@ is a deterministic value, not a
    -- query's wildcard, so the point is what it constrains.
    Just ts@[WWorld gs set []] | Just xb <- plainPoint set ->
      -- nested 'IRIf', not 'OpAnd': a guard protects the ones after it
      let g = foldr (\gd acc -> IRIf gd acc constFalseIR) constTrueIR gs
          fs = [ WWorld [g] (WExcept WFull xb) []
               , WWorld [notIR g] WFull [] ]
      in Just (boolWorlds target ts fs)
    _ -> Nothing
  where
    plainPoint (WPoint xb _) = Just xb
    plainPoint (WChoice _ WFull (WPoint xb _)) = Just xb
    plainPoint _ = Nothing

-- | The free variables of a subtree that name an ENCLOSING random binding --
-- the one way the factorization's independence assumption can be violated,
-- and the reason this check exists rather than a comment asserting it cannot
-- happen.
--
-- 'subtreeHasOcc' establishes that a subtree does not mention the plan-bound
-- variable. That makes it independent of the PLAN, whose randomness is the
-- neural net's alone. It does not by itself make two such subtrees
-- independent of EACH OTHER, and the world measure multiplies their factors.
-- Fresh 'Normal'/'Uniform' leaves and calls to top-level stochastic functions
-- are per-occurrence draws, so two occurrences never share; the only shared
-- random source reachable from inside the traversal is a variable bound by an
-- enclosing @let@, which SPLL's @let@ makes a single draw shared by every
-- occurrence (design let-binding-semantics: the existing @let@ is the eager
-- form, @Apply (Lambda x body) expr@). The traversal cannot descend INTO such
-- a let itself -- 'planResolveApply's 'collectApply' declines a Lambda callee,
-- and 'classifyArg' declines a non-deterministic argument -- but a let
-- enclosing the whole plan-bound binding puts its variable in scope here.
--
-- A variable is flagged when it is a local binding of the ambient scope
-- (@typeEnv@ marks top-level functions with True; 'Normal'/'Uniform' are
-- absent from it entirely) and its occurrence is not 'Deterministic' given
-- scope. Variables bound INSIDE the subtree are not in the ambient scope and
-- so are not flagged -- correctly, since the sub-compile is one
-- 'toIRInference' call that models their sharing itself. A recovered witness
-- variable is deterministic by 'reinferRecovered' and excluded twice over.
--
-- The check is deliberately LOCAL and conservative: it refuses any factor
-- carrying such a variable, rather than tracking which factors end up
-- multiplied into the same world. A shared source between two factors is the
-- actual unsoundness, but that relation depends on how worlds combine, which
-- is exactly the thing a future change could alter silently. Refusing at the
-- factor keeps the guarantee local to this function. Nothing in the corpus is
-- refused by it (see 'planFreeStochastic*'), and the shape it protects is
-- independently unreachable today.
--
-- Takes the ambient scope and the recovered-witness list rather than a whole
-- 'CompilerMetadata' so that it is directly testable: the hazard it guards is
-- unreachable end-to-end today (every enclosing random binding of the shapes
-- tried is refused by the outer engine first), so a white-box test is the only
-- way to pin its behaviour. See 'planFactorExternalsTests' in TestInternals.
planFactorExternals :: TypeEnv -> [String] -> Expr -> [String]
planFactorExternals env recovered = nub . go
  where
    go e = self e ++ concatMap go (getSubExprs e)
    self (Expr ti (Var n))
      | Just (_, False) <- lookup n env
      , n `notElem` recovered
      , pType ti /= Deterministic = [n]
    self _ = []
