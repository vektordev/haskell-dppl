-- | The probability and integrate variants' translator, 'toIRInference', and
-- the knot ('knot') that hands it and 'toIRGenerate' to the engine modules.
module SPLL.IRCompiler.Inference (
  toIRInferenceSave,
  toIRInference,
  knot
) where

import SPLL.ReservedNames (topKCutoffParamName)
import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Analysis (isEnumerable, enumerableDomain)
import SPLL.Typing.PType
import Data.Maybe
import Data.List ((\\), find)
import Data.Functor ((<&>))
import SPLL.Typing.ForwardChaining
import SPLL.Semiring
import Control.Monad (foldM, when)
import Control.Monad.Except (catchError)
import qualified Data.Set as Set
import SPLL.IRCompiler.Monad hiding (toIRInference, toIRInferenceSave)
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Materialize
import SPLL.IRCompiler.Gaussian
import SPLL.IRCompiler.Dispatch
import SPLL.IRCompiler.Enumerate
import qualified SPLL.IRCompiler.Generate as Generate (toIRGenerate)

-- | Whether a condition weight is exactly the semiring zero, the test an
-- 'IfThenElse' arm guard reads. Both semirings compare exactly (linear 0.0,
-- log-space negative infinity), as 'addP' does: a condition probability below
-- 'floatApproxEqThresh' (1e-10 in the interpreter, 1e-9 in pythonLib's
-- isclose) is a possible arm, not a dead one, so an approximate test dropped
-- its mass as impossible (task if-condition-approx-zero-drops-tiny-branch-mass).
-- In log space an approximate test would also be wrong the other way:
-- @(-inf) - (-inf)@ is NaN, so two impossible operands compare "not equal",
-- i.e. live -- the wrong direction for a guard whose job is to skip an arm
-- that may hold a nonterminating call.
deadWeightIR :: Semiring -> IRExpr -> IRExpr
deadWeightIR sr c = IROp OpEq c (srZero sr)

-- | The (True, False) weights of a Bool @if@ condition, compiled in one pass
-- (task map-semiring-complement-and-cdf-wrong).
--
-- A condition that is itself a Bool @if c then a else b@ is built from its
-- children's pairs, each child compiled once:
--
-- > pT = cT (x) aT (+) cF (x) bT
-- > pF = cT (x) aF (+) cF (x) bF
--
-- so its False weight is the semiring's own combine over the False
-- derivations. Deriving it as @1 - pT@ instead is a probability-conservation
-- identity: right under sum-product, wrong under max-product, where it is
-- @1 - max@ rather than the best False derivation. A @not@ swaps the pair.
-- Compile cost stays linear in nesting depth -- compiling the condition at
-- each polarity separately would double it per level, the O(2^d) blowup of
-- fuzz-qc-compiler-bugs item 3.
--
-- Each arm's pair is bound once, under the arm guard the 'IfThenElse' case
-- applies to its own arms: the arm's weight is not the semiring zero, and
-- under topK the accumulated path probability through it reaches the cutoff.
-- A pruned arm contributes the semiring zero to both weights, so both are
-- lower bounds, which is what lets the condition be compiled pruned.
--
-- Any other condition is a leaf of this recursion. Under a semiring that
-- conserves probability ('srConserves'), or when the leaf has a single
-- derivation ('singleDerivation': a comparison of one distribution leaf
-- against a bound, say), it is compiled at True, unpruned, and
-- its False weight is the complement in the semiring's sense ('mixWith' of
-- 'srComplement', so a True outcome that is a density leaves the whole unit
-- mass at dim 0 on the False side; task
-- sampling-matches-pdf-continuous-equality-density). Under one that does not,
-- the leaf is compiled at each polarity: the complement of a combined weight
-- (an @a || b@, a call) is not the other side's weight there. That doubles
-- only the leaf's own compile, and only under max-product.
condWeights :: CompilerMetadata -> Expr -> CompilerMonad (PResult, PResult)
condWeights meta (Expr _ (InjF (Named "not") [c])) = (\(t, f) -> (f, t)) <$> condWeights meta c
condWeights meta (Expr _ (IfThenElse c a b)) = do
  let sr = semiringOf meta
  (cT, cF) <- condWeights meta c
  cTV <- shareWeight "condpairT" cT
  cFV <- shareWeight "condpairF" cF
  (aT, aF) <- armPair cTV a
  (bT, bF) <- armPair cFV b
  let bc x y = IROp OpPlus (IRIf (deadWeightIR sr (unP (rProb cTV))) const0 (rBranches x))
                           (IRIf (deadWeightIR sr (unP (rProb cFV))) const0 (rBranches y))
  t <- mixP sr (bc aT bT) (weigh cTV aT) (weigh cFV bT)
  f <- mixP sr (bc aF bF) (weigh cTV aF) (weigh cFV bF)
  return (t, f)
  where
    sr' = semiringOf meta
    weigh w arm = onBranches (const (rBranches arm)) (prodP sr' w arm)
    shareWeight tag r = do
      v <- mkVariable tag
      setVariables [(v, packResult r)]
      return (unpackResult v)
    armPair w arm = do
      let accArm = srTimes sr' (accProb meta) (unP (rProb w))
          pruneGuard = case topKThreshold (compilerConfig meta) of
            Just _  -> [notIR (IROp OpLessThan accArm (IRVar topKCutoffParamName))]
            Nothing -> []
          guards = notIR (deadWeightIR sr' (unP (rProb w))) : pruneGuard
      armO <- scoped ((\(t, f) -> [t, f]) <$> condWeights meta { accProb = accArm } arm)
      -- Each weight is read once, by one of the two mixtures above.
      closed <- closeResults sr' "condpair_arm" guards armO
      case closed of
        [t, f] -> return (t, f)
        _ -> error "condWeights: closeResults returned other than two results"
condWeights meta c
  | srConserves sr || singleDerivation c = do
      t <- toIRInference (unpruned meta) False c (IRConst (VBool True))
      f <- mixWith (\_ p -> srComplement sr p) const0 (mass (srOne sr)) t
      return (t, f)
  | otherwise = (,) <$> toIRInference meta False c (IRConst (VBool True))
                    <*> toIRInference meta False c (IRConst (VBool False))
  where sr = semiringOf meta

-- | Whether every value of a random expression has at most one derivation (one
-- control-flow path producing it), so that 'srComplement' of its CDF is its
-- upper tail under every semiring, max-product included: a distribution
-- leaf, a Gaussian closed form, or an InjF that transforms one such operand
-- with deterministic ones. Conservative: anything else (an @if@, an
-- enumerated sum of two random operands, a call, a let) answers False.
singleDerivation :: Expr -> Bool
singleDerivation (Expr ti nd)
  | pType ti `elem` [Deterministic, PNormal, PLogNormal] = True
  | otherwise = case nd of
      Var "Uniform" -> True
      Var "Normal"  -> True
      InjF _ ps -> case filter (\x -> pType (getTypeInfo x) /= Deterministic) ps of
        [r] -> singleDerivation r
        _   -> False
      _ -> False


-- | The inverse body and applicability test to invert a bound through, in
-- the given mode. A point query takes the declaration's own. A cumulative one
-- through an exact integer quotient ('roundedQuotientInverse') takes the
-- rounded bound instead -- the floor where the inverse is increasing, the
-- ceiling where it is decreasing (@v * (-6) <= -7@ is @v >= ceil(7/6) = 2@) --
-- under a guard that no longer demands divisibility, which made every
-- non-multiple bound "impossible" (task cdf-through-discrete-inverse-wrong).
modeInverse :: Bool -> FDecl -> IRExpr -> (IRExpr, IRExpr)
modeInverse cumulative decl deriv
  | cumulative, Just (floorB, ceilB, app) <- roundedQuotientInverse decl =
      (IRIf (IROp OpGreaterThan deriv const0) floorB ceilB, app)
  | otherwise = (body decl, applicability decl)

toIRInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
toIRInferenceSave meta cumulative (Expr t (Lambda name subExpr)) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- scoped (toIRInferenceSave newMeta cumulative subExpr sample) <&> generateLetInBlock meta
  return (detP (IRLambda name irTuple))
toIRInferenceSave meta cumulative expr sample = do
  o <- scoped (toIRInference meta cumulative expr sample)
  anySafeShared (semiringOf meta) sample o

-- | Does every value of this type necessarily contribute dimension 0 -- i.e.
-- is it discrete through and through?
--
-- This exists to bound the branch pruning in the field-constructor equation
-- (task recursive-list-prob-missed-cse). Pruning a field that an earlier field
-- has already ruled out means not evaluating it, which means its dimension
-- contribution is reported as 0 rather than whatever it would have been. That
-- is only safe when the two are the same number.
--
-- It has to be a TYPE-level test, and it is genuinely not possible to do
-- better by inspecting the compiled field: a recursive call's 'rDim' is a
-- projection off the call's own result ('IRDestruct AcFst (IRDestruct AcSnd
-- (IRVar "l_9_guarded"))'), so reading the true dimension requires performing
-- exactly the recursion the pruning exists to avoid. Dimension and pruning are
-- mutually exclusive for any field that can carry a continuous payload, which
-- is why this predicate is the boundary rather than something cleverer.
--
-- The convention it protects is pinned by 'test/cases/data-structures/
-- tupleRoundtrip.tst': @p((0.5, 2.5))=(0.0, 2.0)@ -- an out-of-support query
-- against a tuple of two continuous fields still reports dimension 2, not 0.
-- Dimensionality there is a property of the branch, not of the query point.
-- ('mixWith' is the opposite case and needs no protection: it discards an
-- impossible side's dimension outright before comparing.)
--
-- Conservative in both directions that matter: an unknown, open or
-- not-yet-resolved type answers 'False' (no pruning, current behaviour), and a
-- recursive ADT terminates via @seen@ rather than being assumed either way.
dimZeroByType :: [ADTDecl] -> RType -> Bool
dimZeroByType decls = go []
  where
    go seen ty = case ty of
      TBool        -> True
      TInt         -> True
      TSymbol      -> True
      TUnit        -> True
      NullList     -> True
      ListOf t     -> go seen t
      TTensor _ t  -> go seen t
      Tuple a b    -> go seen a && go seen b
      TEither a b  -> go seen a && go seen b
      -- A recursive ADT is dimension-0 as long as no reachable field is
      -- continuous; revisiting a name already on the stack adds no new
      -- field types, so it answers 'True' and lets the other arms decide.
      TADT n
        | n `elem` seen -> True
        | otherwise     -> case find ((== n) . dataName) decls of
            Nothing -> False
            Just d  -> all (go (n : seen) . snd) (concatMap snd (constructors d))
      -- TFloat, TVarR (may be instantiated continuous), TThetaTree, TArrow,
      -- BottomTuple, GreaterType, NotSetYet.
      _            -> False

toIRInference :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
--toIRInference meta cumulative expr sample | trace (show expr) False = undefined
-- A witnessed sample can itself be the 'VAnyExcept' placeholder an '==' (or ADT
-- constructor-test) inverse produces on its False branch ("any value other
-- than this one") -- either bare, or still wrapped in the 'IRIf' that selects
-- it. 'transportDirect' used to produce exactly this shape when it probed the
-- True/False polarity of a comparison the witnessed variable occurs in, and
-- handed it on as a point; it now turns it into a 'WExcept' set instead
-- ('witnessSet'), whose bare-complement measure is this same split. The
-- clause stays for any other producer of a sentinel-valued sample reaching
-- the bound distribution's own inference, rather than through the InjF-probability
-- 'hasAnyExcept' combinator below (which only fires when the comparison
-- itself, not some downstream consumer of its witness, is the thing being
-- queried). Arithmetic on the sentinel -- a density's '(sample - mu)/sigma',
-- say -- is undefined: 'VAnyExcept' names a set, not a point. Previously that
-- reached 'IROptimizer.forceOp' and the interpreter's own operator evaluator
-- as a raw operand and crashed both (task set-witness-eq-o2-optimizer-crash).
-- Splitting here, generically over whichever leaf is being inferred (Normal,
-- Uniform, a user function, ...), mirrors the split the direct InjF case
-- performs: the ANY-branch mass minus the excepted point's own mass/density.
-- A hole: the masked leaf of a pruned observation (design
-- witnessed-per-query-capability, task per-mask-variants-by-pruning;
-- 'SPLL.ObservationMask.pruneObservation'). It is the unit factor -- mass one,
-- dim 0, possible, no branch -- and it never reads the sample: the slot it
-- replaced is the one the query masked, so whatever value the dispatcher handed
-- this variant there is not an observation. First, so no clause below (the
-- equality guard of an ordinary 'Constant', the Boolean CDF split) gets to
-- compare against it. 'Constant VAny' cannot occur in a user program
-- ('SPLL.Validator' forbids it), so this fires on holes only.
toIRInference meta _ (Expr _ (Constant VAny)) _ = return (detP (srOne (semiringOf meta)))
toIRInference meta cumulative e sample
  | Just (binds, shape) <- anyExceptSampleShape sample = do
  -- 'binds' are 'sample's own leading let-bindings (e.g. 'transportDirect's
  -- materialised anchors), stripped off to see the shape beneath. Registering
  -- them via 'setVariables' -- the same mechanism the InjF 'hasAnyExcept'
  -- combinator below uses for its own seeded variables -- rather than
  -- rewrapping the result afterwards keeps them properly threaded through
  -- 'guardedSubInference'/'closeResult's own let-hoisting, which floats a
  -- sub-result's binding to a scope a post-hoc rewrap would sit below.
  setVariables binds
  -- Both operands of the subtraction are compiled 'unpruned': a pruned
  -- excepted mass would inflate the difference, and a pruned marginal could
  -- drive it negative.
  let metaSub = unpruned meta
  case shape of
    Left ex ->
      exceptMeasure meta ex (anyMarginal metaSub cumulative e) (toIRInferenceSave metaSub cumulative e ex)
    Right (cond, isPosAny, nonAnyExpr, exceptExpr) -> do
      let subGuard = if isPosAny then cond else notIR cond
      let nonGuard = notIR subGuard
      nonAnyRes <- guardedSubInference meta [nonGuard] (toIRInference meta cumulative e nonAnyExpr)
      subRes <- exceptMeasure meta exceptExpr (anyMarginal metaSub cumulative e)
                  (guardedSubInference metaSub [subGuard] (toIRInference metaSub cumulative e exceptExpr))
      let ifSample a na = if isPosAny then IRIf cond a na else IRIf cond na a
      return (zipResult ifSample subRes nonAnyRes)
-- CDFs on Booleans make little sense. We define that False < True. Therefor cdf(True) = 1 and cdf(False) = pdf(False)
toIRInference meta True expr sample | rType (getTypeInfo expr) == TBool = do
  false <- toIRInference meta False expr (IRConst (VBool False))
  -- cdf(True) = 1 is always attainable; cdf(False) inherits the False case.
  return (mkPResult (sealP (IRIf sample (srOne (semiringOf meta)) (unP (rProb false)))) dim0 (rBranches false)
                  (IRIf sample constFalseIR (rImposs false)))
-- A node whose certificate is a point mass of known value ('lawPoint'): the
-- value is compared against the sample, as for a literal 'Constant'. This is
-- the zero rule of @mult(0, y)@ read off the law (task
-- mult-inversion-unguarded-at-zero, design law-carrying-modality §E): the
-- product is never inverted through a division by its zero factor, and a
-- zero bound by a @draw@ or a value set {0} counts as the literal does. It
-- also measures @draw z = Normal in 0.0 * z@ at its point, whose binding
-- nothing reads the value of.
toIRInference meta cumulative e@(Expr TypeInfo {rType=rt} _) sample
  | Just v <- lawPoint meta e =
      if cumulative
        then return (mass (compareValueExpr (semiringOf meta) rt (IRConst (valueToIR v)) sample))
        else return (indicatorP (semiringOf meta) (equalityGuard rt (IRConst (valueToIR v)) sample))
-- A conjunction of clauses over enumerable draws whose clauses share the draws
-- in a cycle: variable elimination over the draws ('ConstraintNet'), instead
-- of the nested joint enumeration the stack would otherwise get.
toIRInference meta False e sample
  | Just net <- constraintNet meta e = compileConstraintNet meta net sample
-- The Gaussian catch-all: a PNormal node whose codegen law is a leaf or an
-- affine form ('gaussianLeaf') is one Gaussian density, from the (mu, sigma)
-- its law's builder gives ('gaussianParams').
toIRInference meta False e sample | pType (getTypeInfo e) == PNormal, Just g <- gaussianLeaf meta e = do
  (mu, sigma0) <- gaussianParams meta g e
  degenerateScaleGuard meta False TFloat mu sigma0 sample $ \sigma ->
    density (scaledNormalDensity (semiringOf meta) (IROp OpDiv (IROp OpSub sample mu) sigma) [sigma]) sample
toIRInference meta True e sample | pType (getTypeInfo e) == PNormal, Just g <- gaussianLeaf meta e = do
  (mu, sigma0) <- gaussianParams meta g e
  degenerateScaleGuard meta True TFloat mu sigma0 sample $ \sigma ->
    mass (distCumulative (semiringOf meta) IRNormal (IROp OpDiv (IROp OpSub sample mu) sigma))
-- The lognormal catch-all, gated structurally ('logNormalExtractable').
toIRInference meta False e sample | pType (getTypeInfo e) == PLogNormal, logNormalExtractable meta e = do
  (mu, sigma0) <- toIRLogNormalParams meta e
  let sr = semiringOf meta
  let positive = IROp OpGreaterThan sample const0
  let negativeGuard x = IRIf positive x (srZero sr)
  -- A degenerate scale is a point mass at exp(mu), which is positive, so the
  -- support guard below stays right around it.
  r <- degenerateScaleGuard meta False TFloat (IRUnaryOp OpExp mu) sigma0 sample $ \sigma ->
    let correctedSample = IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma
    in density (scaledNormalDensity sr correctedSample [sigma, sample]) sample
  -- A non-positive sample is outside the lognormal's support: impossible, not
  -- merely unlikely. Support boundaries are the one way a *density* leaf can be
  -- a structural zero, and they are known statically here.
  return (impossibleWhen (notIR positive) (onProb negativeGuard r))
toIRInference meta True e sample | pType (getTypeInfo e) == PLogNormal, logNormalExtractable meta e = do
  (mu, sigma0) <- toIRLogNormalParams meta e
  let sr = semiringOf meta
  let positive = IROp OpGreaterThan sample const0
  let negativeGuard x = IRIf positive x (srZero sr)
  r <- degenerateScaleGuard meta True TFloat (IRUnaryOp OpExp mu) sigma0 sample $ \sigma ->
    mass (distCumulative sr IRNormal (IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma))
  return (impossibleWhen (notIR positive) (onProb negativeGuard r))
-- Distribution primitives (reserved-name Vars). Normal usually reaches the PNormal
-- catch-all above; these equations are the direct density/CDF leaves for Uniform and
-- the defensive Normal fallback.
toIRInference meta False (Expr _ (Var "Normal")) sample = return (density (distDensity (semiringOf meta) IRNormal sample) sample)
-- Unlike Normal, Uniform has bounded support: off it the density is not a tiny
-- tail value but an impossible event, and saying so structurally is what keeps
-- 'mixWith' from having to read it back off the zero.
toIRInference meta False (Expr _ (Var "Uniform")) sample =
  return (impossibleWhen (outsideUnitInterval sample) (density (distDensity (semiringOf meta) IRUniform sample) sample))
toIRInference meta True (Expr _ (Var "Normal")) sample = return (mass (distCumulative (semiringOf meta) IRNormal sample))
toIRInference meta True (Expr _ (Var "Uniform")) sample = return (mass (distCumulative (semiringOf meta) IRUniform sample))
toIRInference _ _ (Expr _ (Constant (VError e))) _ = return (detP (IRError e))
toIRInference meta False (Expr TypeInfo {rType=rt} (Constant value)) sample = do
  let comp = equalityGuard rt (IRConst (fmap failConversion value)) sample
  return (indicatorP (semiringOf meta) comp)
toIRInference meta True (Expr TypeInfo {rType=rt} (Constant value)) sample = return (mass (compareValueExpr (semiringOf meta) rt (IRConst (valueToIR value)) sample))
toIRInference meta True (Expr _ (ThetaI a i)) sample = do
  a' <- toIRGenerate meta a
  return (mass (IRIf (IROp OpLessThan sample (IRDestruct (AcTheta i) a')) (srZero (semiringOf meta)) (srOne (semiringOf meta))))
toIRInference meta False (Expr _ (ThetaI a i)) sample = do
  a' <- toIRGenerate meta a
  return (indicatorP (semiringOf meta) (IROp OpApprox sample (IRDestruct (AcTheta i) a')))
-- A negated condition is the un-negated one with the arms swapped. The
-- equation below derives the False weight as the complement of the True
-- weight, and that complement cannot carry a null-set convention: the True
-- weight of @not (Normal == 0.5)@ is the mass 1, whose complement is the mass
-- 0, so the density convention of the equality's True outcome (task
-- sampling-matches-pdf-continuous-equality-density) was lost and the if-flip
-- of @if Normal == 0.5 then 1 else 2@ answered p(1) impossible. Swapping
-- measures the condition at the polarity that carries the density directly
-- (task null-set-conventions-not-preserved-under-negation).
toIRInference meta cumulative (Expr ti (IfThenElse (Expr _ (InjF (Named "not") [cond])) left right)) sample =
  toIRInference meta cumulative (Expr ti (IfThenElse cond right left)) sample
toIRInference meta cumulative (Expr _ (IfThenElse cond left right)) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  -- 'cond' is TBool, so its weights are the two sides of a partition. Both
  -- come from one pass over the condition ('condWeights'): a condition that is
  -- itself a Bool if (or a not of one) is built from its children's own
  -- pairs, so its False weight is the semiring's combine over its False
  -- derivations, and a leaf condition derives its False weight as the
  -- semiring complement of its True weight where that is sound. Compiling
  -- the condition once per polarity instead doubled the work at every
  -- nesting level (fuzz-qc-compiler-bugs item 3: an O(2^d) compile of a
  -- depth-d chain of nested Bool conditions); deriving every False weight as
  -- @1 - p(True)@ was linear but holds only under sum-product, and gave
  -- max-product @1 - max@ for a nested condition (task
  -- map-semiring-complement-and-cdf-wrong). rDim is carried over from each
  -- weight. A leaf's False weight is "certain minus p(cond=True)" in the
  -- semiring's sense ('mixWith' of 'srComplement'), not a bare 1 - p: when the
  -- True outcome is itself a density -- a continuous @x == c@, a null event
  -- reported at dim > 0 -- the False branch carries the whole unit mass at dim
  -- 0 (task sampling-matches-pdf-continuous-equality-density). The pair
  -- nodes' weights are lower bounds under topK, so the condition is compiled
  -- pruned; only the complemented leaves compile 'unpruned'.
  let sr = semiringOf meta
  (condTrue, condFalseMix) <- condWeights meta cond
  let condTrueExpr  = unP (rProb condTrue)
  let condFalseExpr = unP (rProb condFalseMix)
  -- Every later read of a condition weight reads its binding: the raw
  -- 'condTrueExpr' is the condition's whole probability field, and the arm
  -- guards and branch-count checks below read it three to four times (task
  -- presult-unbound-block-copied-per-field).
  let condTrueV  = IRVar var_condT_p
      condFalseV = IRVar var_condF_p
  let condFalse = mkPResult (sealP condFalseExpr) (rDim condFalseMix) const0
                          (IROp OpEq condFalseV (srZero sr))
  setVariables [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]

  -- The arm is weighted by the condition's probability -- an independent factor,
  -- so 'prodP'. The branch count is the exception to the product rule: both arms
  -- share ONE condition, so its count is added once, below, and each arm carries
  -- only its own count through the product.
  let weighByCond v condRes armRes =
        onBranches (const (rBranches armRes))
          (prodP sr (mkPResult (sealP (IRVar v)) (rDim condRes) const0 (rImposs condRes)) armRes)
  -- Whether the condition's own probability is exactly the semiring zero
  -- ('deadWeightIR'). Comparing against the literal 0.0 here would
  -- falsely treat every log-space arm as live (a log probability is
  -- essentially never exactly 0.0).
  let deadArm = deadWeightIR sr
  let liveArm = notIR . deadArm
  -- Each arm is zero-checked with the same IRIf short-circuit the probability
  -- fields use, so a dead arm's count -- and any recursive call inside it --
  -- is never evaluated. That is what makes a recursive program's branch count
  -- terminate at all (task bc-recursive-prob-divergence).
  let zeroCheckBC c bc = IRIf (deadArm c) const0 bc

  let rt = rType (getTypeInfo left)
  case rt of
    -- Arrow-typed arms: each arm's compiled 'rProb' is itself a CLOSURE (see
    -- the 'Lambda' equation two cases up -- 'detP (IRLambda name irTuple)'),
    -- not a scalar, so weighing it by the condition's probability ('prodP')
    -- or summing the two arms ('mixP') is arithmetic on a function value --
    -- exactly the crash task arrow-lifted-mixture-for-function-values exists
    -- to fix ("Mult can only multiply numbers ...: VClosure"). Lift the
    -- combinators pointwise instead of applying them to the closures
    -- directly: mix(p_c, t, g) == \z -> mix(p_c, unpack(t z), unpack(g z)).
    -- Build a NEW closure over a fresh argument 'z' whose body, once applied,
    -- reduces to the ordinary scalar mixture of each arm's own
    -- (prob, dim, bc, imposs) AT that point -- ordinary, because opening a
    -- closure at one concrete 'z' always yields a plain value's PResult (a
    -- still-arrow-typed result, i.e. a curried multi-argument mixture,
    -- recurses through this very equation the next time IT is combined --
    -- not handled here; see task callee-normalize-curried-and-accessor-gaps
    -- and the arrow-lift task's own declined-scope note).
    --
    -- topK pruning is NOT implemented for this path: the pruned selection
    -- above picks among three PRE-COMPUTED packed alternatives, and here the
    -- "alternative" only exists once applied to an argument that isn't known
    -- yet. Always computing the exact (unpruned) mixture is a strict
    -- refinement of what topK would have approximated -- never a regression
    -- from the pre-fix behaviour of crashing outright -- so 'thr' is simply
    -- not consulted on this branch.
    TArrow _ _ -> do
      let metaTrue  = meta { accProb = srTimes sr (accProb meta) (IRVar var_condT_p) }
      let metaFalse = meta { accProb = srTimes sr (accProb meta) (IRVar var_condF_p) }
      trueClosure  <- toIRInference metaTrue  cumulative left  sample
      falseClosure <- toIRInference metaFalse cumulative right sample
      zVar <- mkVariable "argZ"
      closureBody <- scoped (do
        trueCallV  <- mkVariable "armTcall"
        falseCallV <- mkVariable "armFcall"
        let trueBind  = (trueCallV,  IRApply (unP (rProb trueClosure))  (IRVar zVar))
            falseBind = (falseCallV, IRApply (unP (rProb falseClosure)) (IRVar zVar))
        -- Let-bind each arm's application ONCE (mirroring the ReadNN/curried-
        -- call-spine idiom elsewhere in this module) rather than calling
        -- 'unpackResult' directly on the raw 'IRApply': that destructures its
        -- argument into four separate projections, which would otherwise
        -- inline four copies of a call that may itself be an arbitrarily
        -- expensive (or recursive) sub-inference. 'closeResult' places the
        -- binding inside the dead-arm guard below, so a call whose condition
        -- cannot hold is still never evaluated.
        trueAtZ  <- closeResult sr "armTz" [liveArm condTrueV]  (openWith [trueBind]  (unpackResult trueCallV))
        falseAtZ <- closeResult sr "armFz" [liveArm condFalseV] (openWith [falseBind] (unpackResult falseCallV))
        let weighedTrue  = weighByCond var_condT_p condTrue  trueAtZ
            weighedFalse = weighByCond var_condF_p condFalse falseAtZ
            branchesZ = IROp OpPlus (zeroCheckBC condTrueV  (rBranches weighedTrue))
                                    (zeroCheckBC condFalseV (rBranches weighedFalse))
        mixP sr branchesZ weighedTrue weighedFalse) <&> generateLetInBlock meta
      return (detP (IRLambda zVar closureBody))
    _ -> do
      -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
      let thr = topKThreshold (compilerConfig meta)
      -- We need to restart the monad stack, because variables inside the branches may not be valid outside
      -- E.g. if length(a) > 0 then a[0] else ...
      -- If we were to access a[0] outside of the branch we would error
      mul1Raw <- scoped (do
        let metaTrue = meta { accProb = srTimes sr (accProb meta) (IRVar var_condT_p) }
        weighByCond var_condT_p condTrue <$> toIRInference metaTrue cumulative left sample)
      mul2Raw <- scoped (do
        let metaFalse = meta { accProb = srTimes sr (accProb meta) (IRVar var_condF_p) }
        weighByCond var_condF_p condFalse <$> toIRInference metaFalse cumulative right sample)
      -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
      -- A condition that cannot hold makes its arm an impossible event, which is
      -- exactly what the mixture below needs to know to drop it -- so record it
      -- rather than leaving the zeroed product to be recognised numerically.
      -- The check is the arm block's guard (see 'closeResult'), so an arm whose
      -- condition cannot hold is never evaluated -- it may hold the recursive call
      -- the check exists to skip.
      mul1Zeroed <- closeResult sr "armT" [liveArm condTrueV] mul1Raw
      mul2Zeroed <- closeResult sr "armF" [liveArm condFalseV] mul2Raw
      let leftBranchesExpr  = rBranches mul1Zeroed
      let rightBranchesExpr = rBranches mul2Zeroed
      -- Dispatching is free: a node that delegates to sub-computations contributes
      -- no branch of its own, so the count is the sum of whichever arms were
      -- actually alive -- no term for evaluating the condition, and no -1 wash.
      -- (The previous formula, cond + left + right - 1, telescoped to left + right
      -- only because every condition tested so far happened to be leaf-shaped with
      -- its own count of exactly 1; a compound condition -- a nested if, a call --
      -- inflated the parent by its dispatch cost for no principled reason. Every
      -- other combinator here -- the enumerated sum, toIREnumerate, the topK dispatch --
      -- already sums surviving children and adds nothing for dispatching.)
      let branches = IROp OpPlus (zeroCheckBC condTrueV  leftBranchesExpr)
                                 (zeroCheckBC condFalseV rightBranchesExpr)
      addRes <- mixP sr branches mul1Zeroed mul2Zeroed
      case thr of
        Just _ -> do
          -- Pick among the three whole packed results ONCE, bound to a single
          -- variable, rather than wrapping each of the four PResult fields in
          -- its own copy of the accTrue/accFalse IRIf (the previous shape):
          -- that field-wise wrapping is exactly the duplication pattern
          -- 'closeResult' exists to avoid (see its docs) -- here it wasn't
          -- routed through closeResult at all, so it re-embedded mul1Zeroed's/
          -- mul2Zeroed's/addRes's own fields FOUR times per level. Since this
          -- whole 'IfThenElse' case can itself be 'cond' of an enclosing
          -- topK-guarded IfThenElse, that 4x-per-level duplication compounds
          -- with nesting depth into an exponential blowup independent of (and
          -- compounding on top of) the condTrue/condFalse fix above
          -- (fuzz-qc-compiler-bugs item 3: nested topK-guarded conditions timed
          -- out well before the plain default-config case did).
          accTrueV <- mkVariable "accTrue"
          accFalseV <- mkVariable "accFalse"
          setVariables [(accTrueV, srTimes sr (accProb meta) (IRVar var_condT_p))]
          setVariables [(accFalseV, srTimes sr (accProb meta) (IRVar var_condF_p))]
          prunedV <- mkVariable "pruned"
          let prunedExpr = IRIf
                (IROp OpLessThan (IRVar accTrueV) (IRVar topKCutoffParamName))
                (packResult mul2Zeroed)
                (IRIf (IROp OpLessThan (IRVar accFalseV) (IRVar topKCutoffParamName))
                  (packResult mul1Zeroed)
                  (packResult addRes))
          setVariables [(prunedV, prunedExpr)]
          return (unpackResult prunedV)
        -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
        Nothing -> return addRes
-- A comparison against a deterministic bound under a semiring that does not
-- conserve probability ('srConserves', max-product): the fixed-bound
-- equations below answer the upper tail as the complement of the operand's
-- CDF, which is the upper tail's weight only when that CDF is a single
-- derivation's ('singleDerivation'). An operand with several derivations
-- (an enumerated sum, an @if@) has a CDF that is already their combine, and
-- @1 - max@ is not the best derivation above the bound (task
-- map-semiring-complement-and-cdf-wrong: @a + b > 0@ over two Bernoulli(0.5)
-- indicators answered 0.75 for the best derivation's 0.25). Such an operand
-- is summed over its enumerated domain instead, in the compile's semiring,
--
--   p(cmp = sample) = (+) over v in dom(X) of p(X = v) (x) [cmp(v, bound) = sample]
--
-- and refused when it has no domain within the materialization budget.
toIRInference meta False (Expr _ (InjF (Named cmp) [left, right])) sample
  | cmp `elem` ["gt", "lt"]
  , not (srConserves (semiringOf meta))
  , [randE] <- filter (\x -> pType (getTypeInfo x) /= Deterministic) [left, right]
  , not (singleDerivation randE) = do
    let sr = semiringOf meta
        randLeft = pType (getTypeInfo right) == Deterministic
        detE = if randLeft then right else left
        rtgs = tags (getTypeInfo randE)
    case enumerableDomain rtgs of
      Just dom | enumerationWithinMaterializationBudget meta rtgs -> do
        bnd <- mkVariable "cmp_bound"
        d <- toIRGenerate meta detE
        setVariables [(bnd, d)]
        v <- mkVariable "cmp_value"
        mTbl <- materializeOperandTable meta randE
        let op = if cmp == "gt" then OpGreaterThan else OpLessThan
            holds = if randLeft then IROp op (IRVar v) (IRVar bnd) else IROp op (IRVar bnd) (IRVar v)
        summandO <- scoped $ do
          pV <- operandProb meta mTbl randE (IRVar v)
          return (IRIf (equalityGuard TBool holds sample) pV (srZero sr))
        let (outerBinds, body') = hoistInvariantBindings v (closeExpr summandO id)
        setVariables outerBinds
        opaqueMass sr (enumSumNode sr v dom body') const0
      _ -> refuse (chainName (getTypeInfo randE))
             ("a comparison's upper tail under a semiring without complements (max-product) "
              ++ "needs an operand with a single derivation or a finite enumerated domain")
-- Both sides Gaussian: left - right ~ Normal(muL - muR, sqrt(sL^2 + sR^2)), so the
-- comparison is that difference's CDF evaluated at 0. Neither side is Deterministic,
-- so the bound-based equations below do not apply. resolveCompCons types this Bool
-- as Integrate (a closed-form discrete probability), matching the dim-0 result here.
toIRInference meta False (Expr _ (InjF (Named "gt") [left, right])) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    normalDiffComparison meta False left right sample
toIRInference meta False (Expr _ (InjF (Named "lt") [left, right])) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    normalDiffComparison meta True left right sample
toIRInference meta False (Expr _ (InjF (Named "gt") [left, right])) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const > var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    bound <- strictBelowBound right l
    setVariables [(var, bound)]
    integ <- toIRInference (unpruned meta) True right (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) (notIR sample) (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    integ <- toIRInference (unpruned meta) True left (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) sample (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
toIRInference meta False (Expr _ (InjF (Named "lt") [left, right])) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    integ <- toIRInference (unpruned meta) True right (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) sample (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var < const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    bound <- strictBelowBound left r
    setVariables [(var, bound)]
    integ <- toIRInference (unpruned meta) True left (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) (notIR sample) (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
-- A comparison against a random but enumerable bound (task
-- uniform-below-random-threshold-no-forward): a Bernoulli whose rate is
-- itself random, @Uniform < (if b then 0.9 else 0.1)@ once DrawSinking has
-- moved @draw b@ into the threshold. Neither side is Deterministic, so the
-- two equations above do not apply, and the other side has no
-- 'DiscreteValues' domain, so the enumerate-both grid does not either. The
-- operands are independent ('enumeratedBoundShape'), so
--
--   p(cmp = sample) = sum over v in dom(E) of P(E = v) * p(cmp against v = sample)
--
-- where the inner factor is exactly the fixed-bound equation's: the other
-- side's CDF at @v@, complemented when the outcome asks for its upper tail.
-- ModalityInfer's 'compareGround' admits this shape under the same
-- conditions, and this equation must not outrun it.
toIRInference meta False (Expr _ (InjF (Named cmp) [left, right])) sample
  | cmp `elem` ["gt", "lt"]
  , Just (enumLeft, enumE, cdfE) <- enumeratedBoundShape meta left right = do
    let sr = semiringOf meta
    let enumList = head [x | DiscreteValues x <- tags (getTypeInfo enumE)]
    -- The CDF side lies below the bound when it is the left operand of @<@
    -- or the right operand of @>@; the True outcome is then its CDF, and
    -- the False outcome the complement (and the other way round otherwise).
    let cdfBelow = (cmp == "lt") /= enumLeft
    -- The CDF side is complemented below: under max-product only a single
    -- derivation's CDF has its complement as its upper tail (see the
    -- non-conserving fixed-bound equation above).
    when (not (srConserves sr) && not (singleDerivation cdfE)) $
      refuse (chainName (getTypeInfo cdfE))
        ("a comparison's upper tail under a semiring without complements (max-product) "
         ++ "needs an operand with a single derivation")
    bnd <- mkVariable "enumerated_bound"
    mTbl <- materializeOperandTable meta enumE
    returnO <- scoped $ do
      pE <- operandProb meta mTbl enumE (IRVar bnd)
      cdfAt <- if cdfBelow then strictBelowBound cdfE (IRVar bnd) else return (IRVar bnd)
      integ <- toIRInference (unpruned meta) True cdfE cdfAt  -- complemented below, see 'unpruned'
      pCmp <- complementWhen sr (if cdfBelow then notIR sample else sample) (unP (rProb integ))
      return (srTimes sr pE pCmp)
    let (outerBinds, body') = hoistInvariantBindings bnd (closeExpr returnO id)
    setVariables outerBinds
    opaqueMass sr (enumSumNode sr bnd enumList body') const0
-- The run-time twin of the Dirac-law clause ('lawPoint') (task
-- helper-parameter-zero-factor-answers-nan): a deterministic factor that is
-- not statically known nonzero -- a helper's parameter, say -- can still be
-- zero when the product runs, and then the product is the same point mass,
-- while the inversion below divides by it (its applicability guard found every
-- value impossible). Branch on it: the point mass when it is zero, and the
-- ordinary compile, recorded in 'zeroGuardedProducts' so it does not branch
-- again, otherwise. A Gaussian product never gets here: the PNormal clause
-- above compiles it, and 'degenerateScaleGuard' handles its zero scale.
toIRInference meta cumulative e@(Expr TypeInfo {rType=rt, chainName=cn} (InjF (Named name) [left, right])) sample
  | name `elem` ["mult", "multI"]
  , Just factor <- runtimeZeroFactor left right
  , not (cn `Set.member` zeroGuardedProducts meta) = do
      f <- toIRGenerate meta factor
      v <- mkVariable "factor"
      setVariables [(v, f)]
      let sr = semiringOf meta
          zero = IRConst (valueToIR (zeroValueOf rt))
          isZero = IROp OpEq (IRVar v) zero
          dirac | cumulative = mass (compareValueExpr sr rt zero sample)
                | otherwise  = indicatorP sr (equalityGuard rt zero sample)
          meta' = meta { zeroGuardedProducts = Set.insert cn (zeroGuardedProducts meta) }
      rest <- guardedSubInference meta [notIR isZero] (toIRInference meta' cumulative e sample)
      return (zipResult (IRIf isZero) dirac rest)
-- The CDF of a neural read (task neural-int-read-cdf-returns-pmf). The
-- network's _auto_prob is a point mass, so the cumulative query sums it over
-- the read's enumerated domain, each value weighted by whether it lies at or
-- below the sample ('compareValueExpr'):
--
--   P(X <= x) = sum over v in dom(X) of P(X = v) * [v <= x]
--
-- in the compile's semiring. The point clause below used to answer both
-- queries, returning P(X = x). A read with a continuous leaf has no such sum
-- and is refused; a bare Bool read never gets here (the Boolean CDF split
-- above), nor does a Gaussian-headed one ('gaussianLeaf').
toIRInference meta True e@(Expr TypeInfo {rType=rt, tags=tgs, chainName=cn} (ReadNN name _)) sample =
  case enumerableDomain tgs of
    Just dom | enumerationWithinMaterializationBudget meta tgs -> do
      let sr = semiringOf meta
      v <- mkVariable "nn_cdf_value"
      summandO <- scoped $ do
        pV <- (unP . rProb) <$> toIRInference meta False e (IRVar v)
        return (srTimes sr pV (compareValueExpr sr rt (IRVar v) sample))
      let (outerBinds, body') = hoistInvariantBindings v (closeExpr summandO id)
      setVariables outerBinds
      opaqueMass sr (enumSumNode sr v dom body') const0
    _ -> refuse cn ("cannot compute the cumulative distribution of the neural read '" ++ name
                    ++ "': its domain is not a finite enumeration within the materialization budget")
toIRInference meta _ (Expr _ (ReadNN name symbol)) sample = do
  nnRaw <- mkVariable "nn_raw"
  var <- mkVariable "callNN"
  sym <- toIRGenerate meta symbol
  setVariables [(nnRaw, IRApply (IRVar name) sym)]
  setVariables [(var, IRApply (IRApply (IRVar (name ++ "_auto_prob")) (IRVar nnRaw)) sample)]
  -- Not a leaf: the network's own _auto_prob function already packed a triple.
  return (unpackResult var)
toIRInference meta cumulative (Expr t (Lambda name subExpr)) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- scoped (toIRInference newMeta cumulative subExpr sample) <&> generateLetInBlock meta
  return (detP (IRLambda name irTuple))
-- Deterministic lambda and bound expression PDF
toIRInference meta False (Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ ->
      -- A leaf resolution: a deterministically-known value compared against the
      -- sample, exactly as the 'Constant'/'ThetaI' cases do, so it counts as one
      -- branch like they do ('indicatorP', not 'detP' -- which is reserved for
      -- results that produce no value at all, i.e. closures). See the leaf-anchor
      -- note on the 'Var'-is-a-local-variable case below.
      --
      -- Compared by 'equalityGuard', as every other deterministic leaf is: a
      -- bare 'OpEq' compared a float leaf bit-exactly and read a nested ANY
      -- (@(3.0, (ANY, 2.0))@ against @draw z = (1.0, 2.0) in (3.0, z)@) as a
      -- mismatch. Rare while a @draw@ over a recovered variable kept its
      -- stale random type; common once re-inference types it Deterministic
      -- (task reinfer-body-under-recovered-bindings). Bound once, since the
      -- guard reads the value per field.
      do
        applied <- mkVariable "det_app"
        return (indicatorP (semiringOf meta)
                  (IRLetIn applied (IRApply lIR vIR) (equalityGuard rt (IRVar applied) sample)))
-- Deterministic lambda and bound expression CDF
toIRInference meta True (Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ ->
      return (mass (compareValueExpr (semiringOf meta) rt (IRApply lIR vIR) sample))
-- Enumerable conditional lambda applied to a probabilistic discrete argument:
-- enumerate the argument's discrete support and weight each value by its probability,
-- compiling the body via toIREnumerate. The body need not be deterministic given the
-- bound variable -- toIREnumerate recurses into further enumerable applications
-- (nested enumerable `let`s), so this rule no longer requires `pType l == Deterministic`.
-- Gated on the materialization budget (task of-annotation-forces-dense-enumeration):
-- this arm materializes the argument's whole support, and it is the FIRST matching
-- 'Apply' equation, so an `of` annotation alone used to force dense enumeration and
-- make the plan-guided lazy path below unreachable -- a 423x pessimization on an
-- otherwise identical program. The budget that already bounds Tier-0 marginal
-- materialization now bounds this too; over budget, the equation declines and
-- dispatch falls through to the plan-guided arm ('planWitnessApply'), which
-- factorizes over the 'PartitionPlan' slots without ever materializing the support.
-- Under budget nothing changes: every program the suite already routes here still
-- routes here, so this is strictly a refusal to blow up, not a reordering.
-- Since every read is tagged with its resolved annotation, written or not (task
-- of-annotation-and-auto-derived-enumeration-divergence), this order -- dense
-- first, plan above the budget -- holds for every neural read alike.
-- A stack of enumerable draws over a field constructor whose operands fall
-- into independent groups: the product of the groups' own enumerations
-- ('drawStack'), instead of one joint loop over every draw.
toIRInference meta cumulative e@(Expr _ (Apply _ _)) sample
  | Just ds <- drawStack meta e = factoredDrawStack meta cumulative ds sample
toIRInference meta cumulative (Expr TypeInfo {rType=_} (Apply l v)) sample
  | isEnumerableApplication meta l v
  , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
  , calleeBodyInScope meta l =
  -- The agreement fusion (task categorical-product-ov-fusion) is tried first
  -- and answers 'Nothing' for everything it does not recognise or will not
  -- take, so the ordinary joint enumeration stays the default path.
  case agreementShape meta l v of
    Just ag -> enumerateAgreement meta cumulative ag sample
    Nothing -> enumerateAppliedLambda meta cumulative l v sample
-- A conditional top-level function applied, through a curried spine, to
-- deterministic leading arguments and a probabilistic enumerable last one:
-- @match c (readAttrs s)@ with @c@ fixed. Marginalise the last argument
-- exactly as the one-argument equation above does ('enumerateCurriedArgument').
-- The leading arguments are read with the enclosing enumerated latents fixed,
-- which is what makes the shared-latent spelling
-- @draw c = readQ q in match c (readAttrs s1) ++ match c (readAttrs s2)@
-- compile per slot inside the loop over @c@ (task
-- shared-enumerated-latent-loses-per-slot-factorization).
toIRInference meta cumulative (Expr ti (Apply l v)) sample
  | Just l' <- curriedEnumerableCallee meta l v
  , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v)) =
  enumerateCurriedArgument meta cumulative (\x -> Expr ti (Apply l' x)) v sample
-- Deterministic curried call spine rooted at a known top-level function: build
-- the WHOLE application (the query sample, plus every source-level argument)
-- as one contiguous 'IRApply' chain and let-bind it exactly once, instead of
-- recursing per 'Apply' node -- which is what the general "Deterministic
-- bound expression" case below does, and which let-binds the callee's partial
-- application (awaiting the remaining curried arguments) *before* applying
-- the rest of the spine to it.
--
-- That per-level split is invisible at the default -O, where the let-inliner
-- collapses the single-use intermediate bindings back into one spine before
-- codegen ever sees it. At -O0 nothing does, so codegen is handed
-- @let c0 = f_prob(sample) in c0(x)@: a *contiguous* 'IRApply' spine is what
-- the scalar backends flatten into one @f_prob(sample, x)@ call site
-- ('IROptimizer.unconditionalAnns' states the same invariant, from the CSE
-- side, for why it refuses to hoist a partial spine), and a spine broken
-- across a let is exactly what that flattening cannot see through. Julia
-- calls a partial application as if it were the fully-applied one-argument
-- function and gets an arity 'MethodError'; Python would raise 'TypeError'
-- for the same reason (task
-- curried-call-spine-needs-optimizer-to-typecheck).
--
-- Guarded to the shapes this can handle soundly: every argument in the spine
-- must be Deterministic (a probabilistic argument needs inversion machinery,
-- handled by the existing per-argument cases below, which this equation
-- leaves untouched since its guard then fails), and the spine's head must be
-- a bare reference to a top-level function -- matching exactly the case the
-- 'Var' equation further down would otherwise have let-bound as the spine's
-- first, innermost partial call.
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt} (Apply _ _)) sample
  | (Expr _ (Var n), args@(_:_)) <- flattenApplySpine expr
  , all ((== Deterministic) . pType . getTypeInfo) args
  , Just (TArrow _ _, hasInference) <- lookup n (typeEnv meta) = do
      argIRs <- mapM (toIRGenerate meta) args
      name <- if hasInference then calleeInferenceName meta cumulative n else return n
      let base = if hasInference
            then inferenceCall meta cumulative (IRVar name) sample
            else IRApply (IRVar name) sample
      let wholeCall = foldl IRApply base argIRs
      case rt of
        TArrow _ _ -> return (detP wholeCall)
        _ -> do
          retVal <- mkVariable "call"
          setVariables [(retVal, wholeCall)]
          return (unpackResult retVal)
-- A dead binding of a function value: the body never reads it, so it is
-- compiled alone, exactly as the scalar arm below does at its own
-- 'deadBindingBodyCN' check. The arms next would generate the argument (the
-- deterministic one) or the whole callee (the random one): @draw f = snd
-- (Normal, \x -> Uniform) in (\x -> Uniform) c@ -- CalleeNormalize's rewrite
-- of a projected callee, leaving @f@ unread -- generated the discarded Normal,
-- and the probability was refused as generate-backed
-- (fuzz-admission-oracle-bugs item 2).
toIRInference meta cumulative (Expr _ (Apply l v)) sample
  | isTArrowType (rType (getTypeInfo v))
  , Just deadBody <- deadBindingBody meta l =
  toIRInference meta cumulative deadBody sample
-- Deterministic bound expression
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo v) == Deterministic = do
  let viaCallee = do
        vIR <- toIRGenerate meta v
        lIR <- (unP . rProb) <$> toIRInference meta cumulative l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
        let applied = IRApply lIR vIR
        -- The result is not a tuple if the return value is a closure
        case rt of
          TArrow _ _ -> return (detP applied)
          _ -> do
            retVal <- mkVariable "call"
            setVariables [(retVal, applied)]
            return (unpackResult retVal)
  -- A call whose earlier argument is random, @obs b p@ with @b@ random: the
  -- callee applied to its leading arguments is a closure whose body reads a
  -- parameter bound to a random argument, which the arms compiling @l@ alone
  -- refuse. Where they do, that argument is bound first, in parameter order
  -- ('leadingArgBinding'), as for a random last argument. Tried second, so a
  -- call they answer keeps its emitted code.
  leading <- if cumulative then return Nothing else leadingArgBinding meta expr
  let viaBinding = case leading of
        Nothing -> viaCallee
        Just b -> do
          first <- (Right <$> scoped viaCallee) `catchError` (return . Left)
          case first of
            Right o -> inline o
            Left _ -> applyBinding meta cumulative rt b sample
  -- The call's one random argument, in a leading position and enumerable
  -- (@cont (trans fog) n@), is marginalised over its domain as a random last
  -- argument is ('enumerateCurriedArgument'), where the arms above refuse:
  -- the binding engines none enumerate a finite domain, so which refusal a
  -- call met depended on where its author put the random parameter (task
  -- random-leading-argument-into-recursion-refused). Tried last, so a call
  -- they answer keeps its emitted code; where all refuse, the enumeration's
  -- own refusal is the one reported. Not for the cumulative variant, which
  -- the binding path does not take either: there it would admit integrate
  -- variants that were absent before (corpus observePredicateParameterLambda),
  -- which batched mode cannot tensorize. Both restrictions work around
  -- symptoms and are not design choices. The engine order now depends on the
  -- argument's position, and nested leading calls compile in exponential time
  -- through these retries. Docs-repo tasks
  -- leading-argument-enumeration-as-binding-engine and
  -- nested-leading-random-argument-compile-exponential.
  case leadingEnumerableArgument meta expr of
    Just (mkBody, ai) | not cumulative
                      , enumerationWithinMaterializationBudget meta (tags (getTypeInfo ai)) -> do
      first <- (Right <$> scoped viaBinding) `catchError` (return . Left)
      case first of
        Right o -> inline o
        Left _ -> enumerateCurriedArgument meta False mkBody ai sample
    _ -> viaBinding
-- Probabilistic bound expression
toIRInference meta cumulative (Expr TypeInfo{rType=rt, chainName=_} (Apply l v)) sample | isTArrowType (rType (getTypeInfo v)) && (pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal) = do
  lIR <- toIRGenerate meta l
  vIR <- (unP . rProb) <$> toIRInference meta cumulative v sample
  -- The result is not a tuple if the return value is a closure, as in the
  -- deterministic arms above: @app g x@ with @g@ random reaches here as
  -- @(app g) x@, and @app g@ is a function still awaiting @x@. Unpacking it
  -- projected @fst@ out of a closure (task
  -- named-hof-random-function-argument-miscompiled); the enclosing
  -- application applies it and unpacks the PResult it then returns.
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ -> do
      applied <- mkVariable "call"
      setVariables [(applied, IRApply lIR vIR)]
      return (unpackResult applied)
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt, chainName=_} (Apply l v)) sample | pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal = do
  -- This is the probabilistic inference of a known, deterministic lambda with a probabilistic parameter
  -- The inference looks like this: p(l(v) == sample) = p(l^-1(sample) == v)
  -- The inverse can not be created using recursive descend, therefor we use forward chaining for the inverse only
  -- Chain name of the callable
  let lChainName = chainName (getTypeInfo l)

  -- This logic is here to wrap the expression back into lambdas if the lambda we look at returns a lambda
  -- A callee forward chaining cannot resolve to a lambda is a shape this arm
  -- does not support, not a broken invariant: CalleeNormalize reduces the
  -- selections it knows (projections, an @if@, a redex), and anything it does
  -- not reach is refused rather than crashing the compile.
  case findEquivalentExpression (fcData meta) lChainName of
    Just (_, LambdaInfo{}, _) -> return ()
    other -> refuse lChainName ("the callee of this application does not resolve to a lambda the compiler can see"
                                ++ " (it resolved to " ++ show other ++ "); a function value selected some other way"
                                ++ " than by a projection, an if, or a redex is not supported here")
  let binding0 = resolveBinding meta l v

  -- Dead binding: if the bound variable never appears in the body, the body is independent
  -- of the argument. In that case p(result = sample) = p(body = sample).
  -- Scoped to THIS lambda's body: a same-named variable bound elsewhere must not count.
  -- 'deadBindingBodyCN' is the shared predicate; the Bottom-argument arm below asks it
  -- too, so a dead binding compiles the same way whether or not its argument happens
  -- to have a measurable distribution. It returns this very 'lambdaBodyCN' -- both
  -- resolve l's chain name through 'findEquivalentExpression'.
  let deadBinding = isJust (deadBindingBodyCN meta l)
  if deadBinding then
    toIRInference (withBindingLaw meta binding0 (bindVar binding0)) cumulative (bindBody binding0) sample
  else do
   -- A call whose body reads a leading parameter bound to a random argument
   -- binds that argument first ('leadingArgBinding').
   leading <- if isJust (bindScope binding0) then return Nothing else leadingArgBinding meta expr
   case leading of
     Just _ | cumulative -> refuse lChainName ("cannot compute a cumulative distribution through a call of '"
                 ++ fromMaybe "?" (bindTopLevel binding0) ++ "' binding more than one random argument:"
                 ++ " the slots they reach are correlated, and their joint CDF is not a product of per-slot factors")
     _ -> applyBinding meta cumulative rt (fromMaybe binding0 leading) sample

-- Dead binding over an *intractable* argument. The arms above all require the
-- argument's own pType to be one the compiler can measure (Deterministic, or one
-- of the three probabilistic rungs); a `Bottom` argument matches none of them and
-- used to reach the catch-all below. But a dead binding never reads the value, so
-- the argument's tractability is beside the point: p(result = sample) =
-- p(body = sample), exactly the reduction the probabilistic arm makes at its own
-- `deadBinding` check -- and the same predicate ('deadBindingBodyCN') decides it, so
-- the two agree on branch counts as well as on probability. This is what makes
-- `let x = Uniform * Uniform in Uniform` compile: the binding is unmeasurable and
-- unread, and ModalityInfer types the application by the *body*, so the program as
-- a whole is not Bottom and does get a probability function.
toIRInference meta cumulative (Expr TypeInfo{rType=_} (Apply l _)) sample
  | Just bodyExpr <- deadBindingBody meta l =
  toIRInference meta cumulative bodyExpr sample
-- What is left is an application whose argument has no measurable distribution and
-- whose value the body actually reads. There is no probability to compute: the
-- correct answer would be an integral over the argument's law, which is precisely
-- what `Bottom` says is unavailable. Reaching here is normally impossible --
-- a live occurrence of a Bottom-typed binding makes the body, hence the
-- application, Bottom too, and ModalityInfer then emits no probability function
-- at all -- so this is a diagnostic for a modality/codegen disagreement rather
-- than a user-facing refusal.
toIRInference _ cumulative (Expr TypeInfo{rType=rt, chainName=cnApp} (Apply l v)) _ =
  refuse cnApp ("Cannot compile an application in " ++ (if cumulative then "cumulative" else "probability")
    ++ " mode: the argument has pType " ++ show (pType (getTypeInfo v))
    ++ " (no measurable distribution) and the callee (pType "
    ++ show (pType (getTypeInfo l)) ++ ", chain name '" ++ chainName (getTypeInfo l)
    ++ "') reads its value. Result type: " ++ show rt)
-- Generic inference for multi-field constructor InjFs (Cons, TCons, user-ADT
-- constructors). Each field is independently recoverable from the constructed
-- sample via a deconstructing inverse, so we infer each field against its
-- recovered sub-sample and combine: probabilities multiply, dimensions add,
-- branch counts add. The components are independent, hence product (not the
-- additive PlusConstraint) semantics. Fires for >= 1 probabilistic parameter;
-- the all-deterministic case is handled by the generate-and-compare branch below.
toIRInference meta cumulative (Expr TypeInfo{rType=rt} (InjF (Named name) params)) sample
  | isFieldConstructor (adtDecls meta) name && countProbParams params >= 1 = do
  let resolvedName = resolveInjF rt name
  let localAdts = adtDecls meta
  FPair fwd inversions <- instantiate mkVariable localAdts resolvedName
  let inVars = inputVars fwd
  let outV = soleOutputVar fwd
  -- Inline the sample directly into each inverse body (instead of binding it to
  -- outV) so the optimizer can fold deconstructions like head(prepend(s, ANY))
  -- back to s. A let-binding referenced by every field plus the guard would
  -- survive optimization and force materialising the reconstructed container.
  let inlineSample = irMap (\e -> case e of IRVar n | n == outV -> sample; _ -> e)
  -- Fields are compiled LEFT TO RIGHT rather than independently, threading the
  -- disjunction of the impossibility flags established so far, so that a field
  -- whose predecessors have already ruled this construction out is never
  -- evaluated (task recursive-list-prob-missed-cse, second half). The product
  -- below is impossible as soon as any one factor is ('prodP' ORs the flags),
  -- so a later factor's value cannot affect the answer once an earlier one has
  -- set its flag -- but 'prodP' is an arithmetic combination of already-computed
  -- results, so without this the later factor is computed regardless and only
  -- then multiplied into a product known to be impossible.
  --
  -- This matters exactly where a cheap discriminating field precedes an
  -- expensive one, which is the shape of every branching recursive list: an
  -- 'A : rec' / 'B : rec' mixture compiles each arm as (head indicator, tail
  -- recursion), and the head indicator rules its arm out for all but one
  -- symbol. Unpruned, BOTH arms recurse at every level, doubling the work per
  -- element -- measured at exactly 2.0x/element, i.e. 2^n in list length, on
  -- 'rec = if Uniform < 0.5 then [] else (if Uniform < 0.5 then A : rec else
  -- B : rec)'. This is NOT the duplicate-evaluation bug the first half of that
  -- task fixed (that was one call emitted twice); here the two recursive calls
  -- are distinct and each emitted once, just not pruned by a sample that has
  -- already ruled one out.
  --
  -- The guard is threaded through 'guardedSubInference' -- the same mechanism
  -- the applicability test already uses -- so it is baked INTO the bound value
  -- by 'closeResult' rather than applied to the returned 'PResult' afterwards.
  -- That is what makes it prune rather than merely zero: a shared let-in block
  -- is evaluated where it is bound, so a guard layered on top of the result
  -- would come too late to stop the recursion.
  --
  -- 'rImposs' is taken AFTER guarding, so it already carries this field's own
  -- applicability test and prune guard; a field is thus pruned if any
  -- predecessor was impossible for any reason, not only an indicator mismatch.
  -- An all-constant accumulator adds no guard at all, which is what keeps
  -- cumulative mode untouched: its deterministic fields are 'mass'es with no
  -- impossibility flag, so nothing ever accumulates there.
  let pruneGuards fieldType accImposs
        | accImposs == constFalseIR        = []
        | not (dimZeroByType localAdts fieldType) = []
        | otherwise                        = [notIR accImposs]
  (revFieldResults, _) <- foldM
    (\(acc, accImposs) (inV, p) -> do
      let inv = inversionFor resolvedName inV inversions
      let FDecl {body=invBody, applicability=appT, deconstructing=decons} = inv
      -- Deconstructing inverses need the Any-safe inference variant.
      let probF = if decons then toIRInferenceSave else toIRInference
      let appTExpr = inlineSample appT
      -- A field can be a self-recursive probability call -- the tail of a
      -- recursive list, e.g. 'main = if Uniform>p then [] else X:main'
      -- compiles its tail field exactly here -- so this field's own
      -- computation is isolated and re-guarded on its own applicability test
      -- rather than left in the ambient scope (see 'guardedSubInference').
      fieldRes <- guardedSubInference meta
                    (appTExpr : pruneGuards (rType (getTypeInfo p)) accImposs)
                    (probF meta cumulative p (inlineSample invBody))
      -- Bind the accumulator: an inline field's flag already contains
      -- 'accImposs' (through its prune guard), so the unbound OR would hold
      -- it twice and N fields would copy the first flag 2^N times. Binding
      -- eagerly is safe -- each flag carries its own applicability test, and
      -- the product evaluates every field's flag anyway.
      accV <- case orIR accImposs (rImposs fieldRes) of
        c@(IRConst _) -> return c
        v@(IRVar _)   -> return v
        e             -> do
          accName <- mkVariable "acc_imposs"
          setVariables [(accName, e)]
          return (IRVar accName)
      return ((fieldRes, appTExpr) : acc, accV))
    ([], constFalseIR) (zip inVars params)
  let fieldResults = reverse revFieldResults
  -- The fields are independent, so the whole construction is their product.
  let combined = foldl1 (prodP (semiringOf meta)) (map fst fieldResults)
  -- Guard the result by the conjunction of all field applicability tests (e.g.
  -- the non-empty-list test carried by the Cons inverses).
  let guardCond = foldr1 (IROp OpAnd) (map snd fieldResults)
  return (guardP (semiringOf meta) [guardCond] combined)
toIRInference meta cumulative (Expr ti (InjF (Named name) params)) sample | isHigherOrder (adtDecls meta) name = do
  let localAdts = adtDecls meta
  let resolvedName = resolveInjF (rType ti) name
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable localAdts resolvedName
  -- Unary InjF has a single inversion
  inv <- case fPair of
        FPair _ [i] -> return i
        FPair _ is -> refuse (chainName ti) ("Higher-order InjF '" ++ resolvedName ++ "' must declare exactly one inversion, but declares " ++ show (length is))
  let FDecl {inputVars=inVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=derivs} = inv
  --Handle the function being in different positions of the signature
  let aPoss = [0 .. (length params - 1)] \\ getFunctionParamIdx localAdts name
  aPos <- case aPoss of
        [n] -> return n
        x -> refuse (chainName ti) ("Higher-order InjF '" ++ resolvedName ++ "' expects exactly one non-function parameter, but got " ++ show (length x))
  let a = params !! aPos
  let aVar = inVars !! aPos
  let fs = map (params !!) (getFunctionParamIdx localAdts name)
  let fVars = map (inVars !!) (getFunctionParamIdx localAdts name)
  let invDerivExpr = inverseDerivative resolvedName aVar derivs
  -- Set sample value to the variable name in the InjF
  setVariables [(aVar, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Create all inverses of the ho functions and save them on the variable stack
  -- Then create a substitution that substitutes f^-1 to f_prob. All substitutions are then composed in the fold
  renVar <- foldM (\sub tup -> createHOInverse meta tup <&> (.) sub) id (zip fVars fs)
  -- When deconstructing an Either and sample contains a nested VAny (e.g. Left ANY),
  -- arithmetic in invExpr would crash before isAny can fire. Replace invExpr with a
  -- safe alternative (Left VAny / Right VAny) that lets OpEq handle the comparison.
  let renamedInvExpr = renVar invExpr
  let finalInvExpr = case (decons, rType (getTypeInfo a)) of
        (True, TEither _ _) ->
          let deepCheck = mkDeepAnyCheck (TEither undefined undefined) sample
          in IRIf deepCheck (mkSafeInvExpr sample) renamedInvExpr
        _ -> renamedInvExpr
  -- Isolated and re-guarded on appTest (see 'guardedSubInference') so a
  -- shared let-in block from inside 'a's own compilation -- e.g. a
  -- self-recursive probability call -- cannot escape into the ambient
  -- scope ahead of the applicability test 'guardP' applies below.
  -- Unpruned when the cumulative CoV below may flip it through a complement.
  let metaOp = covOperandMeta cumulative invDerivExpr meta
  paramRes <- guardedSubInference metaOp [appTest] (probF metaOp cumulative a finalInvExpr)
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  return (substResult renVar (guardP (semiringOf meta) [appTest] (scaleCoV (semiringOf meta) cumulative invDerivExpr paramRes)))
-- A function value computed by an InjF with no probabilistic operand --
-- @head ((\v3 -> [\v4 -> Uniform]) 1.0)@, @left (\r1 -> ..)@ -- would be
-- answered by the two leaf equations below, which generate the value and
-- compare it against the sample. A function is not a value a sample can be
-- compared with: the CDF has no order to integrate along (it reached
-- 'compareValueExpr''s internal-invariant 'error'), and an arrow-typed result
-- is consumed as a probability CLOSURE (the arrow-lifted @if@ mixture, the
-- arrow-typed probabilistic-argument 'Apply' arm), which an equality indicator
-- is not -- and one whose body draws trips the central generate-backed guard,
-- refusing the whole program, generate included. Refused here instead, as an
-- absent variant (task function-value-compared-in-probability-mode).
toIRInference _ _ (Expr TypeInfo {rType=rt, chainName=cn} (InjF (Named name) params)) _
  | containsArrow rt, countProbParams params == 0, allParamsMeasurable params =
  refuse cn ("'" ++ name ++ "' here yields a value containing a function (" ++ show rt ++ "), selected some"
             ++ " other way than by a lambda, an if, or a call the compiler can see through; a function value"
             ++ " is not compared against a query sample, so no probability or cumulative closure can be built for it")
toIRInference meta False e@(Expr TypeInfo {tags=_, rType=rt} (InjF (Named _) params)) sample
  | countProbParams params == 0 && allParamsMeasurable params = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate meta e
  -- Leaf resolution, one branch -- see the leaf-anchor note on the
  -- 'Var'-is-a-local-variable case below.
  return (indicatorP (semiringOf meta) (equalityGuard rt expr sample))
toIRInference meta True e@(Expr TypeInfo {tags=_, rType=rt} (InjF (Named _) params)) sample
  | countProbParams params == 0 && allParamsMeasurable params = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is less than the sample
  expr <- toIRGenerate meta e
  return (mass (compareValueExpr (semiringOf meta) rt expr sample))
-- Exactly one probabilistic operand, as 'theProbIndex' presumes: a
-- comparison of two random operands, or of a deterministic one against an
-- unmeasurable (Bottom) one -- @False == (Uniform > Uniform)@ -- is left to
-- the arms below, and was an uncaught 'error' here (task
-- single-prob-param-injf-with-no-probabilistic-operand).
toIRInference meta cumulative (Expr TypeInfo {tags=_, chainName=cnAE} (InjF (Named name) params)) sample
  | hasAnyExcept (adtDecls meta) name
  , countProbParams params == 1 = do
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) name
  let inVars = inputVars fwd
  let v1 = soleOutputVar fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let probIdx = theProbIndex name params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let invDecl = inversionFor name (inVars !! probIdx) inversions
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  (v1', invPosExpr, invNegExpr) <- case invExpr of
        IRIf (IRVar v) pos neg -> return (v, pos, neg)
        _ -> refuse cnAE ("Form of InjF is not supported, its inverse must be an if on the sample: " ++ name)
  when (v1 /= v1') $ refuse cnAE ("Form of InjF is not supported, sample has to be the condition: " ++ name)
  (isPosAny, nonAnyExpr, exceptExpr) <-
        case (invPosExpr, invNegExpr) of
          (IRConst (VAnyExcept [expt]), non) -> return (True, non, expt)
          (non, IRConst (VAnyExcept [expt])) -> return (False, non, expt)
          _ -> refuse cnAE ("AnyExcept in InjF must be the first expression inside the if: " ++ name)

  -- Find the relevant derivative of the inversion
  let invDeriv = inverseDerivative name v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic
  -- subexpression. Both 'nonAnyRes' and 'exceptRes' are compiled here
  -- unconditionally and only later selected between at runtime by
  -- 'ifSample'/'zipResult' below -- so, mirroring that selection exactly,
  -- each is isolated and re-guarded on the condition under which it is the
  -- one actually read (see 'guardedSubInference'): a shared let-in block
  -- from inside either's own compilation (e.g. a deconstructing inverse
  -- crashing on the untaken arm, or a self-recursive call) must not run
  -- when that arm is not selected.
  let subResGuard = if isPosAny then IRVar v1 else notIR (IRVar v1)
  let nonAnyGuard = notIR subResGuard
  -- The subtraction's operands are compiled 'unpruned' (a pruned excepted
  -- mass inflates the difference); the plain arm only needs that when the
  -- cumulative CoV below may flip it through a complement.
  let metaNon = covOperandMeta cumulative invDeriv meta
  let metaSub = unpruned meta
  nonAnyRes <- guardedSubInference metaNon [nonAnyGuard] (probF metaNon cumulative (params !! probIdx) nonAnyExpr)
  let ifSample a na = if isPosAny then IRIf (IRVar v1) a na else IRIf (IRVar v1) na a
  -- The ANY arm is the marginal minus the excepted value's mass; its branch count
  -- is the excepted value's, not a sum (this is a select between the two arms).
  -- A one-constructor pattern leaves an empty, impossible complement ('exceptMeasure').
  subRes <- exceptMeasure meta exceptExpr (anyMarginal metaSub cumulative (params !! probIdx))
              (guardedSubInference metaSub [subResGuard] (probF metaSub cumulative (params !! probIdx) exceptExpr))
  let ifRes = zipResult ifSample subRes nonAnyRes
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  return (guardP (semiringOf meta) [appTest] (scaleCoV (semiringOf meta) cumulative invDeriv ifRes))
-- Single-operand enumeration for forward-only binary InjFs (and/or) when exactly
-- one operand is deterministic and the other is a single tractable random Bool
-- (Integrate/PNormal/PLogNormal). Forward-only ops (see 'isForwardOnly') declare
-- no inversions, so the generic single-inversion clause below has nothing to
-- invert and crashes with "Non-exhaustive patterns in [invDecl]" on exactly this
-- shape (found by TestFuzz's typed generator, e.g. @(Uniform < 0.4) and True@).
-- Mirrors the two-operand enumerate-both case further down: the deterministic
-- side doesn't depend on the enum variable, so it's evaluated once outside the
-- loop; the random side's own (already-tractable) enum is then looped, keeping
-- cells where forward(l,r) == sample.
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isForwardOnly (adtDecls meta) (resolveInjF rt name)
    && (pType (getTypeInfo left) == Deterministic || pType (getTypeInfo right) == Deterministic)
    && countProbParams [left, right] == 1
    && isEnumerable (tags (getTypeInfo (if pType (getTypeInfo left) == Deterministic then right else left))) = do
  let resolvedName = resolveInjF rt name
  let leftDet = pType (getTypeInfo left) == Deterministic
  let (detExprSrc, randExprSrc) = if leftDet then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo randExprSrc)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  let sr = semiringOf meta
  mTblRand <- materializeOperandTable meta randExprSrc
  returnO <- scoped $ do
    pRand <- operandProb meta mTblRand randExprSrc (IRVar randVar)
    return (IRIf (IROp OpEq f sample) pRand (srZero sr))
  let (outerBinds, body') = hoistInvariantBindings randVar (closeExpr returnO id)
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr randVar enumList body') const0
-- Cumulative (cdf) counterpart of the single-operand enumeration case above.
toIRInference meta True (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isForwardOnly (adtDecls meta) (resolveInjF rt name)
    && (pType (getTypeInfo left) == Deterministic || pType (getTypeInfo right) == Deterministic)
    && countProbParams [left, right] == 1
    && isEnumerable (tags (getTypeInfo (if pType (getTypeInfo left) == Deterministic then right else left))) = do
  let resolvedName = resolveInjF rt name
  let leftDet = pType (getTypeInfo left) == Deterministic
  let (detExprSrc, randExprSrc) = if leftDet then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo randExprSrc)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  let sr = semiringOf meta
  mTblRand <- materializeOperandTable meta randExprSrc
  returnO <- scoped $ do
    pRand <- operandProb meta mTblRand randExprSrc (IRVar randVar)
    return (IRIf (IROp OpLessThan sample f) (srZero sr) pRand)
  let (outerBinds, body') = hoistInvariantBindings randVar (closeExpr returnO id)
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr randVar enumList body') const0
-- A Boolean connective with one deterministic operand: @d || b@ is True where
-- @d@ holds and @b@ elsewhere, and @d && b@ dually. The connective has no
-- inverse (the arm below would need one), and before this a random operand
-- without an enumerable tag had no rule at all (fuzz-let-witness-bugs item 4,
-- @False || isLeft (left Uniform)@).
toIRInference meta cumulative (Expr _ (InjF (Named name) [a, b])) sample
  | name `elem` ["and", "or"]
  , countProbParams [a, b] == 1 && allParamsMeasurable [a, b] = do
  let sr = semiringOf meta
  let (detE, randE) = if pType (getTypeInfo a) == Deterministic then (a, b) else (b, a)
  d <- toIRGenerate meta detE
  r <- toIRInference meta cumulative randE sample
  let absorbing = name == "or"
  let absorbed = if cumulative
        then mass (compareValueExpr sr TBool (IRConst (VBool absorbing)) sample)
        else indicatorP sr (equalityGuard TBool (IRConst (VBool absorbing)) sample)
  -- The deterministic operand selects every field, so it is bound once rather
  -- than copied into each ('zipResult'); a literal stays inline and folds.
  dv <- case d of
    IRConst _ -> return d
    IRVar _   -> return d
    _ -> do
      v <- mkVariable "and_or_det"
      setVariables [(v, d)]
      return (IRVar v)
  let decides = if absorbing then dv else IRUnaryOp OpNot dv
  return (zipResult (IRIf decides) absorbed r)
--
-- Not for a forward-only InjF (@and@/@or@): it has no inverse to solve for the
-- probabilistic operand, and asking 'inversionFor' for one was an uncaught
-- error (fuzz-let-witness-bugs item 4, @False || isLeft (left Uniform)@).
toIRInference meta cumulative (Expr TypeInfo {tags=_, rType=rt} (InjF (Named name) params)) sample
  | countProbParams params == 1 && allParamsMeasurable params
  , not (isForwardOnly (adtDecls meta) (resolveInjF rt name)) = do
  let resolvedName = resolveInjF rt name
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let inVars = inputVars fwd
  let v1 = soleOutputVar fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let probIdx = theProbIndex name params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let invDecl = inversionFor name (inVars !! probIdx) inversions
  let FDecl {inputVars=invVars, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  -- Find the relevant derivative of the inversion
  let invDeriv = inverseDerivative name v1 invDerivs
  -- The bound to invert through, rounded for a cumulative integer quotient
  -- ('modeInverse').
  let (invExpr, appTest) = modeInverse cumulative invDecl invDeriv
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic
  -- subexpression, isolated and re-guarded on appTest (see
  -- 'guardedSubInference') so a shared let-in block cannot escape the
  -- applicability test 'guardP' applies below.
  -- Unpruned when the cumulative CoV below may flip it through a complement.
  let metaOp = covOperandMeta cumulative invDeriv meta
  let operandAt c = guardedSubInference metaOp [appTest] (probF metaOp c (params !! probIdx) invExpr)
  paramRes <- operandAt cumulative
  -- Scale the result according to the CoV formula (the point mass at the
  -- bound joins a decreasing CDF flip), then test whether the inversion is
  -- applicable.
  scaled <- pointInverseCoV meta cumulative invDeriv paramRes (operandAt False)
  return (guardP (semiringOf meta) [appTest] scaled)
-- Enumerate-both discrete path for forward-only binary InjFs (and/or). No point
-- inverse exists, so loop the |L|x|R| grid and keep cells where forward(l,r) == sample,
-- accumulating pLeft(l) * pRight(r). Mirrors the cumulative double-enum path below.
--
-- Also for @==@ of two random enumerable operands (@camNN img == depthNN
-- depth@): its inverse on the False polarity is the 'VAnyExcept' set, which
-- the invertible grid below would hand to 'IRIsPossible' and the text
-- backends cannot render, so it is compared forward here instead. Before the
-- 'hasAnyExcept' arm above required one probabilistic operand, this shape died
-- there ("More than one probabilistic argument", task
-- bare-equality-of-two-neural-reads-crashes, whose O(V) agreement fusion this
-- O(V^2) grid is not).
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | (isForwardOnly (adtDecls meta) (resolveInjF rt name) || hasAnyExcept (adtDecls meta) name)
    && isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  let enumListL = head [x | DiscreteValues x <- tags (getTypeInfo left)]
  let enumListR = head [x | DiscreteValues x <- tags (getTypeInfo right)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let sr = semiringOf meta
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  returnO <- scoped $ do
    pLeft <- operandProb meta mTblL left (IRVar v1)
    pRight <- operandProb meta mTblR right (IRVar v2)
    return (IRIf (IROp OpEq f sample) (srTimes sr pLeft pRight) (srZero sr))
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (closeExpr returnO id)
  let innerSum = buildLetIns v2InvBinds (enumSumNode sr v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr v1 enumListL v1Body) const0
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head [x | DiscreteValues x <- extrasLeft]
  let enumListR = head [x | DiscreteValues x <- extrasRight]
  -- mult/multI's own absorbing element, in this node's type -- see the
  -- zero-atom mix below.
  let zeroValL = zeroValueOf rt

  fPair <- instantiate mkVariable (adtDecls meta) resolvedName -- FPair of the InjF with unique names
  let FPair fwd inversions = fPair
  let (_, v3) = binaryInputVars resolvedName fwd
  -- We get the inversion to the right side
  let invDecl = inversionFor resolvedName v3 inversions
  let (x2, x3) = binaryInputVars resolvedName invDecl
  let invExpr = body invDecl
  let appTest = applicability invDecl

  -- We now compute
  -- for each e in leftEnum:
  --   sum += if invExpr(e, sample) in rightEnum then pLeft(e) * pRight(sample - e) else 0
  -- For that we name e like the lhs of
  -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
  let sr = semiringOf meta
  -- Materialized operand marginals, when the operand is itself a nested
  -- enumerable chain: built here, in the enclosing scope, so their cells are
  -- computed once instead of once per iteration of the enumeration below.
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  irTuple <- scoped (do
    -- the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    setVariables [(x3, sample)]
    -- The inversion's own applicability (task mult-enumerable-zero-divisor-crash):
    -- 'invExpr' (e.g. mult's c/e) is undefined at some enumerated values (e.g.
    -- e=0), and it sits as an argument to 'IRIsPossible', so it must be
    -- evaluated before any membership test can run. Gating via 'IRIf' rather
    -- than 'OpAnd' matters here: both operands of an IR boolean op are
    -- evaluated, so an 'OpAnd' would still divide by zero.
    let possibleExpr = IRIf appTest (IRIsPossible (multiValueToIR enumListR) invExpr) (IRConst (VBool False))
    -- Without topK, pLeft is read once, inside the 'possible' arm below, and the
    -- optimizer's let-inlining moves its bindings there: a cell whose inverted
    -- value lies outside the right-hand domain never descends into @left@.
    -- Under topK the cutoff test reads pLeft a second time, so its bindings
    -- stayed in front of the guard and every cell descended into @left@
    -- whether or not it was possible. On a left-nested chain that eager
    -- descent compounds per level into a product of the domain sizes, where
    -- the guarded one only walks the possible splits (task
    -- topk-compiled-scene-count-query-exponential-in-slots: p(0) on a 7-slot
    -- scene count took 34 s against 0.1 s topK-off). So under topK pLeft is
    -- bound once, behind 'possible', and reads as zero elsewhere -- a value
    -- nothing consumes there, since the cutoff test is conjoined with
    -- 'possible'. Its pure loop-invariant bindings (a network call) are
    -- released into the writer first, as pRight's are below, so hoisting
    -- still lifts them out of the loop.
    (pLeft, leftNames, possible) <- case topKThreshold (compilerConfig meta) of
      Nothing -> do
        oL <- scoped (operandProb meta mTblL left (IRVar x2))
        pL <- inline oL
        return (pL, openNames oL, possibleExpr)
      Just _ -> do
        oL <- scoped (operandProb meta mTblL left (IRVar x2))
        let (lFree, lGuarded) = splitOpen (splitHoistable [x2, x3]) oL
        inline lFree
        possibleV <- mkVariable "possible"
        pLeftV <- mkVariable "pLeft"
        setVariables [ (possibleV, possibleExpr)
                     , (pLeftV, IRIf (IRVar possibleV) (closeExpr lGuarded id) (srZero sr)) ]
        return (IRVar pLeftV, openNames lGuarded ++ [possibleV, pLeftV], IRVar possibleV)
    -- pRight is computed in a nested writer so its bindings can be guarded by the topK check,
    -- avoiding the inner right-side inference work whenever acc_prob * pLeft is already below cutoff.
    -- The right-hand key is the INVERTED value, an expression rather than an
    -- enumeration variable, so a table read has to bind it first: the lookup
    -- reads its key once per arm.
    pRightO <- scoped $ case mTblR of
          Just tbl -> do
            keyName <- mkVariable "mat_key"
            setVariables [(keyName, invExpr)]
            return (mass (lookupMarginal meta tbl (IRVar keyName)))
          Nothing -> toIRInference meta False right invExpr
    -- The guard below keeps pRight's per-cell work out of cells that fail it,
    -- but it also used to trap pRight's loop-invariant bindings -- a neural
    -- operand's raw network call, @nn_raw = n(b)@ -- inside the loop body,
    -- where 'hoistInvariantBindings' below never sees them. pLeft's matching
    -- call is in this writer and so was hoisted: @n(a) ++ n(b)@ ran the
    -- network once for @a@ and once per enumerated cell for @b@ (task
    -- plusi-second-operand-oracle-not-hoisted: 1 vs 1900 on the two-digit
    -- MNIST sum). Pure bindings that read no loop variable and nothing bound
    -- per iteration are released into this writer instead, so they are
    -- hoisted exactly like pLeft's; everything else stays guarded.
    let (rFree, rGuarded) = splitOpen (splitHoistable (x2 : x3 : leftNames)) pRightO
    inline rFree
    -- accProb * pLeft is a semiring product (srTimes): under logSpace both
    -- operands are log-probabilities, so a hardcoded OpMult here silently
    -- pruned every branch (task topk-logspace-unsound). The comparison against
    -- the cutoff stays OpGreaterThan either way -- log is monotone, and the
    -- runtime cutoff parameter is passed in the matching space.
    let cutoffOk = case topKThreshold (compilerConfig meta) of
          Nothing -> possible
          Just _  -> IROp OpAnd possible
                       (IROp OpGreaterThan
                          (srTimes sr (accProb meta) pLeft)
                          (IRVar topKCutoffParamName))
    let returnExpr   = IRIf cutoffOk (closeExpr rGuarded (srTimes sr pLeft . unP . rProb)) (srZero sr)
    let branchesExpr = IRIf cutoffOk (IRConst (VFloat 1)) (IRConst (VFloat 0))
    return (mkPResult (sealP returnExpr) dim0 branchesExpr (notIR cutoffOk))
    ) <&> generateLetInBlock meta
  uniquePrefix <- mkVariable ""
  let applyUnique = irMap (uniqueify [x2, x3] uniquePrefix)
  let (outerBinds, innerTuple) = hoistInvariantBindings x2 irTuple
  let renameHoisted (n, v) = (if n `elem` [x2, x3] then uniquePrefix ++ n else n, applyUnique v)
  setVariables (map renameHoisted outerBinds)
  summed <- enumSumP (semiringOf meta) (countBranches (compilerConfig meta)) applyUnique x2 enumListL innerTuple
  -- mult(0, y) = 0 for every y: the applicability guard above correctly drops
  -- that enumerated cell (a=0 is not point-invertible -- its fiber is the
  -- whole right-hand domain, not a point), but dropping it silently
  -- under-reports p(sample=0) by exactly P(a=0) (task
  -- mult-inverse-unguarded-zero-division: "the marginal should be trivially
  -- 1" for that cell). Mixed back in the same way an explicit
  -- `if coinflip then ... else 0` mixture already is: as its own alternative,
  -- picked by 'mixP' (lower dim / possibility wins) rather than folded into
  -- the enumerated sum, which assumes every term is a point-invertible
  -- density/mass of the same shape.
  if resolvedName `elem` ["mult", "multI"] && zeroValL `elem` multiValueToValueList enumListL
    then do
      pLeftZero <- operandProb meta mTblL left (IRConst (valueToIR zeroValL))
      let zeroAtom = prodP sr (mass pLeftZero) (indicatorP sr (equalityGuard rt sample (IRConst (valueToIR zeroValL))))
      mixP sr (IROp OpPlus (rBranches summed) (rBranches zeroAtom)) zeroAtom summed
    else return summed
-- For the cumulative case we cant get around two enum sums
toIRInference meta True (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head [x | DiscreteValues x <- extrasLeft]
  let enumListR = head [x | DiscreteValues x <- extrasRight]

  fPair <- instantiate mkVariable (adtDecls meta) resolvedName -- FPair of the InjF with unique names
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let sr = semiringOf meta
  -- Compute the loop body in a nested writer so its bindings can be captured rather
  -- than leaking to the enclosing function scope: those bindings reference the enum
  -- variables v1/v2 (the coin_prob calls) and must be scoped *inside* the matching
  -- enumSum, not above it.
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  returnO <- scoped $ do
    pLeft <- operandProb meta mTblL left (IRVar v1)
    pRight <- operandProb meta mTblR right (IRVar v2)
    return (IRIf (IROp OpLessThan sample f) (srZero sr) (srTimes sr pLeft pRight))
  -- Place each binding at the outermost scope where it remains well-formed: fully
  -- invariant bindings are hoisted to the function top level, bindings depending only
  -- on v1 sit between the two enumSums, and bindings depending on v2 stay innermost.
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (closeExpr returnO id)
  let innerSum = buildLetIns v2InvBinds (enumSumNode sr v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr v1 enumListL v1Body) const0
toIRInference meta cumulative (Expr TypeInfo {rType=rt} (Var n)) sample = do
  -- Variable might be a function
  case lookup n (typeEnv meta) of
    -- Var is a function
    Just(TArrow _ _, hasInference) -> do
      var <- mkVariable "call"
      name <- if hasInference then calleeInferenceName meta cumulative n else return n
      let callExpr = if hasInference
            then inferenceCall meta cumulative (IRVar name) sample
            else IRApply (IRVar name) sample
      setVariables [(var, callExpr)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (detP (IRVar var))
    -- Var is a top level declaration (an therefor has a _prob function)
    Just (_, True) -> do
      var <- mkVariable "call"
      calleeName <- calleeInferenceName meta cumulative n
      let callExpr = inferenceCall meta cumulative (IRVar calleeName) sample
      setVariables [(var, callExpr)]
      return (unpackResult var)
    -- Var is a local variable
    -- A bound parameter used directly as a return value is a LEAF resolution:
    -- it compares a deterministically-known value against the sample and stops,
    -- the identical operation the 'Constant'/'ThetaI' cases perform. It
    -- therefore counts as one branch like they do -- 'mass'/'indicatorP', not
    -- 'detP'. The branch-count anchor is "every terminal leaf counts 1,
    -- deterministic or random", so which AST constructor happens to carry the
    -- same value into the same comparison must not change the count (task
    -- bc-recursive-prob-divergence; pinned by prop_BCLeafSpellingIndependence).
    -- 'detP' -- zero branches -- stays for results that resolve to no value at
    -- all: closures, lambdas, the TArrow arms above.
    Just (_, False) ->
      if cumulative then
        return (mass (compareValueExpr (semiringOf meta) rt (IRVar n) sample))
      else
        return (indicatorP (semiringOf meta) (equalityGuard rt (IRVar n) sample))
    -- Invariant, not a refusal (task static-refusals-become-absent-variants): every bound name is in the type env (a miss is filed: fuzz-admission-oracle-bugs item 7).
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
-- Mixed enumerate-and-shift/scale convolution: exactly ONE operand is a
-- finite-discrete enumerable (a `DiscreteValues`-tagged mixture of point
-- masses), the other is a continuous scalar with a density. The marginal
--
--   f_Z(z) = sum_e p_X(e) * f_Y(g^-1_y(e, z)) * |d g^-1_y / dz|
--
-- is exactly what 'marginalize's `keepD` guard promises for this shape (a
-- finite mixture convolved with a Normal/LogNormal has a closed-form density),
-- and until task marginalize-keepd-overclaims-density-for-generic-plus-mult
-- nothing here built it: the node typed 'Integrate', matched no equation, and
-- fell through to the catch-all `error` below.
--
-- It is the composition of the two clauses either side of it: the
-- both-enumerable path's `enumSumP` loop over the finite operand's support,
-- with the generic single-inversion path's body (invert to the continuous
-- operand, evaluate its density there, apply the change-of-variables Jacobian)
-- as the loop body. The `IRIsPossible` membership test the both-enumerable
-- path applies to the inverted value is absent here on purpose: the other
-- operand is continuous, so every inverted point is in its support.
--
-- The result's `dim` cannot come through 'enumSumP', which packs only
-- (prob, branches) and hardcodes dim 0 for the discrete mass it normally
-- builds. It is supplied here instead, and it is a static property rather
-- than a per-iteration one: the enumerated side contributes dim 0, the
-- change of variables is dimension-preserving, so the node's dim is the
-- continuous operand's. In probability mode that is dim 1, ANY-guarded on
-- this node's own sample; in cumulative mode a CDF value is a mass, so it is
-- dim 0 (what the continuous operand's own cumulative result reports). The
-- guard's `rType` test is what earns reading that off statically: a
-- non-'Deterministic', non-enumerable 'TFloat' operand under
-- 'allParamsMeasurable' is a continuous scalar.
--
-- The override happens outside the loop and so does not disturb 'scaleCoV',
-- which reads the per-iteration operand's own `rDim` inside it.
toIRInference meta cumulative (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | rt == TFloat
  , not (isForwardOnly (adtDecls meta) (resolveInjF rt name))
  , pType (getTypeInfo left) /= Deterministic
  , pType (getTypeInfo right) /= Deterministic
  , isEnumerable (tags (getTypeInfo left)) /= isEnumerable (tags (getTypeInfo right))
  , rType (getTypeInfo (if isEnumerable (tags (getTypeInfo left)) then right else left)) == TFloat
  , allParamsMeasurable [left, right] = do
  let resolvedName = resolveInjF rt name
  let leftEnum = isEnumerable (tags (getTypeInfo left))
  let (enumE, contE) = if leftEnum then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo enumE)]
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let (vL, vR) = binaryInputVars resolvedName fwd
  let contVar = if leftEnum then vR else vL
  -- The inversion that solves for the CONTINUOUS operand; its two inputs are
  -- the enumerated operand's value and this node's observation.
  let invDecl = inversionFor resolvedName contVar inversions
  let FDecl {body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  let (xEnum, xSample) = binaryInputVars resolvedName invDecl
  -- d(inverse)/d(observation), keyed by the forward declaration's output var
  -- (for `mult` this is the 1/e that makes the scaled mixture integrate to 1).
  let invDeriv = inverseDerivative resolvedName (soleOutputVar fwd) invDerivs
  let sr = semiringOf meta
  let probF = if decons then toIRInferenceSave else toIRInference
  let metaOp = covOperandMeta cumulative invDeriv meta
  mTblEnum <- materializeOperandTable meta enumE
  -- With no table for the enumerated operand, the loop below re-derives
  -- p(enumE = e) for every value e of its domain, and that is a full
  -- enumeration of the draws it is a function of: |dom(enumE)| x 10^N cells
  -- for N digit reads (task noisy-observation-mixes-over-result-value-domain).
  -- When the operand is such a function, sum over its draws' cells directly
  -- instead ('latentCellSum'): one term per cell, at the cell's forward value.
  let cellDraws = latentCellBinders meta enumE
  perCell <- case (mTblEnum, cellDraws) of
    (Nothing, ds@(_:_)) | not (any (`Set.member` freeVarsExpr contE) ds) -> do
      uniquePrefix <- mkVariable ""
      let un = irMap (uniqueify [xEnum, xSample] uniquePrefix)
          metaOpU = covOperandMeta cumulative (un invDeriv) meta
      -- Built in a scope of its own: a leaf that turns out to draw fresh
      -- randomness declines the whole attempt, and its bindings are dropped.
      attemptO <- scoped $
        latentCellSum meta cumulative (anyGuardedDim sample) enumE (\fv -> fmap Just $ do
          setVariables [(uniquePrefix ++ xSample, sample), (uniquePrefix ++ xEnum, fv)]
          contRes <- guardedSubInference metaOpU [un appTest]
                       (probF metaOpU cumulative contE (un invExpr))
          return (guardP sr [un appTest] (scaleCoV sr cumulative (un invDeriv) contRes)))
      inlineIfJust attemptO
    _ -> return Nothing
  summedTyped <- case perCell of
   Just r -> return r
   Nothing -> do
    irTuple <- scoped (do
      setVariables [(xSample, sample)]
      pEnumRaw <- operandProb meta mTblEnum enumE (IRVar xEnum)
      pEnumVar <- mkVariable "p_enum"
      setVariables [(pEnumVar, pEnumRaw)]
      let pEnum = IRVar pEnumVar
      contRes <- guardedSubInference metaOp [appTest]
                   (probF metaOp cumulative contE invExpr)
      let scaled = guardP sr [appTest] (scaleCoV sr cumulative invDeriv contRes)
      -- A value of the enumerated operand's domain with no mass is an
      -- impossible term, not a possible zero: 'enumMixP' below lets the
      -- lowest-dim possible term decide the result's dim, and a zero-weight
      -- atom must not outvote a real density. The tag over-approximates the
      -- support, so such values are ordinary. Exact zero is sound here for the
      -- reason 'opaqueMass' gives: this is a discrete mass.
      return (prodP sr (impossibleWhen (IROp OpEq pEnum (srZero sr)) (mass pEnum)) scaled)
      ) <&> generateLetInBlock meta
    uniquePrefix <- mkVariable ""
    let applyUnique = irMap (uniqueify [xEnum, xSample] uniquePrefix)
    let (outerBinds, innerTuple) = hoistInvariantBindings xEnum irTuple
    let renameHoisted (n, v) = (if n `elem` [xEnum, xSample] then uniquePrefix ++ n else n, applyUnique v)
    setVariables (map renameHoisted outerBinds)
    -- The "continuous" operand is only known to be a real scalar (its rType),
    -- not to have a density: an operand no tag reaches -- a fold through a
    -- recursive helper, which Analysis refuses to look through -- may be a
    -- discrete count the plan path answers as a mass, or a mixture of atoms and
    -- a density. So in probability mode each term keeps the dim its own
    -- inference reports, and 'enumMixP' combines them as a mixture (possible
    -- atoms outvote densities), instead of stamping dim 1 on the sum (task
    -- plan-sum-with-sunk-discrete-draw-reports-density). A term that is a true
    -- density reports 'anyGuardedDim', so a genuinely continuous operand gets
    -- exactly the result it did before. Cumulative mode is a CDF, dim 0,
    -- whatever the terms are.
    if cumulative
      then enumSumP sr (countBranches (compilerConfig meta)) applyUnique xEnum enumList innerTuple
      else enumMixP sr (countBranches (compilerConfig meta)) applyUnique (anyGuardedDim sample) xEnum enumList innerTuple
  -- mult(0, y) = 0 for every y (task mult-inversion-unguarded-at-zero, symptom
  -- 3): 'appTest' above already keeps the guarded scaling from dividing by
  -- e=0, but that just drops the term -- the true contribution of that
  -- enumerated cell is the DEGENERATE law "the result is deterministically 0",
  -- an atom the density sum can't represent (it has no Lebesgue density).
  -- Mixed back in exactly the way an explicit `if coinflip then 0 else 2*Normal`
  -- already is: as its own alternative, picked by 'mixP' (lower dim wins) in
  -- probability mode, or added in cumulative mode where both sides are dim 0
  -- CDF contributions anyway.
  if resolvedName == "mult" && VFloat 0 `elem` multiValueToValueList enumList
    then do
      pEnumZero <- operandProb meta mTblEnum enumE (IRConst (VFloat 0))
      let zeroIndicator = if cumulative
                            then mass (compareValueExpr sr rt (IRConst (VFloat 0)) sample)
                            else indicatorP sr (equalityGuard rt sample (IRConst (VFloat 0)))
      let zeroAtom = prodP sr (mass pEnumZero) zeroIndicator
      mixP sr (IROp OpPlus (rBranches summedTyped) (rBranches zeroAtom)) zeroAtom summedTyped
    else return summedTyped
toIRInference _ _ (Expr ti (Subtree _ _)) _ = refuse (chainName ti) "Cannot infer prob on subtree expression. Please check your syntax"
-- The catch-all: no inference equation covers this node. Reached only when
-- the modality engine admitted a shape no IR equation builds (an over-promise,
-- design pipeline-coherence F2); it is a refusal of the variant, not a crash.
toIRInference _ cumulative x _ = refuse (chainName (getTypeInfo x))
  ("found no way to convert to IR in " ++ (if cumulative then "cumulative" else "probability")
   ++ " mode (pType " ++ show (pType (getTypeInfo x)) ++ "): " ++ show x)

createHOInverse :: CompilerMetadata -> (String, Expr) -> CompilerMonad (IRExpr -> IRExpr)
createHOInverse meta (fVar, f) = do
  let fcData' = fcData meta
  let localAdts = adtDecls meta
  -- NB: the applicability guard (3rd component, see observe-partials-umbrella
  -- N1b) is not threaded through the higher-order inverse path yet -- a
  -- deconstructing InjF crossed while inverting a user-defined function passed
  -- through createHOInverse can still crash. Not hit by any current test case;
  -- tracked as follow-up alongside the other HO-inverse gaps.
  let InvChain{invValue = inverseF0, invCoV = inverseCoV0} = toInvExpr fcData' localAdts (chainName $ getTypeInfo f)
  inverseF   <- materializeAnchors meta inverseF0
  inverseCoV <- materializeAnchors meta inverseCoV0
  let (_, _, lBodyChainName, tag) = equivalentLambda "createHOInverse" fcData' (chainName $ getTypeInfo f)
  let inverseLambdaProb = IRLambda (lBodyChainName ++ tag) inverseF
  let inverseLambdaCoV = IRLambda (lBodyChainName ++ tag) inverseCoV
  -- Rename all occurances of f^-1 from the definition to f_prob
  let renVar = renameVar (fVar ++ "^-1") (fVar ++ "_prob")
  let renDeriv = renameVar (fVar ++ "^-1'") (fVar ++ "_prob_deriv")
  setVariables [(fVar ++ "_prob", inverseLambdaProb), (fVar ++ "_prob_deriv", inverseLambdaCoV)]
  return (renVar . renDeriv)

countProbParams :: [Expr] -> Int
countProbParams es = length probParams
  where
    probParams = filter (\p -> p == Integrate || p == PNormal || p == PLogNormal) pTypes
    pt x = pType (getTypeInfo x)
    pTypes = map pt es

-- True when no parameter is 'Bottom' -- i.e. every parameter is either
-- 'Deterministic' or one of the three tractable probabilistic rungs
-- (Integrate/PNormal/PLogNormal). A 'countProbParams params == k' guard by
-- itself only counts the tractable rungs, so a 'Bottom' parameter (no
-- measurable distribution at all -- "nothing better than sampling is
-- available") is silently indistinguishable from an absent one: a clause
-- guarded by 'countProbParams params == 0' would treat "every parameter is
-- Deterministic" and "one parameter is Bottom, the rest Deterministic" as
-- the same case, and fall through to 'toIRGenerate' on the Bottom
-- parameter -- a fresh random draw compared against the query sample,
-- silently wrong rather than refused (task
-- projection-discards-intractable-sibling-generate-backed, reached via
-- 'fst'/'snd' projecting away an intractable sibling: 'fst (Uniform,
-- Uniform * Uniform)'). Every 'countProbParams params == k' guard on an
-- InjF clause must therefore also assert this.
allParamsMeasurable :: [Expr] -> Bool
allParamsMeasurable = all ((/= Bottom) . pType . getTypeInfo)

-- | 'mult'/'multI's absorbing element, in a given return type -- shared by the
-- zero-multiplier InjF clause above and the enumerable-domain zero-atom fixes
-- below (tasks mult-inversion-unguarded-at-zero,
-- mult-enumerable-zero-divisor-crash, mult-inverse-unguarded-zero-division).
zeroValueOf :: RType -> Value
zeroValueOf TInt = VInt 0
zeroValueOf _    = VFloat 0

-- | The factor of a product that is deterministic, may be zero at run time,
-- and multiplies a random operand -- the one 'mult' must branch on (see the
-- run-time zero-factor clause). Not a factor that is statically zero (the
-- static clauses take it) or statically nonzero (a nonzero literal, or a
-- 'DiscreteValues' set without zero), nor a product of two random operands.
runtimeZeroFactor :: Expr -> Expr -> Maybe Expr
runtimeZeroFactor a b = case (det a, det b) of
  (True, False) | mayBeZero a -> Just a
  (False, True) | mayBeZero b -> Just b
  _ -> Nothing
  where
    det x = pType (getTypeInfo x) == Deterministic
    mayBeZero x@(Expr ti nd)
      | isStaticZero x = False
      | Constant _ <- nd = False
      | (MultiDiscretes vs : _) <- [ mv | DiscreteValues mv <- tags ti ] = any isZeroLit vs
      | otherwise = True
    isZeroLit (VFloat 0) = True
    isZeroLit (VInt 0) = True
    isZeroLit _ = False

-- | Whether a value of this type has a function anywhere inside it.
containsArrow :: RType -> Bool
containsArrow (TArrow _ _)      = True
containsArrow (ListOf t)        = containsArrow t
containsArrow (Tuple a b)       = containsArrow a || containsArrow b
containsArrow (TEither a b)     = containsArrow a || containsArrow b
containsArrow (TTensor _ t)     = containsArrow t
containsArrow (GreaterType a b) = containsArrow a || containsArrow b
-- Spelled out rather than a catch-all, so a new 'RType' constructor is a
-- compile error here instead of a silent False.
containsArrow TBool       = False
containsArrow TInt        = False
containsArrow TSymbol     = False
containsArrow TFloat      = False
containsArrow TUnit       = False
containsArrow TThetaTree  = False
containsArrow (TADT _)    = False
containsArrow NullList    = False
containsArrow BottomTuple = False
containsArrow (TVarR _)   = False
containsArrow SPLL.Typing.RType.NotSetYet = False


-- | The 'Recur' every compile's 'CompilerMetadata' carries: the translators
-- themselves, for the engine modules below this one to call back into.
knot :: Recur
knot = Recur
  { recInference     = toIRInference
  , recInferenceSave = toIRInferenceSave
  , recGenerate      = Generate.toIRGenerate
  }
