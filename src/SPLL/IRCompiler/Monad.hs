-- | The compiler's shared state and vocabulary: 'CompilerMetadata' and the
-- binder environment ('LawEnv'), the 'Recur' record through which the engine
-- modules call back into the translators, and the small helpers several
-- engines share.
module SPLL.IRCompiler.Monad (
  TypeEnv,
  CompilerMetadata(..),
  Recur(..),
  toIRInference,
  toIRInferenceSave,
  toIRGenerate,
  semiringOf,
  unpruned,
  inferenceCall,
  covOperandMeta,
  pointInverseCoV,
  generateLetInBlock,
  flattenApplySpine,
  equivalentLambda,
  Binding(..),
  exprWithCN,
  LawEnv,
  BoundVar(..),
  boundAt,
  recoveredVars,
  recoverVars,
  marginaliseAs,
  withBindingLaw,
  lawPoint,
  nodeLaw,
  anyMarginal,
  exceptMeasure,
  wholeSoleConstructor,
  guardedSubInference,
  inlineIfJust,
  anyExceptSampleShape,
  isTArrowType,
  failConversion,
  materializeAnchors,
  nodeChainNames,
  compareValueExpr,
  listSpine,
  discreteFloatAtoms,
  atomBelow,
  atomAbove,
  symbolCdfMessage,
  equalityGuard,
  equalityGuardBody,
  leafEqIR,
  uniqueify
) where

import SPLL.ReservedNames (topKCutoffParamName)
import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.IRCompiler.Affine
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Analysis (LatentBinder(..))
import SPLL.Typing.PType
import Data.Maybe
import Data.List (isInfixOf, nub, sort)
import SPLL.Typing.ForwardChaining
import SPLL.Typing.ModalityInfer (ReinferCtx, LawTable, Law, bareLawOfPType, bindingLawEnv, lawValue)
import qualified SPLL.Typing.ModalityInfer as ModalityInfer
import SPLL.Typing.AlgebraicDataTypes
import SPLL.IR.Type (IRType(..))
import SPLL.Semiring
import Control.Monad (foldM, mfilter)
import Control.Monad.Except (catchError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | 'PResult', its combinator vocabulary, and the 'Semiring' abstraction that
-- makes the probability field's arithmetic mode-agnostic (linear vs. log-space)
-- now live in 'SPLL.Semiring' (task semiring-discipline-enforcement): moving
-- them out of this module -- the one whose dispatch code caused both known
-- instances of the "hand-rolled linear arithmetic on a probability" bug class
-- -- lets the probability field be a newtype whose constructor only
-- 'SPLL.Semiring' can see, so a 'toIRInference' case here cannot drop a bare
-- 'IROp'/'IRIf' into it without going through a Semiring-aware combinator or
-- a named, greppable escape hatch ('unsafeLinearP'/'sealP').

-- (name, ((RType of (Var name)), (Has _gen _prop _integ (if applicable) functions)))
type TypeEnv = [(String, (RType, Bool))]

data CompilerMetadata = CompilerMetadata {
  compilerConfig :: CompilerConfig,
  fcData :: FCData,
  typeEnv :: TypeEnv,
  adtDecls :: [ADTDecl],
  compilingProgram :: Program,
  accProb :: IRExpr,
  -- | The decomposability verdict per binary InjF node of the whole program,
  -- keyed by chain name (unique program-wide): True = the node's two operands
  -- may share an enumerated latent, so its marginal must NOT be tabulated by
  -- convolving them separately. Precomputed once per compile because the
  -- verdict depends on the 'let'-scope lexically enclosing the node, which a
  -- 'toIRInference' case looking at a node in isolation cannot reconstruct.
  latentVerdicts :: Map.Map ChainName Bool,
  -- | What 'latentVerdicts' is computed from, per binary InjF node
  -- ('materializationScopes'), for the one consumer that retakes the verdict
  -- given the latents an enclosing enumeration has fixed.
  latentScopes :: Map.Map ChainName ([LatentBinder], Expr, Expr),
  -- | The latent identities (the chain names of their draws, as
  -- 'bindLatent' keys them) that enclosing enumeration loops have fixed:
  -- inside @enumerateAppliedLambda@'s loop over @let x = v@, @v@ holds one
  -- value. The latent counterpart of a recovered variable ('recoveredVars').
  fixedLatents :: Set.Set ChainName,
  -- | The @_gen@ function names whose evaluation draws no randomness, from
  -- 'SPLL.Typing.Determinism.functionSummaries'. Consumed by
  -- 'requireDeterministicUnderEnum' (and only there) as the deterministic-generator
  -- set 'isPureGiven' needs: 'isEffectfulVar' is a name test that calls /every/
  -- @_gen@ reference random, and an enumerated inference body is written almost
  -- entirely in terms of deterministic helper calls.
  detGenNames :: Set.Set Varname,
  -- | The @_gen@ names of the top-level functions that sit on a call-graph
  -- cycle (self-recursion included). 'toIREnumerate' reads this to tell a
  -- fresh draw it can hand to 'toIRInference' (a primitive, a neural read, a
  -- call into a non-recursive helper) from one whose probability function
  -- could re-enter the very enumeration being compiled with an unchanged
  -- argument -- the unbounded @... else main@ shape, which stays refused
  -- (task enum-let-latent-gates-fresh-draw).
  cyclicGenNames :: Set.Set Varname,
  -- | Which 'SemiringFamily' 'semiringOf' builds this compile's 'Semiring'
  -- from (task semiring-parametric-marginals). 'SRSumProduct' for every
  -- ordinary compiled body; overridden to one of 'extraSemirings''s entries
  -- only for the extra probability-mode 'IRFunGroup's 'envToIRUnoptimized''
  -- builds alongside the ordinary ones -- see 'extraSemiringGroups'. Kept on
  -- 'CompilerMetadata' rather than read straight off 'CompilerConfig' so that
  -- override is a plain record update at the one call site that needs it,
  -- with every recursive call (all ~50 of which read 'semiringOf meta', not
  -- 'compilerConfig meta', for exactly this reason) automatically compiling
  -- under the overridden family with no change of its own.
  semiringFamily :: SemiringFamily,
  -- | What 'reinferRecovered' needs to re-run modality inference on a body
  -- under the recovered variables; built once per compile.
  reinferContext :: ReinferCtx,
  -- | The 'mult'/'multI' nodes (by chain name) whose deterministic factor is
  -- already branched on at run time ('runtimeZeroFactor'), so the recursive
  -- compile of the nonzero arm takes the ordinary inversion.
  zeroGuardedProducts :: Set.Set ChainName,
  -- | Function parameters an engine has bound to a lambda it can see, under
  -- the fresh names 'enterBindingScope' gives them: a call through one is a
  -- binding of that lambda's parameter ('callBindingAt').
  boundLambdas :: [(String, Expr)],
  -- | The callee bodies 'enterBindingScope' has made meaningful here, each
  -- as the chain names of its nodes and the renames of its leading
  -- parameters to their fresh names. An engine compiles such a body renamed,
  -- but a forward-chaining anchor in it is fetched by chain name from the
  -- program as written ('materializeAnchors'), so the anchor is renamed the
  -- same way ('anchorAtCall'); otherwise it reads the caller's namesake of
  -- the parameter (task theta-anchor-through-callee-local-binding).
  enteredScopes :: [(Set.Set ChainName, [(String, String)])],
  -- | The modality engine's certificate for every node of the program, by
  -- chain name ('SPLL.Typing.ModalityInfer.inferProgram'; design
  -- law-carrying-modality §B). Not a 'TypeInfo' field: a 'Law' holds closures.
  -- Read through 'nodeLaw'. It certifies the program as written: a node
  -- re-inferred under recovered variables ('reinferRecovered') gets new types,
  -- not a new entry here.
  lawTable :: LawTable,
  -- | Every variable bound by an enclosing binder of the code being
  -- compiled ('BoundVar'): a lambda's parameter ('extendMetaForLambda') and,
  -- at every 'Binding', the bound parameter at the argument's law
  -- ('withBindingLaw'), by the modality engine's own binder rule
  -- ('bindingLawEnv'), so its laws are the environment 'inferE' had there.
  -- It also records what an engine did with a variable: fixed it
  -- ('recoverVars') or marginalised it as an affine form ('marginaliseAs').
  lawEnv :: LawEnv,
  -- | Whether every enclosing enumerated sum keeps its terms' dims
  -- ('enumSumTerms'; task enumerated-sum-over-density-body). True outside
  -- any enumeration; an enumeration whose body's type has no static bound on
  -- its dim ('floatLeafBound') sums its terms as masses and clears it for
  -- everything below. 'forwardOrInfer' reads it: a delegated body that may
  -- be a density needs its run-time guard only when some enclosing sum
  -- would report it as a mass.
  dimAwareEnum :: Bool,
  -- | Whether this compile is a materialized-marginal leaf cell
  -- ('SPLL.IRCompiler.Materialize.pointQueryTable'). Inside one,
  -- 'SPLL.IRCompiler.Enumerate.nestedDrawTables' is off, as it is under
  -- --batched: the cell's size decides whether the table is built at all
  -- ('maxTabulatedLeafNodes'), and that decision must not depend on the
  -- backend, or the backends answer through different engines and prune
  -- differently under topK (task batched-topk-noisy-if-fold-of-reads-disagrees).
  inTabulatedLeaf :: Bool,
  -- | The translators' recursive entry points ('Recur'), so an engine
  -- module calls back into them without importing the module that
  -- defines them. Always 'SPLL.IRCompiler.Inference.knot'.
  recur :: Recur
}

-- | The translators' recursive entry points, as a record held in every
-- 'CompilerMetadata' ('recur'). The engine modules call back into the
-- translators through it: 'SPLL.IRCompiler.Inference' defines them on top of
-- the engines and ties the knot once ('SPLL.IRCompiler.Inference.knot'), so no
-- module imports one above it and no @.hs-boot@ file is needed.
data Recur = Recur
  { recInference     :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
  , recInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
  , recGenerate      :: CompilerMetadata -> Expr -> CompilerMonad IRExpr
  }

-- | 'SPLL.IRCompiler.Inference.toIRInference', through 'recur'.
toIRInference :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
toIRInference meta = recInference (recur meta) meta

-- | 'SPLL.IRCompiler.Inference.toIRInferenceSave', through 'recur'.
toIRInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
toIRInferenceSave meta = recInferenceSave (recur meta) meta

-- | 'SPLL.IRCompiler.Generate.toIRGenerate', through 'recur'.
toIRGenerate :: CompilerMetadata -> Expr -> CompilerMonad IRExpr
toIRGenerate meta = recGenerate (recur meta) meta

semiringOf :: CompilerMetadata -> Semiring
semiringOf meta = mkSemiring (semiringFamily meta) (logSpace (compilerConfig meta))

-- | Compile a sub-expression with topK pruning switched off.
--
-- A topK-pruned probability is a LOWER bound on the exact one: a dropped arm
-- contributes zero, never less than zero. Lower bounds compose under the
-- operations the rest of this module applies to them -- products, sums, and
-- the lowest-dimension-wins mixture -- but not under a complement or a
-- subtraction: @1 - lower@ and @a - lower@ are UPPER bounds. So the operand of
-- every 'srComplement' / 'srMinus' ('mixSubP') / CDF-difference site must be
-- compiled through this wrapper, or pruning below it silently inflates the
-- result above the exact value (task topk-inflates-probability-int-comparison-mix:
-- @if (if Uniform < 0.95 then False else True) then 1.0 else 2.0@ answered
-- @p(2.0) = 1.0@ at threshold 0.1, because the condition's own True-probability
-- pruned to 0 and its else-weight was then the complement 1 - 0).
--
-- Pruning is switched off by seeding the accumulated path probability with the
-- semiring's infinity rather than by a flag: every guard in this module (the
-- 'IfThenElse' arms, the enumerable-'InjF' term filter, the materialised
-- table's per-cell test) compares @accProb ⊗ p@ against the cutoff, and
-- @∞ ⊗ p = ∞@ fails every "below cutoff" test in both the linear (@∞ · p@) and
-- the log (@∞ + log p@) semiring. Being a value rather than a flag is what lets
-- it cross a function-call boundary unchanged: a callee's @_prob@ takes its
-- @acc_prob@ as an argument and needs no second, unpruned variant. The one
-- corner is @p = 0@, where @∞ ⊗ 0@ is NaN: every comparison against NaN is
-- False, so such an arm is not pruned -- the same outcome the dead-arm
-- short-circuit ('deadArm') already gives a zero-probability arm.
--
-- The cost is that nothing under a complement is pruned. An 'IfThenElse'
-- condition is no longer such a site wherever 'condWeights' builds its two
-- weights directly: a condition that is itself a Bool @if@ (or a @not@ of
-- one) gets both weights from one pass over its children, each a pruned lower
-- bound, so pruning reaches into it. Only the leaves of that recursion still
-- complement, and they compile unpruned. The subtraction sites (AnyExcept,
-- CDF differences, comparison flips) keep this wrapper.
unpruned :: CompilerMetadata -> CompilerMetadata
unpruned meta = meta { accProb = IRConst (VFloat (1 / 0)) }

-- | A call into another definition's compiled inference function. Under
-- 'topKThreshold' a @_prob@ function takes the caller's accumulated path
-- probability as a second parameter (see 'baseFunGroup''s @probFun@); an
-- @_integ@ function does not -- its root seeds its own 'accProb' with the
-- semiring's one -- so a cumulative-mode call passes only the sample. (Passing
-- @acc_prob@ there applied the callee's result tuple to a second argument:
-- "Expression is not a closure" on every topK CDF query through a call.) A
-- callee integral pruned from its own root rather than the caller's is pruned
-- less, never more, so the lower-bound reading of topK is unaffected.
--
-- Under 'topKThreshold' both variants also take the runtime cutoff
-- ('topKCutoffParamName', after @acc_prob@ for a @_prob@ and after the sample
-- for an @_integ@), forwarded unchanged so the whole call tree prunes at the
-- threshold the root was called with (task runtime-parametric-topk-threshold).
inferenceCall :: CompilerMetadata -> Bool -> IRExpr -> IRExpr -> IRExpr
inferenceCall meta cumulative callee sample =
  case topKThreshold (compilerConfig meta) of
    Just _ | not cumulative -> IRApply (IRApply (IRApply callee sample) (accProb meta)) cutoff
           | otherwise      -> IRApply (IRApply callee sample) cutoff
    Nothing                 -> IRApply callee sample
  where cutoff = IRVar topKCutoffParamName

-- | Whether an inverse's derivative is a literal positive constant, so that in
-- cumulative mode 'scaleCoV' will pass the operand's CDF through unflipped.
-- Only then may the operand stay pruned: a decreasing (or not statically
-- signed) transform flips the CDF through 'srComplement', which needs an
-- 'unpruned' operand. 'plus'/'plusI' declare literal @1@; 'neg' declares @-1@
-- and 'mult' a @1 / a@ that is only known at run time, so both compile their
-- cumulative operand unpruned.
staticallyIncreasing :: IRExpr -> Bool
staticallyIncreasing (IRConst (VFloat d)) = d > 0
staticallyIncreasing _                    = False

-- | The metadata to compile an inverted operand under: pruned in probability
-- mode (the Jacobian is a positive factor), and in cumulative mode only when
-- the CDF is statically known not to be flipped -- see 'staticallyIncreasing'.
covOperandMeta :: Bool -> IRExpr -> CompilerMetadata -> CompilerMetadata
covOperandMeta cumulative deriv meta
  | cumulative && not (staticallyIncreasing deriv) = unpruned meta
  | otherwise                                      = meta

-- | The change of variables through one point inverse, for either mode
-- (task cdf-through-discrete-inverse-wrong). Probability mode and a
-- statically increasing inverse are plain 'scaleCoV'. A cumulative query
-- through an inverse that may be decreasing needs @P(v >= x)@, which is the
-- flipped CDF plus the operand's own mass at @x@ ('scaleCoVAtom'); @atomM@
-- compiles that point result, and is run only here.
--
-- When the point result cannot be compiled (a refusal), the flip falls back
-- to the plain complement. That is exact for an operand with no atoms -- a
-- density, which is what a probability-mode refusal under a cumulative
-- variant overwhelmingly is -- and the answer every such transform gave
-- before, so no variant that compiled before becomes absent.
pointInverseCoV :: CompilerMetadata -> Bool -> IRExpr -> PResult -> CompilerMonad PResult
                -> CompilerMonad PResult
pointInverseCoV meta cumulative deriv res atomM
  | cumulative && not (staticallyIncreasing deriv) = do
      mAtom <- (Just <$> atomM) `catchError` (\_ -> return Nothing)
      return (maybe (scaleCoV sr True deriv res) (\atom -> scaleCoVAtom sr deriv atom res) mAtom)
  | otherwise = return (scaleCoV sr cumulative deriv res)
  where sr = semiringOf meta

generateLetInBlock :: CompilerMetadata -> Open PResult -> IRExpr
generateLetInBlock _ codeGen = closeExpr codeGen $ \res ->
  case unP (rProb res) of
    p@(IRLambda _ _) -> p --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> packResult res

-- | True when `Apply l v` should be compiled by enumerating the argument's discrete
-- support (marginalising over a random draw). This requires:
--   * the applied function is conditional (its body is enumerable-compilable, not
--     something forward chaining must algebraically invert), and
--   * the argument is a *probabilistic* discrete draw -- it carries DiscreteValues and
--     is not Deterministic. The Deterministic exclusion is essential: a constant or
--     deterministic input (e.g. `dice 4.0`, where `4.0` carries a DiscreteValues tag)
--     is a fixed value with nothing to marginalise over, and must take the ordinary
--     application path instead of being enumerated.
--   * the application is saturated -- its result is a value, not another
--     function. Enumerating a *partial* application would generate a closure and
--     compare it against the sample, which is not a comparison at all (the
--     interpreter rejects it: "Equals can only evaluate on two values").
--     Analysis tags only saturated applications ('SPLL.Analysis.applyTags'),
--     but this is stated here because it is a precondition of enumerating, not
--     a consequence of that. A saturated curried spine whose random argument
--     is the last one is 'curriedEnumerableCallee''s case, not this one.
-- | Peel a curried application spine (@Apply (Apply (Apply f a) b) c@) down to
-- its head and the left-to-right list of arguments applied to it
-- (@(f, [a, b, c])@). Used to build a whole saturated call to a top-level
-- function in one shot instead of one 'IRApply' per source-level argument
-- (task curried-call-spine-needs-optimizer-to-typecheck).
flattenApplySpine :: Expr -> (Expr, [Expr])
flattenApplySpine = go []
  where
    go args (Expr _ (Apply l v)) = go (v : args) l
    go args e = (e, args)

-- | The lambda that forward chaining resolves a chain name to. These sites are
-- reached only after the clause set has established the equivalence, so a miss
-- (or a non-lambda) means chaining and compilation disagree.
-- Returns (resolved chain name, bound variable, body chain name, invocation tag).
equivalentLambda :: String -> FCData -> ChainName -> (ChainName, String, ChainName, String)
equivalentLambda ctx fcd cn = case findEquivalentExpression fcd cn of
  Just (rCN, LambdaInfo boundVar bodyCN, tag) -> (rCN, boundVar, bodyCN, tag)
  other -> error (ctx ++ ": chain name '" ++ cn ++ "' should resolve to a lambda, but resolved to " ++ show other)

-- | One probabilistic application @l v@, resolved to the parameter it binds,
-- whatever the head: a lambda in place (a @draw@), a named function, a function
-- parameter or a let-bound lambda (task binding-resolver-one-application-rule,
-- design law-carrying-modality §C). Every engine of the probabilistic 'Apply'
-- arm reads its application through this record, so they agree on what is
-- bound and on where its body may be compiled.
--
-- Nothing is inlined in the AST: the body is the resolved lambda's own, and
-- the per-invocation identity is the one forward chaining already gives the
-- call ('bindTag').
data Binding = Binding
  { bindHead   :: Expr
    -- ^ The callee as written.
  , bindArg    :: Expr
    -- ^ The argument.
  , bindLambda :: ChainName
    -- ^ The lambda forward chaining resolves the head to (untagged).
  , bindVar  :: String
    -- ^ Its parameter.
  , bindBodyCN :: ChainName
    -- ^ Its body (untagged).
  , bindTag    :: String
    -- ^ The invocation tag forward chaining copied the body's clauses under,
    -- @""@ for a lambda in place. It names forward chaining's per-call
    -- inversion variables and nothing else: no engine decides on it.
  , bindOccs   :: [ChainName]
    -- ^ The parameter's occurrences in the body.
  , bindBody   :: Expr
    -- ^ The body, as the engines compile it: the resolved lambda's own
    -- ('bindBodyCN'), or for a leading-argument binding the call it was taken
    -- from ('leadingArgBinding').
  , bindOuterVars :: [String]
    -- ^ The parameters of a function-valued body ('unwrapLambdas'), which the
    -- result is wrapped back into.
  , bindLeadingArg :: Bool
    -- ^ Whether this binds a random leading argument of a call, taken first
    -- ('leadingArgBinding').
  , bindScope  :: Maybe [(String, Expr)]
    -- ^ How the body is made meaningful at this call site: the enclosing
    -- parameters it reads, each paired with the spine argument binding it
    -- (deterministic given the enclosing recovered variables), to be bound
    -- under fresh names ('enterBindingScope'). @Just []@ for a body that reads
    -- nothing but its parameter and names in scope here -- a lambda in place,
    -- a top-level function's outermost lambda, a closed lambda reached through
    -- a function parameter. 'Nothing': it reads a variable this call site
    -- cannot bind (a leading parameter whose argument is random, or a lambda
    -- closing over a scope this one never entered).
  , bindTopLevel :: Maybe String
    -- ^ The top-level function whose lambda spine holds the resolved lambda.
    -- Its body is never compiled inline as a body factor, because a top-level
    -- function may be recursive and inlining a recursive body at compile time
    -- does not terminate: the body factor is a call of the callee's own
    -- inference function instead (the greatest-fixpoint summary's runtime
    -- counterpart), or nothing.
  }

-- | The expression carrying a chain name, looked up in the program being compiled.
exprWithCN :: CompilerMetadata -> ChainName -> Expr
exprWithCN meta cn =
  let Program{functions=fs} = compilingProgram meta
  in findExprWithCN (map snd fs) cn

-- | The compiler's binder environment ('lawEnv'), by variable.
type LawEnv = Map.Map String BoundVar

-- | A variable bound by an enclosing binder: the law the modality engine had
-- for it there, and what the engine compiling its binding did with it.
data BoundVar = BoundVar
  { bvLaw :: Law
  , bvForm :: Maybe AffineForm
    -- ^ Marginalised as an affine Gaussian form (task
    -- affine-gaussian-closure-lost-across-let-bindings; design
    -- affine-gaussian-forms): the form's coefficients, as IR. Which bindings
    -- those are is their certificate's call ('affineMarginalisable' reads the
    -- argument's 'JAffine' law); this holds only the IR the certificate has no
    -- room for. Such a variable has no runtime value in the emitted code: it
    -- is only ever read through 'affineFormOf', inside the one Gaussian
    -- density leaf that consumes it.
  , bvRecovered :: Bool
    -- ^ Fixed by an enclosing engine: a point-inversion witness, an
    -- enumeration loop, a residue factor. It holds one value, so a body is
    -- re-inferred with it 'Exact' ('reinferRecovered'). Body expressions are
    -- re-fetched from the (original) program at every fold level, so the
    -- re-inference is replayed with the full set.
  }

-- | A variable at its law, nothing done with it yet.
boundAt :: Law -> BoundVar
boundAt l = BoundVar l Nothing False

-- | The modality engine's environment: the laws of 'lawEnv'.
envLaws :: CompilerMetadata -> ModalityInfer.Env
envLaws = Map.map bvLaw . lawEnv

-- | The variables an enclosing engine has fixed ('bvRecovered').
recoveredVars :: CompilerMetadata -> [String]
recoveredVars meta = [ v | (v, bv) <- Map.toList (lawEnv meta), bvRecovered bv ]

-- | Record these variables as fixed ('bvRecovered'). One no binder put in
-- 'lawEnv' (an engine's own loop variable) enters at a point law.
recoverVars :: [String] -> CompilerMetadata -> CompilerMetadata
recoverVars ns meta = meta { lawEnv = foldr (Map.alter (Just . maybe fresh mark)) (lawEnv meta) ns }
  where
    fresh = (boundAt (bareLawOfPType Deterministic)) { bvRecovered = True }
    mark bv = bv { bvRecovered = True }

-- | Record variable @x@ as marginalised with this affine form ('bvForm'). One
-- no binder put in 'lawEnv' (a callee's parameter the affine algebra enters,
-- 'affineCallForm') enters at a Gaussian law.
marginaliseAs :: String -> AffineForm -> CompilerMetadata -> CompilerMetadata
marginaliseAs x f meta = meta { lawEnv = Map.alter (Just . maybe fresh mark) x (lawEnv meta) }
  where
    fresh = (boundAt (bareLawOfPType PNormal)) { bvForm = Just f }
    mark bv = bv { bvForm = Just f }

-- | The metadata for compiling a binding's body: its parameter, under the
-- name @var@ the body reads it by, bound in 'lawEnv' at the argument's law,
-- by the modality engine's own binder rule. The argument's law is its node
-- certificate ('lawTable'); an argument the table does not hold (a node an
-- engine synthesized) is taken at the law its annotation projects.
withBindingLaw :: CompilerMetadata -> Binding -> String -> CompilerMetadata
withBindingLaw meta b var = meta { lawEnv = Map.insert var (boundAt varLaw) (lawEnv meta) }
  where
    varLaw = Map.findWithDefault (bareLawOfPType (pType (getTypeInfo (bindArg b)))) var
               (bindingLawEnv (reinferContext meta) headCN var (bindArg b) argLaw (envLaws meta))
    headCN = chainName (getTypeInfo (bindHead b))
    argLaw = nodeLaw meta (bindArg b)

-- | The value a node's certificate ('nodeLaw') fixes it to, when it is a
-- point mass of statically known value and not itself a literal (whose own
-- equations measure it), nor a function. A NaN point (@Infinity -
-- Infinity@) is left to the node's own equations: like the optimizer's
-- folds ('IROptimizer.isNaNResult'), the compiler never embeds a NaN
-- literal, which the optimizer's fixpoint test would compare unequal to
-- itself forever.
lawPoint :: CompilerMetadata -> Expr -> Maybe Value
lawPoint meta e@(Expr ti nd)
  | Constant _ <- nd = Nothing
  | isTArrowType (rType ti) = Nothing
  | otherwise = mfilter (not . hasNaN) (lawValue (nodeLaw meta e))
  where
    -- Structured values hold their floats at any depth; a symbol spelt
    -- "NaN" only costs the shortcut.
    hasNaN v = "NaN" `isInfixOf` show v

-- | A node's certificate ('lawTable'), or for a node the table does not hold
-- (one an engine synthesized), the law its annotation projects.
nodeLaw :: CompilerMetadata -> Expr -> Law
nodeLaw meta e = fromMaybe (bareLawOfPType (pType ti)) (Map.lookup (chainName ti) (lawTable meta))
  where ti = getTypeInfo e

-- | The marginal operand of the marginal-minus-point split ('mixSubP' of this
-- and the excepted point's result): 'toIRInferenceSave' at the wildcard sample
-- 'VAny', without compiling anything. At that sample 'anySafe' answers every
-- field with its default, so for any non-lambda expression the result is the
-- constant (one, dim 0, no branches, possible), and compiling the body only
-- built dead code -- three compiles per level of a nested @==@ chain instead
-- of two (task anyexcept-any-arm-compiled-instead-of-constant). A 'Lambda'
-- still goes through 'toIRInferenceSave', which returns a closure there.
anyMarginal :: CompilerMetadata -> Bool -> Expr -> CompilerMonad PResult
anyMarginal meta cumulative e@(Expr _ (Lambda _ _)) = toIRInferenceSave meta cumulative e (IRConst VAny)
anyMarginal meta _ _ = return (detP (srOne (semiringOf meta)))

-- | The measure of "any value but @ex@" (the 'VAnyExcept' sentinel an @==@ or
-- constructor-test inverse yields on its False polarity): the marginal minus
-- the excepted value's measure ('mixSubP'), both supplied as actions and run
-- in that order. Every marginal-minus-point split goes through here, so the
-- one exception below holds for all of them: when @ex@ is @C ANY ..@ and @C@
-- is its type's only constructor, the pattern covers the whole type and the
-- complement is empty, which is impossible -- not the merely-zero mass the
-- subtraction would compute (task single-ctor-test-false-witness-crashes).
exceptMeasure :: CompilerMetadata -> IRExpr -> CompilerMonad PResult -> CompilerMonad PResult -> CompilerMonad PResult
exceptMeasure meta ex anyM exceptM
  | wholeSoleConstructor (adtDecls meta) ex = return (impossibleP (semiringOf meta))
  | otherwise = do
      anyRes    <- anyM
      exceptRes <- exceptM
      mixSubP (semiringOf meta) (rBranches exceptRes) anyRes exceptRes

-- | Whether a pattern is @C ANY ..@ (every field the wildcard, under any
-- let-bindings a transport wrapped around it) with @C@ the only constructor
-- of its ADT: the pattern then covers every value of the type.
wholeSoleConstructor :: [ADTDecl] -> IRExpr -> Bool
wholeSoleConstructor decls = go []
  where
    go args (IRApply f a) = go (a : args) f
    go [] (IRLetIn _ _ inner) = go [] inner
    go args (IRVar c) =
      all isWild args
        && any (\d -> case constructors d of
                        [(c', fields)] -> c' == c && length fields == length args
                        _ -> False) decls
    go _ _ = False
    isWild (IRConst VAny) = True
    isWild _ = False

-- | Isolate a sub-inference's own let-in bindings into a fresh scope
-- and re-embed them gated on @guards@ -- baking the guard into the bound
-- value via 'closeResult' -- rather than running the action directly in the
-- ambient scope and applying a guard to the returned 'PResult' only
-- afterwards (task recursive-list-prob-missed-cse).
--
-- Every call site of 'toIRInferenceSave'/'toIRInference' below this point
-- that follows its result with a 'guardP' or a 'zipResult'-style runtime
-- selection has exactly this shape: the sub-inference is compiled first,
-- unconditionally, and the guard is layered on top of the finished
-- 'PResult'. That is fine as long as the sub-inference's own let-in
-- bindings stay lexically embedded at their point of use -- which is what
-- 'anySafeShared' does when it declines to share (the 'anySafe' fallback,
-- gated by 'blockIterates'). But 'anySafeShared' may instead choose to
-- SHARE a sub-inference's own bindings, e.g. when they contain a call
-- that is itself expensive or self-recursive (the standard "coin-flip
-- list" pattern, @main = if Uniform>p then [] else X:main@, whose tail
-- field is compiled exactly through this path). Sharing binds the block
-- via a plain 'setVariables' with no guard of its own, in the AMBIENT
-- scope -- which, without this wrapper, is the guard-free scope the
-- caller compiles in, ahead of any 'guardP'/'zipResult' that comes after.
-- A deconstructing inverse applied on the wrong arm crashes
-- (observe-partials-umbrella N1b's reasoning applies here identically),
-- and a self-referential recursive call can fail to terminate.
--
-- Isolating the scope here and re-threading it through
-- 'closeResult' with @guards@ fixes that: whether or not the inner call
-- decides to share, the guard ends up baked inside the returned value
-- itself, so any later, unguarded read of it (another 'setVariables', a
-- CSE'd duplicate, an enclosing combinator's own eager bind) still only
-- evaluates the protected computation when the guard holds.
guardedSubInference :: CompilerMetadata -> [IRExpr] -> CompilerMonad PResult -> CompilerMonad PResult
guardedSubInference meta guards action = do
  o <- scoped action
  closeResult (semiringOf meta) "guarded" guards o

-- | Keep a scope tried for a 'Just': its bindings are emitted when it
-- answered, dropped when it declined.
inlineIfJust :: Open (Maybe a) -> CompilerMonad (Maybe a)
inlineIfJust o = case openValue o of
  Just _  -> inline o
  Nothing -> return Nothing

-- | Recognise a sample that is an 'IRIf' selecting between a plain value and
-- the 'VAnyExcept' placeholder -- the shape 'transportDirect' produces when it
-- substitutes a known True/False polarity into a seeded '==' (or ADT
-- constructor-test) inversion without reducing the 'IRIf' away. Returns
-- (condition, which polarity is the AnyExcept side, the non-AnyExcept arm, the
-- excepted expression), mirroring the destructuring the InjF 'hasAnyExcept'
-- combinator performs on an inverse's own two arms.
anyExceptIfSplit :: IRExpr -> Maybe (IRExpr, Bool, IRExpr, IRExpr)
anyExceptIfSplit (IRIf c pos (IRConst (VAnyExcept [ex]))) = Just (c, False, pos, ex)
anyExceptIfSplit (IRIf c (IRConst (VAnyExcept [ex])) neg) = Just (c, True, neg, ex)
anyExceptIfSplit _ = Nothing

-- | Peel a sample's leading 'IRLetIn' chain (e.g. 'transportDirect's
-- materialised anchors) off to see whether the expression underneath is a
-- 'VAnyExcept' placeholder -- bare, or still 'IRIf'-wrapped ('anyExceptIfSplit').
-- Returns the peeled bindings alongside whichever shape matched, so a caller
-- that reconstructs a result from the pieces inside can re-wrap it in the same
-- bindings (the pieces may reference names those bindings introduce).
anyExceptSampleShape :: IRExpr -> Maybe ([(Varname, IRExpr)], Either IRExpr (IRExpr, Bool, IRExpr, IRExpr))
anyExceptSampleShape sample = case core of
  IRConst (VAnyExcept [ex]) -> Just (binds, Left ex)
  _ | Just split <- anyExceptIfSplit core -> Just (binds, Right split)
  _ -> Nothing
  where
    (binds, core) = stripLetIns sample
    stripLetIns (IRLetIn v val inner) = let (bs, c) = stripLetIns inner in ((v, val) : bs, c)
    stripLetIns e = ([], e)

-- | True for a function type, i.e. an expression that evaluates to a callable
-- rather than to a value a density can be taken of.
isTArrowType :: RType -> Bool
isTArrowType (TArrow _ _) = True
isTArrowType _            = False

failConversion :: Expr -> IRExpr
failConversion = error "Cannot convert VClosure"

-- Bind the forward-chaining anchors a generated inverse lands on. An anchor
-- chain name that appears free in the inverse (e.g. a ThetaI/Subtree operand FC
-- inverted through) is not bound by the wrapping sample lambda, so we materialise
-- its value from the anchor node's generate-mode IR and let-bind it. Plain
-- constants need no binding (they render as IRConst); only non-constant anchors
-- show up free here (modality-split-forwardchaining, anchor wiring).
materializeAnchors :: CompilerMetadata -> IRExpr -> CompilerMonad IRExpr
materializeAnchors meta expr = foldM bindAnchor expr usedAnchors
  where
    usedAnchors = filter (`freeInIR` expr) (Set.toList (fcAnchors (fcData meta)))
    fns = map snd (functions (compilingProgram meta))
    -- The free var is a (possibly invocation-tagged) anchor chain name; the
    -- source node to generate its value from is the untagged original.
    bindAnchor irBody cn = do
      anchorIR <- toIRGenerate meta (anchorAtCall meta (getTag cn) (findExprWithCN fns (untag cn)))
      return (IRLetIn cn anchorIR irBody)

-- | An anchor node as its value is computed at this call site. An anchor in a
-- callee's per-invocation copy (tag @t@) reads the callee's parameters, which
-- are not in scope here: each such occurrence is replaced by the argument
-- the invocation passed ('boundArgument'), itself resolved the same way where
-- the call sits in another copied body. Going by the clause rather than by
-- name is what keeps the anchor from reading whatever the caller happens to
-- bind under the parameter's name, or crashing on an unbound name when it
-- binds none (task callee-body-name-sensitive-across-call).
--
-- A variable bound inside the copied body itself (a @draw t2 = ts in ..@
-- around the anchor) has its clause only untagged: the copy follows the
-- equivalences of the nodes it chains through, and the anchor is not one of
-- them. Its value lies in the same function body as the occurrence, so in
-- the same per-invocation copy, and is resolved under the same tag. A value
-- in another function's body is not: tags are only unique per function, so
-- the tag is never carried across one (task
-- theta-anchor-through-callee-local-binding).
--
-- An untagged anchor sits in the scope being compiled and is left as it is,
-- except where it lies in a callee body an engine entered here
-- ('enteredScopes'): there a leading parameter is read under its fresh
-- name, and a variable the body binds itself by its value, which the
-- materialized anchor is not under the binder of.
anchorAtCall :: CompilerMetadata -> String -> Expr -> Expr
anchorAtCall meta "" e0 = go Set.empty e0
  where
    go bound e@(Expr t (Var n))
      | not (n `Set.member` bound)
      , (nodes, renames) : _ <- [ sc | sc@(nodes, _) <- enteredScopes meta, cn `Set.member` nodes ]
      = case boundArgument (fcData meta) cn of
          Just valCN | valCN `Set.member` nodes -> anchorAtCall meta "" (exprWithCN meta valCN)
          _ -> Expr t (Var (fromMaybe n (lookup n renames)))
      where cn = chainName (getTypeInfo e)
    go bound (Expr t (Lambda x b)) = Expr t (Lambda x (go (Set.insert x bound) b))
    go bound (Expr t f) = Expr t (fmap (go bound) f)
anchorAtCall meta tag e0 = go Set.empty e0
  where
    go bound e@(Expr _ (Var n))
      | not (n `Set.member` bound)
      , Just argCN <- boundArgument (fcData meta) (cn ++ tag)
      = anchorAtCall meta (getTag argCN) (exprWithCN meta (untag argCN))
      | not (n `Set.member` bound)
      , Just valCN <- boundArgument (fcData meta) cn
      , null (getTag valCN)
      , Just f <- functionOf cn
      , functionOf valCN == Just f
      = anchorAtCall meta tag (exprWithCN meta valCN)
      where cn = chainName (getTypeInfo e)
    go bound (Expr t (Lambda x b)) = Expr t (Lambda x (go (Set.insert x bound) b))
    go bound (Expr t f) = Expr t (fmap (go bound) f)
    functionOf cn = listToMaybe
      [ f | (f, fBody) <- functions (compilingProgram meta), cn `Set.member` nodeChainNames fBody ]

-- | The chain names of every node of an expression.
nodeChainNames :: Expr -> Set.Set ChainName
nodeChainNames e = Set.insert (chainName (getTypeInfo e)) (Set.unions (map nodeChainNames (getSubExprs e)))

-- | Discrete value-equality / step-CDF masses (used both for a deterministic
-- Constant's cumulative "0 below, 1 at-or-above" step function and for
-- equality indicators), built as semiring one/zero rather than the literal
-- linear 1.0/0.0 so it stays correct under 'logSpace' (task
-- log-space-probability-computation).
--
-- A scalar wildcard in the sample bounds nothing: P(v <= ANY) is the semiring
-- one, tested before the comparison reads the sentinel. The root wildcard is
-- answered by 'anySafe', but one inside a tuple reaches here whenever the
-- sample was built by an inverse rather than queried -- @snd@'s inverse puts
-- ANY in the slot it discards (fuzz-admission-oracle-bugs item 5). The test
-- folds away wherever the sample component is statically concrete.
compareValueExpr :: Semiring -> RType -> IRExpr -> IRExpr -> IRExpr
compareValueExpr sr TFloat v sample = anyBoundsNothing sr sample (IRIf (IROp OpLessThan sample v) (srZero sr) (srOne sr))
compareValueExpr sr TInt v sample = anyBoundsNothing sr sample (IRIf (IROp OpLessThan sample v) (srZero sr) (srOne sr))
compareValueExpr sr TBool v sample = anyBoundsNothing sr sample (IRIf (IROp OpAnd (IRUnaryOp OpNot sample) v) (srZero sr) (srOne sr))
compareValueExpr sr TUnit _ _ = srOne sr
-- A compound slot can be the wildcard as a whole (@fst@'s inverse discards a
-- tuple- or Either-valued second component as one ANY), so it is tested before
-- the comparison destructures it (task cdf-fst-of-nested-tuple-indexes-any).
compareValueExpr sr (Tuple ft st) v sample = anyBoundsNothing sr sample $ srTimes sr (compareValueExpr sr ft (IRDestruct AcFst v) (IRDestruct AcFst sample)) (compareValueExpr sr st (IRDestruct AcSnd v) (IRDestruct AcSnd sample))
compareValueExpr sr (TEither lr rr) v sample = anyBoundsNothing sr sample $
  IRIf (IRDestruct AcIsLeft v)
    (IRIf (IRDestruct AcIsLeft sample) (compareValueExpr sr lr (IRDestruct AcFromLeft v) (IRDestruct AcFromLeft sample)) (srZero sr))
    (IRIf (IRDestruct AcIsRight sample) (compareValueExpr sr rr (IRDestruct AcFromRight v) (IRDestruct AcFromRight sample)) (srZero sr))
compareValueExpr sr (TVarR _) v sample = anyBoundsNothing sr sample (IRIf (IROp OpLessThan sample v) (srZero sr) (srOne sr))
-- A list is ordered componentwise, as the CDF of a random Cons chain is the
-- product of its element CDFs ('toIRInference''s field-constructor case): a
-- list is below the sample when the two have the same length and every
-- element is below the sample's. A deterministic list whose spine is static
-- ('listSpine': a literal, a Cons chain) is compared element by element, so a
-- wildcard tail the sample carries bounds nothing -- @head@'s inverse asks
-- @P(head xs <= x)@ as @xs <= x : ANY@, which the equality indicator answered
-- as @head xs == x@ (task head-cdf-uses-equality). The empty list, and a list
-- whose spine is only known at run time, keep the equality indicator.
compareValueExpr sr rt@(ListOf et) v sample = case listSpine v of
  Just (h, t) -> anyBoundsNothing sr sample
    (IRIf (IROp OpEq sample (IRConst (VList EmptyList))) (srZero sr)
      (srTimes sr (compareValueExpr sr et h (IRDestruct AcHead sample))
                  (compareValueExpr sr rt t (IRDestruct AcTail sample))))
  Nothing -> anyBoundsNothing sr sample (maskSR sr (IROp OpEq sample v))
-- RInfer types a literal @[]@ as @[a]@ with a fresh @a@
-- ('SPLL.Typing.RInfer.freshenNullLists'), so 'NullList' should no longer
-- survive typing; an annotation built from 'getRType' outside RInfer can still
-- carry it. Its only inhabitant is the empty list, so it takes the same
-- equality indicator as 'ListOf' (task comparevalueexpr-nulllist-cdf-gap).
compareValueExpr sr NullList v sample = maskSR sr (IROp OpEq sample v)
-- An ADT carries no order, so there is nothing for a CDF to integrate along.
-- This case and the TSymbol one below are refusals rather than gaps: every call
-- site is on the @cumulative = True@ path, so reaching it means a cdf() query was
-- asked of an ADT-valued program. See 'adtCdfMessage'.
compareValueExpr _ (TADT n) _ _ = IRError (adtCdfMessage n)
-- A Symbol is unordered too, so it gets the same treatment as an ADT. Here it is
-- also routine to build the comparison: a helper that returns a Symbol (picking
-- a board image by index, say) gets an integrate variant like every other
-- function, so this has to compile to an IRError that only fires when it is
-- called. The callers' own CDFs, over ordered types, don't call it (task
-- symbol-selected-by-helper-crashes-cdf-compile).
compareValueExpr _ TSymbol _ _ = IRError symbolCdfMessage
-- A function is unordered as well. The leaf sites that would compare a whole
-- function value refuse statically (see the arrow-typed InjF equation of
-- 'toIRInference'); what still gets here is a function in a component of a
-- tuple or Either reached some other way, whose sample slot may be a wildcard
-- an inverse put there -- then it bounds nothing, as for a scalar -- or a
-- concrete closure, which no CDF is defined over (task
-- function-value-compared-in-probability-mode).
compareValueExpr sr (TArrow _ _) _ sample = anyBoundsNothing sr sample (IRError functionCdfMessage)
-- A tensor has no CDF here either: its order would be the componentwise one,
-- which nothing compiles (task tensor-gaussian-heads-rd-diffusion). Built
-- routinely -- a trajectory of tensors gets an integrate variant like any list
-- -- so it is a runtime error that fires only when a cdf() reaches it.
compareValueExpr sr (TTensor _ _) _ sample = anyBoundsNothing sr sample (IRError tensorCdfMessage)

-- Invariant, not a refusal (task static-refusals-become-absent-variants): a CDF comparison is only built for first-order result types.
compareValueExpr _ rt _ _ = error $ "Comparison not implemented for type: " ++ show rt

-- | The atoms of a Float-valued node whose 'DiscreteValues' tag is a finite
-- set of finite Float constants, ascending; Nothing for an Int, a continuous
-- or mixed node, an untagged one, or one with an infinite or NaN atom. The tag may over-approximate the support,
-- which is harmless to 'atomBelow'/'atomAbove': a value with no mass between
-- two atoms changes no CDF.
discreteFloatAtoms :: Expr -> Maybe [Double]
discreteFloatAtoms e
  | rType ti == TFloat
  , [MultiDiscretes vs@(_:_)] <- [mv | DiscreteValues mv <- tags ti]
  , Just ds <- mapM asFloat vs
  = Just (sort (nub ds))
  | otherwise = Nothing
  where ti = getTypeInfo e
        -- Finite atoms only: an infinite one has no neighbour beyond it to
        -- stand for "below every atom", and a NaN constant compares unequal
        -- to itself, so the optimizer's fixpoint over IR equality never
        -- settles on it (it hung on known-issues/nanOperandComparisonThroughCdf).
        asFloat (VFloat d) | not (isNaN d || isInfinite d) = Just d
        asFloat _ = Nothing

-- | IR for the largest atom strictly below @e@, or a value below every atom
-- when there is none: the point whose CDF is the mass strictly below @e@.
atomBelow :: [Double] -> IRExpr -> CompilerMonad IRExpr
atomBelow [] e = return e
atomBelow ds@(d0:_) e = shareBound e $ \x ->
  foldl (\acc d -> IRIf (IROp OpLessThan (floatAtom d) x) (floatAtom d) acc) (floatAtom (d0 - 1)) ds

-- | IR for the smallest atom strictly above @e@, or a value above every atom
-- when there is none.
atomAbove :: [Double] -> IRExpr -> CompilerMonad IRExpr
atomAbove [] e = return e
atomAbove ds e = shareBound e $ \x ->
  foldr (\d acc -> IRIf (IROp OpGreaterThan (floatAtom d) x) (floatAtom d) acc) (floatAtom (last ds + 1)) ds

floatAtom :: Double -> IRExpr
floatAtom = IRConst . VFloat

-- | Reads a bound several times without copying it: a variable or constant
-- inline, anything else let-bound around the reading expression.
shareBound :: IRExpr -> (IRExpr -> IRExpr) -> CompilerMonad IRExpr
shareBound e@(IRVar _) k = return (k e)
shareBound e@(IRConst _) k = return (k e)
shareBound e k = do
  n <- mkVariable "atom_bound"
  return (IRLetIn n e (k (IRVar n)))

-- | The head and tail of a deterministic non-empty list whose spine is
-- static: a list literal, or a Cons chain, possibly under the lets a
-- generated list literal binds its elements and its tail in (substituted:
-- the value is deterministic, so where a binding is read twice, evaluating
-- it twice changes nothing). Nothing for the empty list and for a list only
-- known at run time.
listSpine :: IRExpr -> Maybe (IRExpr, IRExpr)
listSpine (IRConst (VList (ListCont x rest))) = Just (IRConst x, IRConst (VList rest))
listSpine (IRConstruct TgCons [h, t]) = Just (h, t)
listSpine (IRLetIn n e b) = listSpine (substIRVar n e b)
listSpine _ = Nothing

-- | The runtime diagnostic for a cdf() query that reaches a function-valued component.
functionCdfMessage :: String
functionCdfMessage =
  "cdf(): no cumulative distribution is defined over a function value -- functions "
  ++ "carry no order to integrate along."

-- | The runtime diagnostic for a cdf() query that reaches a Symbol-valued node.
tensorCdfMessage :: String
tensorCdfMessage =
  "cdf(): no cumulative distribution is defined over a tensor value -- its "
  ++ "componentwise order is not compiled. Use p() for a point query on this value."

symbolCdfMessage :: String
symbolCdfMessage =
  "cdf(): no cumulative distribution is defined over a Symbol -- symbols carry "
  ++ "no order to integrate along. Use p() for a point query on this value."

-- | See 'compareValueExpr': a wildcard sample component is the whole mass.
anyBoundsNothing :: Semiring -> IRExpr -> IRExpr -> IRExpr
anyBoundsNothing sr sample = IRIf (IRUnaryOp OpIsAny sample) (srOne sr)

-- | Bool-valued IR: is deterministic value @v@ equal to @sample@? This is the
-- equality analogue of 'compareValueExpr' (which builds a '<='-style CDF
-- indicator): a continuous leaf (TFloat/TVarR) recovered via inverse
-- arithmetic is one ulp away from the query point far more often than it is
-- bit-identical, so it is compared with 'OpApprox' (floatApproxEqThresh,
-- 1e-10 -- well inside the .tst harness's 1e-4 probTolerance) rather than
-- bit-exact 'OpEq'. Discrete/exact types (Bool, Int, ListOf, TADT, Symbol)
-- keep bit-exact 'OpEq': their values are never fp-recovered, so exactness is
-- both correct and cheaper. Tuple/Either recurse structurally so a compound
-- value's float leaves get the approximate treatment too, mirroring
-- compareValueExpr's own recursion shape.
--
-- Every recursion step of 'equalityGuard' additionally wraps an Any-wildcard
-- guard around itself first: the plain 'OpEq'/'OpApprox' this replaces relied
-- on a single flat comparison whose runtime semantics (IRInterpreter's
-- 'cmp', pythonLib's 'T'/'Left'/'Right' '__eq__') already treat a VAny
-- operand at *any* depth as an automatic match (a partial marginal query
-- like @p((0.5, ANY))@ or @p(Left ANY)@). Once the comparison is decomposed
-- into per-field IR (IRDestruct AcFst/AcFromLeft), that recursive Any-awareness must
-- be rebuilt explicitly at each step, or a nested ANY reaches a leaf
-- comparison op that errors (OpApprox on a non-float) or silently returns
-- False (OpEq's own base case treats VAny as never equal to anything --
-- correct as a *fallback*, wrong as the first thing tried). The guard is
-- spelled as nested 'IRIf', never 'IROp OpOr'/'OpAnd': both operands of an
-- IR boolean op are evaluated, and the real comparison beneath the guard is
-- exactly the op that would crash on a genuine VAny operand.
--
-- 'equalityGuardStatic' is the same structural recursion without that guard,
-- for the plan-guided-lazy-enumeration caller ('planDetGuard'): it builds
-- purely compile-time constraint IR over concrete plan values that are never
-- themselves a runtime VAny, and the Any-check nodes confuse that engine's
-- own static analysis of the guard IR (occurrence counting for accessor
-- pruning) -- adding it there produced spurious "constructor ... not present
-- in the plan" refusals on the plan-enum corpus without fixing anything the
-- guard is for. The set-witness engine's 'memberGuard' used to share it and
-- no longer does: its point is a projection of the query sample, which a
-- marginal query does make a runtime VAny (see there).
equalityGuard :: RType -> IRExpr -> IRExpr -> IRExpr
--
-- The sample is tested first, and a tuple @v@ builds syntactically (under
-- its let-bindings) is compared field by field, each field under its own
-- let-bindings only: an observed wildcard constrains nothing, and the part of
-- @v@ it observes need not be evaluable there. A residue factor fixes a bound
-- variable at a wildcard witness ('transportDirect'), and @(x + 0.0, 1.0)@ at
-- @x = ANY@ against @(ANY, 1.0)@ evaluated @x + 0.0@ -- a raw type error --
-- to test the whole tuple, and again to project its second field (task
-- any-slot-through-injf-inverse-reaches-condition). A constructed tuple is
-- never itself a wildcard, so its own 'OpIsAny' test is not needed.
equalityGuard rt v sample =
  IRIf (IRUnaryOp OpIsAny sample) constTrueIR $ case (rt, constructedTuple v) of
    (Tuple ft st, Just (wrap, a, b)) ->
      IROp OpAnd (equalityGuard ft (wrap a) (IRDestruct AcFst sample))
                 (equalityGuard st (wrap b) (IRDestruct AcSnd sample))
    _ -> IRIf (IRUnaryOp OpIsAny v) constTrueIR (equalityGuardBody equalityGuard rt v sample)
  where
    constructedTuple (IRConstruct TgTuple [a, b]) = Just (id, a, b)
    -- A nested tuple's field is its own let-bound construction.
    constructedTuple (IRLetIn n e (IRVar n')) | n == n' = constructedTuple e
    constructedTuple (IRLetIn n e inner) = do
      (wrap, a, b) <- constructedTuple inner
      return (pruneDeadLetIns . IRLetIn n e . wrap, a, b)
    constructedTuple _ = Nothing

equalityGuardBody :: (RType -> IRExpr -> IRExpr -> IRExpr) -> RType -> IRExpr -> IRExpr -> IRExpr
equalityGuardBody _    TFloat    v sample = leafEqIR TFloat sample v
equalityGuardBody _    rt@(TVarR _) v sample = leafEqIR rt sample v
equalityGuardBody _    TUnit _ _ = constTrueIR
equalityGuardBody self (Tuple ft st) v sample =
  IROp OpAnd (self ft (IRDestruct AcFst v) (IRDestruct AcFst sample)) (self st (IRDestruct AcSnd v) (IRDestruct AcSnd sample))
equalityGuardBody self (TEither lr rr) v sample =
  IRIf (IRDestruct AcIsLeft v)
    (IRIf (IRDestruct AcIsLeft sample) (self lr (IRDestruct AcFromLeft v) (IRDestruct AcFromLeft sample)) (IRConst $ VBool False))
    (IRIf (IRDestruct AcIsLeft sample) (IRConst $ VBool False) (self rr (IRDestruct AcFromRight v) (IRDestruct AcFromRight sample)))
-- A function has no equality (the IR contract's 'OpEq' takes none, and the
-- interpreter has no case for a closure). A function in a component of a
-- tuple or Either is compared only where its query slot is not a wildcard,
-- and no query value holds a concrete closure, so this is a run-time error
-- that a reachable comparison would raise, as the cdf's is
-- ('functionCdfMessage'). Before, @(\y -> (\x -> x, y)) 1.0@ at
-- @(ANY, 1.0)@ emitted @fst sample == fst v@ at the function type behind the
-- slot's wildcard test (task ir-contract-violations-in-compiler-output).
equalityGuardBody _    (TArrow _ _) _ _ = IRError functionProbMessage
equalityGuardBody _    _ v sample = IROp OpEq sample v

-- | The runtime diagnostic for a p() query that compares a function-valued component.
functionProbMessage :: String
functionProbMessage =
  "p(): no probability is defined at a function value -- functions carry no "
  ++ "equality to compare a query value against."

-- | Bool-valued IR comparing two leaves of type @rt@ (callers pass the query
-- sample first). A float is compared with 'OpApprox' (see 'equalityGuard' for
-- why), anything with an exact representation with 'OpEq'.
--
-- A type variable is neither: nothing in the function constrained it, so the
-- value may be a float at one call and a Bool, Int, tuple or ADT at another.
-- 'OpApprox' is defined on floats only (the interpreter refuses anything
-- else), and 'OpEq' alone would lose the tolerance for a float the caller
-- computed, so it dispatches on the run-time tag of @a@ (task
-- polymorphic-parameter-compared-as-float). 'IRConformsTo' accepts a wildcard
-- as a float, so an ANY operand reaches 'OpApprox' exactly as it did before
-- this dispatch existed; callers keep owning the ANY guard. The batched
-- backend emits the tag test as a bucket-uniform dtype check
-- ('SPLL.CodeGenPyTorchBatched.structural').
leafEqIR :: RType -> IRExpr -> IRExpr -> IRExpr
leafEqIR TFloat    a b = IROp OpApprox a b
leafEqIR (TVarR _) a b = IRIf (IRConformsTo ITFloat a) (IROp OpApprox a b) (IROp OpEq a b)
leafEqIR _         a b = IROp OpEq a b


-- Must be used in conjunction with irMap, as it does not recurse
uniqueify :: [Varname] -> String -> IRExpr -> IRExpr
uniqueify vars prefix (IRVar name) | name `elem` vars = IRVar (prefix ++ name)
uniqueify vars prefix (IRLetIn name boundExpr bodyExpr) | name `elem` vars = IRLetIn (prefix ++ name) (uniqueify vars prefix boundExpr) (uniqueify vars prefix bodyExpr)
-- 'SPLL.Semiring.enumSumNode'/'enumSumP' build an enumerated reduction as
-- 'IRBuiltin BMap [IRLambda v body, ...]', reusing the SAME enumeration
-- variable name as the 'IRLambda's binder. Without this case, 'irMap's generic
-- descent (this function relies on for recursion -- see the comment above)
-- renames free occurrences of that name inside 'bodyExpr' (correctly, per the
-- 'IRVar' case above) while leaving the 'IRLambda' binder untouched, splitting
-- one identifier into two: every *use* of the loop variable pointed at a name
-- nothing bound any more. Added for the max-product semiring, whose reduction
-- was the first built in tensor form (testCases/applyEnumOperandPair.ppl under
-- '--semiring=map' is the canary); task retire-irenumsum made every enumerated
-- reduction that shape, so it now guards the whole double-enumeration
-- ('applyUnique') site rather than one semiring's corner of it.
uniqueify vars prefix (IRLambda name bodyExpr) | name `elem` vars = IRLambda (prefix ++ name) (uniqueify vars prefix bodyExpr)
uniqueify _ _ e = e
