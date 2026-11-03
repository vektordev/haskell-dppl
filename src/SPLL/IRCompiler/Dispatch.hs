-- | The engine dispatch: the declared engine list ('dispatchEngines'), each
-- engine's applicability, and applying a 'Binding' ('applyBinding').
module SPLL.IRCompiler.Dispatch (
  calleeInferenceName,
  applyBinding
) where

import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Typing.PType
import Data.Maybe
import Data.List (isPrefixOf)
import Data.Functor ((<&>))
import SPLL.Typing.ForwardChaining
import SPLL.Typing.ModalityInfer (Engine(..), engineOrder, engineLabel)
import Control.Applicative ((<|>))
import SPLL.Semiring
import Control.Monad (foldM, forM, when)
import Debug.Trace (traceM)
import Control.Monad.Except (catchError)
import qualified Data.Set as Set
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Gaussian
import SPLL.IRCompiler.Worlds
import SPLL.IRCompiler.Plan

-- | Does this expression contain a @let@ (an applied literal lambda) whose
-- bound value is still random? That is the shape the witnessed-let fold in
-- 'toIRInference' nests through, one body factor inside another, and so the
-- shape whose body factor it binds once rather than inlines per field.
holdsProbabilisticLet :: Expr -> Bool
holdsProbabilisticLet e = case e of
  Expr _ (Apply (Expr _ (Lambda _ _)) v) | pType (getTypeInfo v) /= Deterministic -> True
  _ -> any holdsProbabilisticLet (getSubExprs e)

-- | The compiled inference function a call to top-level function @n@ must
-- reference, given the semiring the CALLER is being compiled under.
--
-- Under the default family this is exactly the @n ++ "_prob"@ / @n ++ "_integ"@
-- it has always been. Under an 'extraSemirings' family it is that family's own
-- group for the callee (@n ++ "_map_prob"@), because otherwise the call falls
-- back to the callee's sum-product group and the requested semiring silently
-- stops applying at the first function boundary -- see 'semiringGroupInfix' for
-- the measured symptom.
--
-- Cumulative position under a non-default family is REFUSED rather than
-- mis-routed: an extra-semiring group deliberately has no @integFun@ at all
-- (a CDF has no settled meaning under max-product -- see 'extraFunGroups'), so
-- there is no @n ++ "_map_integ"@ to call. Failing loudly here is the same
-- choice 'mixSubP' makes (refusing the variant) for AnyExcept under MAP; the
-- alternative is emitting a reference to a function that was never generated.
calleeInferenceName :: CompilerMetadata -> Bool -> String -> CompilerMonad String
calleeInferenceName meta cumulative n = case semiringFamily meta of
  SRSumProduct -> return (n ++ (if cumulative then "_integ" else "_prob"))
  fam
    | cumulative -> refuse "" ("IRCompiler: this program takes a cumulative (CDF) "
        ++ "query through a call to the top-level function " ++ show n ++ ", which has "
        ++ "no defined meaning under the " ++ show fam ++ " semiring: an extra-semiring "
        ++ "function group is compiled in probability mode only, so there is no "
        ++ show (n ++ semiringGroupInfix fam ++ "_integ") ++ " to call. Compile this "
        ++ "program without requesting that semiring, or inline the call.")
    | otherwise -> return (n ++ semiringGroupInfix fam ++ "_prob")

-- | One engine of a probabilistic application: its name, and, where it
-- applies, its construction, which takes the diagnostic an earlier engine
-- that declined left and either declines in turn ('Left', with its own) or
-- answers.
type BindingEngine = (String, Maybe (Maybe String -> CompilerMonad (Either (Maybe String) PResult)))

-- | Try the engines in order, first applicable wins ('applyBinding'); a
-- construction that declines hands on to the next applicable one. @none@
-- answers when every engine is inapplicable or declined.
--
-- Under @-v@ it names the engine a binding compiled from (@onAnswer@), which
-- can differ from the first one the modality engine's report lists: that one
-- may decline here.
dispatchEngines :: (String -> CompilerMonad ()) -> [BindingEngine] -> (Maybe String -> CompilerMonad PResult) -> CompilerMonad PResult
dispatchEngines onAnswer engines none = go Nothing engines
  where
    go diag [] = none diag
    go diag ((_, Nothing) : rest) = go diag rest
    go diag ((name, Just run) : rest) =
      run diag >>= either (\d -> go (d <|> diag) rest) (\r -> onAnswer name >> return r)

-- | The in-place engine's applicability to a binding, and the expression it
-- compiles: a lambda in place whose body reads its variable once, with no
-- binder on the way ('readOnceInPlace', the predicate of the modality
-- engine's 'CertInPlace'), is the body with the argument at that read. The
-- read has the argument's own law, so this is the binding's meaning, not a
-- rewrite of it; it is the last engine, for bindings no other one measures
-- ('dispatchEngines').
--
-- Only a body compiled inline here qualifies ('bindInline', no invocation
-- tag, no leading argument, not function-valued): the body handed to the
-- engines is then the lambda's own, and every node it holds on the way to
-- the read is compiled from this tree, not looked up by chain name.
inPlaceApplicable :: RType -> Binding -> Maybe Expr
inPlaceApplicable rt binding
  | bindInline binding, not (bindLeadingArg binding), null (bindTag binding)
  , null (bindOuterVars binding), not (isTArrowType rt)
  , readOnceInPlace (bindVar binding) (bindBody binding)
  = Just (substituteVar (bindVar binding) (bindArg binding) (bindBody binding))
  | otherwise = Nothing

-- | The set-witness engine's applicability to a binding: the shape walk of
-- 'SPLL.Typing.ForwardChaining.worldsShape' over its body, as the modality
-- engine's let rule asks it.
setWitnessApplicable :: CompilerMetadata -> Binding -> Maybe WorldsShape
setWitnessApplicable meta binding =
  worldsShape (WorldsCtx (fcData meta) (adtDecls meta) (functions (compilingProgram meta)) permissiveDet)
              (bindOccs binding) (bindBody binding)

-- | Bind the conditions a point inverse split on ('toInvExprMaybeWith') to
-- their values at this binding: each condition is compiled where the body is
-- made meaningful here ('enterBindingScope'), so a condition reading a
-- leading parameter of the callee (@t < 0.5@ in @step t x@) reads that
-- parameter's argument. 'Nothing' (the engine declines) where the body cannot
-- be entered here, a condition is not in the body this binding compiles, or
-- it reads a parameter of a function-valued body, which is not bound where
-- the inverse is applied.
bindIfConditions :: CompilerMetadata -> Binding -> InvChain -> CompilerMonad (Maybe InvChain)
bindIfConditions meta binding chain = case used of
  [] -> return (Just chain)
  _ -> do
    -- In its own scope: the leading parameters' bindings are folded
    -- into each condition, so a declining binding leaves nothing behind.
    scopeO <- scoped (enterBindingScope meta binding)
    case openValue scopeO of
      Nothing -> return Nothing
      Just (scopeMeta, scopedBody) -> do
        let conds = [ (v, findCond cn scopedBody) | (v, cn) <- used ]
        if any (maybe True readsOuter . snd) conds
          then return Nothing
          else do
            binds <- forM conds $ \(v, c) -> do
              cO <- scoped (toIRGenerate scopeMeta (fromJust c))
              -- Each condition closes over its own copy of the scope's block
              -- (a few parameter bindings), so a declining binding leaves
              -- nothing behind.
              return (v, closeExpr (scopeO *> cO) id)
            let wrap e = foldr (\(v, cIR) acc -> if freeInIR v acc then IRLetIn v cIR acc else acc) e binds
            return (Just chain { invValue = wrap (invValue chain), invCoV = wrap (invCoV chain)
                               , invGuard = wrap (invGuard chain), invReadsAny = wrap (invReadsAny chain)
                               , invCumValue = wrap (invCumValue chain), invCumGuard = wrap (invCumGuard chain) })
  where
    fields = [invValue chain, invCoV chain, invGuard chain, invReadsAny chain, invCumValue chain, invCumGuard chain]
    used = [ vc | vc@(v, _) <- ifConditionVars (fcData meta) (bindTag binding), any (freeInIR v) fields ]
    -- The condition, under the @let@s on the way to it whose variables it
    -- reads: a split reached through a @let@ ('toInvExprMaybeWith') has a
    -- condition that may read the let-bound variable (@draw c = 0.2 < 0.5 in
    -- if c ..@), which the binding's scope does not bind.
    findCond cn e
      | chainName (getTypeInfo e) == cn = Just e
      | Expr ti (Apply (Expr lti (Lambda y b)) v) <- e
      , Just c <- findCond cn b
      = Just (if y `Set.member` freeVarsExpr c then Expr ti (Apply (Expr lti (Lambda y c)) v) else c)
      | otherwise = listToMaybe (mapMaybe (findCond cn) (getSubExprs e))
    readsOuter c = any (`Set.member` freeVarsExpr c) (bindOuterVars binding)

-- | The probabilistic 'Apply' arm's engines, over one resolved application
-- ('Binding'), in dispatch order ('engineOrder'): plan-guided enumeration,
-- point inversion with its body factor, joint affine and affine
-- marginalisation, set-valued witnesses, and in place.
applyBinding :: CompilerMetadata -> Bool -> RType -> Binding -> IRExpr -> CompilerMonad PResult
applyBinding meta cumulative rt binding sample = do
  let clauses = fcData meta
  let localAdts = adtDecls meta
  let Binding{bindHead = l, bindArg = v, bindVar = toInvCN, bindBodyCN = lambdaBodyCN, bindTag = tag} = binding
  let lChainName = chainName (getTypeInfo l)
  -- Whether the body factor is compiled inline (see 'bindInline'); where it
  -- is not, a top-level callee's is a call ('namedCall'), and any other
  -- binding keeps the single witness.
  let inlineBody = bindInline binding
  let (boundVar, _) = unwrapLambdas (fcData meta) lambdaBodyCN
  let lambdaVars = bindOuterVars binding
  let wrapInLambdas ex = foldr IRLambda ex lambdaVars
  do
   -- Plan-guided lazy enumeration (design plan-guided-lazy-enumeration): when
   -- the bound value is a neural network's structured output, its distribution
   -- factorizes per PartitionPlan slot and the observation can be inverted
   -- onto individual plan leaves without ever materializing the support. This
   -- is tried BEFORE point inversion: for the body shapes the plan traversal
   -- supports (accessor chains, is<Ctor>/==/comparison predicates, if splits),
   -- forward chaining's "inverse" routes through the VAnyExcept machinery and
   -- crashes at runtime on ADT accessors — an M0-style silent-failure path —
   -- so interception strictly improves them; bodies the traversal declines
   -- keep their current path untouched.
   -- Whether the bound variable sits in a field of a constructed result. Only
   -- then can forward chaining's witness leave other parts of the body
   -- unaccounted for; a pure invertible chain down to one occurrence is exact
   -- as a single witness, and keeps its emitted code.
   let underField = occursUnderFieldCtor (adtDecls meta) toInvCN (bindBody binding)
   -- A saturated call of a top-level function whose leading arguments are
   -- deterministic: its body factor is the callee's own probability (or, for
   -- a cumulative query, integrate) function at the recovered witness (the
   -- 'namedCall' arm of the result below). Not for a cumulative query of a
   -- call returning a function: its closure arm was built for probability
   -- mode and has no cumulative test, so that shape keeps the single witness.
   let arrowRT = case rt of { TArrow _ _ -> True; _ -> False }
   let namedCall = case flattenApplySpine l of
         (Expr _ (Var fName), fArgs)
           | underField && not (cumulative && arrowRT) && bindTopLevel binding == Just fName
           , all ((== Deterministic) . pType . getTypeInfo) fArgs
           , Just (TArrow _ _, True) <- lookup fName (typeEnv meta) -> Just (fName, fArgs)
         _ -> Nothing
   -- Forward chaining sees through a field constructor in a callee's body.
   -- Where neither the inline fold nor the 'namedCall' arm folds the body
   -- back in, the single-witness branch below would recover the variable from
   -- one field and silently drop every other one (`f Normal Normal` with
   -- `f x y = (x, y)` answered p(y) alone). For such a binding whose bound
   -- variable occurs under a field constructor, point inversion is therefore
   -- not offered, in either mode: a tuple-valued CDF through the single
   -- witness measured only the witnessed slot too (task
   -- tuple-cdf-through-named-callee-measures-only-witnessed-slot). A
   -- function-valued cumulative result keeps it, as 'namedCall' declines it.
   let fieldWitnessUnfolded = underField && not inlineBody && isNothing namedCall
         && not (cumulative && arrowRT)
   -- An if-then-else on the way is split when its condition is deterministic
   -- here ('toInvExprMaybeWith'; the condition is bound in 'bindIfConditions').
   -- Not for a cumulative query: the point path refuses a variable read more
   -- than once (its occurrences in both arms count), where the set-witness
   -- engine splits the same if and answers it.
   let condKnown cn = not cumulative && pType (getTypeInfo (reinferRecovered meta (recoveredVars meta) (exprWithCN meta cn))) == Deterministic
   let pointInversion = if fieldWitnessUnfolded then Nothing
                        else toInvExprMaybeWith condKnown condKnown clauses localAdts lChainName
   -- A binding whose certificate is an affine Gaussian form, all of whose
   -- uses flow affinely into one density leaf, needs no witness at all: it is
   -- integrated out analytically inside that leaf (task
   -- affine-gaussian-closure-lost-across-let-bindings; dispatched on the
   -- certificate since law-carrying-modality M4, not offered as the
   -- set-witness engine's fallback).
   let affineCollapse x lamBody = do
          form <- affineFormOf meta v
          let bodyMeta = marginaliseAs x form (withBindingLaw (extendMetaForLambda meta (getTypeInfo l) x) binding x)
          toIRInference bodyMeta cumulative lamBody sample
   -- Point inversion: the witness recovered by the inverse chain, the
   -- change of variables, and the body factor at the witness.
   let pointInvertWith witnessOf chain@InvChain{invCoV = invExprCoV0, invReadsAny = invExprReadsAny0} = do
        -- A cumulative query transports a bound, rounded at integer quotients
        -- (task cdf-through-discrete-inverse-wrong); a point query the point.
        let (invExprP0, invExprGuard0)
              | cumulative = (invCumValue chain, invCumGuard chain)
              | otherwise  = (invValue chain, invGuard chain)
        -- A CUMULATIVE query transports a bound through each step, and an '=='
        -- or constructor-test step has none to transport. Observed True, the
        -- bound @<= True@ holds for either outcome, so it constrains nothing --
        -- yet the step recovered the compared point, and @right (v2 == 0)@ at
        -- cdf(Right True) answered P(v2 = 0) rather than 1. Observed False, it
        -- recovers the set "any value but this one" ('VAnyExcept'), neither a
        -- bound nor a point: the interpreter compared it as a point, and no text
        -- backend can render it, so 'anyExceptCodegenRefusal' refused the whole
        -- module, the probability function's queries included (task
        -- fuzz-unconsumed-vanyexcept-reaches-codegen, second seed). Either
        -- polarity is wrong here, so the chain is refused. A step handed
        -- a wildcard the chain made up never shows the sentinel here: forward
        -- chaining replaces it by the wildcard ('injectedWildcards').
        --
        -- 'toInvExprMaybeWith' no longer offers a chain whose point value holds
        -- the sentinel, and the cumulative value is built from the same steps,
        -- so this is a backstop (task point-inversion-vanyexcept-witness-crashes).
        when (cumulative && hasAnyExceptExpr invExprP0) $
          refuse lChainName ("cannot compute a cumulative distribution through binding '"
            ++ (case l of Expr _ (Lambda n _) -> n; _ -> toInvCN)
            ++ "': it is recovered through an == or constructor test, which transports no bound"
            ++ " (task fuzz-unconsumed-vanyexcept-reaches-codegen)")
        invExprP        <- pruneDeadLetIns <$> materializeAnchors meta invExprP0
        invExprCoV      <- pruneDeadLetIns <$> materializeAnchors meta invExprCoV0
        invExprGuard    <- pruneDeadLetIns <$> materializeAnchors meta invExprGuard0
        invExprReadsAny <- pruneDeadLetIns <$> materializeAnchors meta invExprReadsAny0
        let appliedCoV = IRApply (IRLambda (boundVar ++ tag) invExprCoV) sample
        -- 'witnessOf' is 'id' except under 'pointInvert''s enumeration of a
        -- wildcard leaf, which reads the inverse as a parameter instead.
        let lInv = witnessOf (IRLambda (boundVar ++ tag) invExprP)
        -- Apply the sample to the inverse
        let appliedSample = IRApply lInv sample
        -- The inversion chain may pass through a deconstructing InjF whose inverse
        -- (e.g. fromLeft/fromRight) is only applicable on one arm (isLeft/isRight):
        -- 'guard' is False exactly when `sample` falls outside that domain, in which
        -- case the whole result below must be forced to zero WITHOUT evaluating it
        -- (it crashes on out-of-domain input -- observe-partials-umbrella N1b). Each
        -- `IRIf guard ... 0` below relies on the interpreter's short-circuit
        -- evaluation of the untaken branch, same as the existing appTestExpr/zeroCheck
        -- idiom elsewhere in this module.
        --
        -- Whether the chain's own arithmetic reads a wildcard ('invReadsAny', see
        -- 'readsAnyW' below). The domain guard is a step of that same chain --
        -- @exp@'s applicability test reads the very slot @log@ would -- so it is
        -- not asked of an unevaluable witness: there it raised a type error in
        -- the interpreter, and the optimizer folded the comparison on the
        -- sentinel into a False guard, a silent impossible answer
        -- (fuzz-admission-oracle-bugs item 8). Every arm below answers a reading
        -- wildcard before it evaluates the inverse.
        let readsAnyW = IRApply (IRLambda (boundVar ++ tag) invExprReadsAny) sample
        let guard = IRIf readsAnyW (IRConst (VBool True)) (IRApply (IRLambda (boundVar ++ tag) invExprGuard) sample)
        let userVar = case l of Expr _ (Lambda n _) -> n; _ -> toInvCN
        -- Query-dependent (the wildcard is in the query value), so a runtime
        -- IRError rather than a static 'refuse'.
        let anyRefusal = IRError ("cannot compute marginal: binding '" ++ userVar
              ++ "' is unobserved (ANY in its witnessing slot), but its value feeds"
              ++ " observed slots or further randomness; integrating it out is beyond"
              ++ " this engine (design modality-witnessed-inference)")
        -- Do probabilistic inference using the applied inverse; unpruned when the
        -- cumulative CoV below may flip it through a complement ('covOperandMeta').
        --
        -- In its own scope: a binding the argument's inference floats (a
        -- mixture's operands, an enumerated sum) reads the inverse, and floated
        -- to the enclosing scope it is evaluated before -- and regardless of --
        -- the domain guard: @draw r = (if Uniform < 0.5 then Stop else Stop) in
        -- Link 8.4 r@ at @Stop@ ran @lnext Stop@ (found by the admission oracle).
        -- So the block is bound under the guard, and under the condition every
        -- arm below reads the result at all: never on an unevaluable witness, and
        -- where a wildcard witness has its own answer, not on one either.
        let sr = semiringOf meta
        let wildcardHasOwnAnswer = case rt of
              TArrow _ _ -> False
              _ -> cumulative || inlineBody
        --
        -- Where a wildcard witness has no answer of its own, the operand's
        -- result IS read at it, as the operand's marginal: one, as
        -- 'toIRInferenceSave' answers a wildcard, before the operand's own
        -- inverse steps apply arithmetic to it. Unguarded, a compound operand
        -- -- @snd (if ..) + 0.0@ handed a helper's chain-made wildcard -- died
        -- in its @plus@ inverse's @Minus (VAny, 0.0)@ at -O0 (task
        -- any-slot-through-injf-inverse-reaches-condition).
        let wildW = IRUnaryOp OpIsAny appliedSample
        let resReadable = IRIf readsAnyW (IRConst (VBool False)) (notIR wildW)
        let wildcardSafe = if wildcardHasOwnAnswer then id else anySafe sr appliedSample id
        let operandAt c = do
              resO <- scoped (toIRInference (covOperandMeta cumulative appliedCoV meta) c v appliedSample)
              wildcardSafe <$> if openIsEmpty resO then return (openValue resO)
                else closeResult sr "inverted" [guard, resReadable] resO
        res <- operandAt cumulative
        -- Change of variables for the inverse the observation was pushed through;
        -- a decreasing CDF flip adds the operand's mass at the bound back.
        scaled <- pointInverseCoV meta cumulative appliedCoV res (operandAt False)
        let guarded e zero = IRIf guard e zero
        -- Guarded-to-zero: outside the inverse's domain the whole result is zero,
        -- and must not be evaluated (short-circuit, see 'guard' above).
        let guardedZero = guardP sr [guard]
        -- The recovered variable (and any recovered by enclosing folds) is
        -- Deterministic for the body's dispatch; re-typing happens after the
        -- fetch because the fetch always returns original annotations.
        let recovered = toInvCN : recoveredVars meta
        let bodyExpr = reinferRecovered meta recovered (bindBody binding)
        -- The body references the bound variable, so it must be in scope in the type
        -- environment (mirrors how the Lambda arm descends into a lambda body).
        let bodyMeta = recoverVars recovered (withBindingLaw (extendMetaForLambda meta (getTypeInfo l) toInvCN) binding toInvCN)
        -- ANY in the witnessing slot (design modality-witnessed-inference, §ANY):
        -- appliedSample is VAny at runtime iff the slot FC recovers this binding
        -- from was queried marginally. If the binding is a "sink" — a single
        -- occurrence and no further randomness in the body — its density
        -- integrates to 1 and the body factor alone is the correct marginal
        -- (the ANY-valued occurrence lands in the very slot that is ANY, where
        -- the deconstruction Save-guard absorbs it). Otherwise the marginal is a
        -- genuine convolution (or the ANY value would flow into inverse
        -- arithmetic / observed-slot comparisons), so refuse at runtime rather
        -- than crash or return a silently wrong density.
        --
        -- The occurrence count is forward chaining's, syntactic, and does not
        -- see through a @draw@: in @draw y = x in (y, y + 1.0)@ the one
        -- occurrence of @x@ reaches two slots through @y@. Re-inference types
        -- @y@ Deterministic there, so 'containsRandomSource' no longer
        -- vetoes it, and the uses are counted through binders as well
        -- ('usesThroughBinders').
        let occurrences = bindOccs binding
        let singleUse = not (bindLeadingArg binding) && length occurrences == 1
              && usesThroughBinders toInvCN (bindBody binding) <= 1
        let bindingIsSink = singleUse && not (containsRandomSource bodyExpr)
        let anyW = IRIf readsAnyW (IRConst (VBool True)) (IRUnaryOp OpIsAny appliedSample)
        let constResult = constantResult
        case rt of
          -- Integrate mode, a binding read more than once, whatever its head
          -- (a named callee's single witness answered these CDFs wrong too,
          -- e.g. @f x = (x, x + 1.0)@ at @cdf((0.3, 1.0))@ 0.618 for 0.5): the
          -- point inversion recovers it from ONE slot, but its other uses
          -- correlate that slot with the rest of the body, and a joint CDF of
          -- correlated slots is no product of per-slot factors -- @draw v =
          -- Uniform in (v, v + 1.0)@ at @cdf((0.5, 1.2))@ is P(v <= min(0.5,
          -- 0.2)) = 0.2, where the single witness answered 0.5 and the body
          -- factor (v fixed at its witness, 1.5 <= 1.2 fails) answers 0. No
          -- engine here measures that region, so the variant is refused rather
          -- than answered wrong (task tuple-cdf-through-draw-ignores-other-slots).
          -- A binding read ONCE reaches only the slot it is recovered from, so
          -- the body's other slots are independent of it and the generic arm
          -- below folds them in as a body factor, exactly as probability mode
          -- does: @draw v = Uniform in (v, 2.0)@ at @(0.5, 1.0)@ is 0.5 * [2.0
          -- <= 1.0] = 0, where the single witness alone answered 0.5. A named
          -- callee read once is folded in the same way by the 'namedCall' arm,
          -- through its own integrate function: @pair v = (v, 2.0)@ at the same
          -- point (task tuple-cdf-through-named-callee-measures-only-witnessed-slot).
          -- This arm comes first so that arm never meets a correlated CDF. A
          -- function-valued result keeps the 'TArrow' arm below, as before.
          _ | cumulative && not singleUse && not arrowRT ->
                refuse lChainName ("cannot compute a cumulative distribution through binding '" ++ userVar
                  ++ "': it is read more than once, so the slots it reaches are correlated and"
                  ++ " their joint CDF is not a product of per-slot factors"
                  ++ " (task tuple-cdf-through-draw-ignores-other-slots)")
          -- A saturated call of a top-level function (`f v`, `step 2.0 v`) whose
          -- parameter was just recovered: the body factor is the callee's own
          -- probability function evaluated at the recovered witness, i.e. the
          -- deterministic-argument call with the witness in v's place. Inlining the
          -- body (the literal-lambda fold below) would mis-bind its tagged chain
          -- names, which is why this used to fall into the single-witness branch
          -- and drop the body entirely -- every other slot of `x : [x + Normal]`,
          -- including the consistency indicator on the witnessing one (task
          -- named-function-list-head-witness-not-recovered).
          --
          -- A call returning a function (`mk v 1.0`, compiled at `mk v`) gets the
          -- same factor inside the closure over the remaining parameters, which
          -- the call then also passes on.
          _ | Just (fName, fArgs) <- namedCall -> do
                let namedRefusal = IRError ("cannot compute marginal: the argument of '" ++ fName
                      ++ "' is unobserved (ANY in its witnessing slot), but its value feeds"
                      ++ " observed slots or further randomness; integrating it out is beyond"
                      ++ " this engine (design modality-witnessed-inference)")
                argIRs <- mapM (toIRGenerate meta) fArgs
                calleeName <- calleeInferenceName meta cumulative fName
                let callee = inferenceCall meta cumulative (IRVar calleeName) sample
                let call = foldl IRApply callee (argIRs ++ [appliedSample] ++ map IRVar lambdaVars)
                callVar <- mkVariable "call"
                let bodyReadable = if bindingIsSink then notIR readsAnyW else notIR anyW
                let whenAny whenAnySink
                      | bindingIsSink = IRIf readsAnyW namedRefusal whenAnySink
                      | otherwise     = namedRefusal
                let guardAny ok whenAnySink = IRIf anyW (whenAny whenAnySink) ok
                let withBody bodyRes = guardedZero (zipResult guardAny (prodP sr scaled bodyRes) bodyRes)
                case rt of
                  -- Inside the closure the call reads its parameters, so its
                  -- binding cannot float out: it is let-bound in place, under the
                  -- same two guards 'closeResult' would have put on it.
                  TArrow _ _ -> do
                    let impossible = packResult (impossibleP sr)
                    let guardedCall = IRIf guard (IRIf bodyReadable call impossible) impossible
                    -- Outside the inverse's domain the closure answers an
                    -- impossible event, flagged, as 'guardedZero' does for a
                    -- value result: an unflagged zero made @mk Normal 1.0@
                    -- (@mk x y = x : [x + y]@) answer p([]) as a possible
                    -- zero (task ir-contract-violations-in-compiler-output).
                    return (detP (guarded
                      (wrapInLambdas (IRLetIn callVar guardedCall (packResult (withBody (unpackResult callVar)))))
                      (wrapInLambdas impossible)))
                  _ -> do
                    bodyRes <- closeResult sr "body_factor" [guard, bodyReadable]
                                 (openWith [(callVar, call)] (unpackResult callVar))
                    return (withBody bodyRes)
          TArrow _ _ -> return (detP (IRIf readsAnyW anyRefusal
                                       (guarded (wrapInLambdas (packResult scaled)) (wrapInLambdas (packResult (impossibleP sr))))))
          _ | not inlineBody ->
                -- The single witness, where the body cannot be folded in inline
                -- ('bindInline'): a top-level callee's body (folded by the
                -- 'namedCall' arm above where it must be), or one that reads a
                -- variable this scope does not bind. A wildcard witness has no
                -- answer here (in integrate mode it used to crash in 'irCDF'), and
                -- an unevaluable one none anywhere. A bound variable under a
                -- field constructor never gets here ('fieldWitnessUnfolded').
                let anyHere = if cumulative then anyW else readsAnyW in
                return (underLambdas lambdaVars (guardedZero (errorWhen anyHere anyRefusal scaled)))
          _ -> do
            -- The inversion above only recovers and infers the variable bound by THIS
            -- lambda. Any additional independent latents bound deeper in the body (e.g. a
            -- second `let` whose value is repacked alongside this one in a tuple) are not
            -- captured by the bound-value inference. Infer the body too and fold it in as an
            -- independent factor: probabilities multiply, dimensions add, branch counts add.
            -- For a body that is deterministic given the recovered variable, the exact
            -- inverse makes the body factor an always-true (dim-0) indicator, so the product
            -- collapses to the original result; only genuinely new latents add density/dim.
            -- Asking whether the recovered witness IS a wildcard evaluates the
            -- inverse, and an inverse whose own arithmetic READS one has no value
            -- to evaluate to: it dies in the interpreter's `Minus` / `Fst` with a
            -- raw type error, and in the typed backends on the string "ANY" (task
            -- fc-inverse-refuses-on-any-input). 'invReadsAny' is the chain's own
            -- static answer to which of its steps read the observation, as a
            -- runtime disjunction over their inputs, so testing it FIRST is what
            -- makes the question below safe to ask at all.
            --
            -- It is folded into 'anyW' rather than wrapped around the result,
            -- which would be a fifth IRIf level per field: every field already
            -- reads 'anyW', so putting it here adds no reader and no nesting,
            -- where wrapping each field of the whole result grew the emitted chain
            -- programs up to 6x (the duplication 'closeResult' documents).
            -- Compile the body factor in its own scope: any bindings the
            -- recursion floats (e.g. the shared `l_*_call` triple of an inner Apply)
            -- must stay under the recovered-variable binding -- evaluation is
            -- strict, so a floated binding that mentions the bound variable would
            -- otherwise be evaluated before the recovered value is in scope.
            bodyO <- scoped (toIRInference bodyMeta cumulative bodyExpr sample)
            -- The recovered value of the bound variable heads that block, so free
            -- occurrences in the body factor resolve (and redundant comparisons
            -- collapse to true), and the whole block is bound ONCE ('closeResult'),
            -- with the fields below projected off it.
            --
            -- It used to be kept inline and unpacked field by field, i.e. one copy
            -- of the block per field that reads it, and the block of a nested
            -- witnessed let holds the enclosing copies of every inner one: the
            -- -O0 IR of a K-step observed chain grew ~6x per step, and the optimizer
            -- spent exponential time folding it back (task
            -- chained-gaussian-trajectory-compile-exponential). Inline was a
            -- workaround for 'stripBranchCount' mis-shifting projections off a
            -- hoisted local result, which it no longer does.
            --
            -- Being bound, the block is evaluated wherever its binding lands, not
            -- where a field reads it, so it carries its own guards: the inverse's
            -- domain guard (outside it the inverse crashes), and the condition
            -- under which the body is read at all below -- a sink's body absorbs a
            -- wildcard-valued witness but not an unevaluable one, and any other
            -- body is read only when the witness is not a wildcard.
            --
            -- Only a body that itself holds a probabilistic let is bound. The
            -- duplication compounds only through such nesting, and a leaf body
            -- factor is typically an indicator whose dim and flag fold to
            -- constants inline but not through a tuple ('closeResult' records
            -- the -O2 cost of routing constants through one), so the innermost
            -- level keeps the inline form -- and single-let programs their
            -- emitted code.
            let bodyReadable = if bindingIsSink then notIR readsAnyW else notIR anyW
            let bodyBlock = openWith [(toInvCN, appliedSample)] () *> bodyO
            bodyRes <- shareUnlessLeaf sr "body_factor" (holdsProbabilisticLet bodyExpr)
                         [guard, bodyReadable] bodyBlock
            -- Independent factors: probabilities multiply, dims add, branch counts add.
            let combined = prodP sr scaled bodyRes
            -- A sink's body factor absorbs a wildcard-VALUED witness, which is
            -- why it may answer with the body alone. It cannot absorb an
            -- unevaluable one: there is no witness to bind, and letting the body
            -- proceed with a wildcard in its place is exactly the silent p = 1.0
            -- this refusal exists to prevent. So a sink refuses here too.
            -- A wildcard witness -- the recovered value is ANY, or a step of the
            -- chain read one (unevaluable) -- means the binding's one occurrence
            -- sits under an ANY slot of the observation, which constrains
            -- nothing there: the marginal is the body's own inference with the
            -- binding left random, its occurrence never evaluated (the slot's
            -- 'anySafe' answers first). That holds for any single-use binding --
            -- fresh randomness elsewhere in the body is independent of it -- not
            -- only a sink (fuzz-admission-oracle-bugs item 8: @snd (draw h =
            -- Uniform in (exp h, True))@ answered p(True) = 0; @draw z = x + 1.0
            -- in (z, Uniform)@ at @(ANY, 0.5)@ refused). A sink keeps its cheaper
            -- answer for a wildcard-valued witness, and a body that cannot be
            -- compiled this way keeps the refusal.
            unevaluable <- if not singleUse then return (constResult anyRefusal) else do
              let openBody = bindBody binding
              let openMeta = withBindingLaw (extendMetaForLambda meta (getTypeInfo l) toInvCN) binding toInvCN
              r <- (Just <$> scoped (toIRInference openMeta cumulative openBody sample))
                     `catchError` (\_ -> return Nothing)
              -- Bound ONCE ('closeResult'), like the body factor above: unpacked
              -- inline, every field of the result carried its own copy of the
              -- open body, which holds the next binding's fold and so its own
              -- four copies -- ~8x per binding on independent single-use lets
              -- (task witness-fold-open-body-copied-per-field). Its guards are
              -- exactly the conditions 'whenAny' reads it under ('guardedZero'
              -- adds 'guard' outside): a wildcard witness, and for a sink an
              -- unevaluable one. As for the body factor, only a body that itself
              -- holds a probabilistic let is bound: the copies compound only
              -- through such nesting, and a leaf block's constant dim and flag
              -- fold away inline but not through the shared tuple.
              --
              -- The open body is read only where the witness is a wildcard,
              -- and the binding's one occurrence is read only behind its
              -- slot's own wildcard test, so it is never evaluated. It is still
              -- a free variable of the block, which the IR contract does not
              -- allow, whatever the evaluation order (task
              -- ir-contract-violations-in-compiler-output: @draw x = Uniform
              -- in draw y = Uniform in (x, y)@ at @(ANY, 0.5)@ read @x@ in an
              -- arm that bound it nowhere). So it is replaced by the wildcard
              -- it stands for: the witness's own value where that is
              -- evaluable, and a value the dead read cannot tell from it where
              -- not. Substituted rather than bound: a leaf block is copied per
              -- field, and a binding with it.
              case r of
                Just openO ->
                  shareUnlessLeaf sr "open_body" (holdsProbabilisticLet openBody)
                    [guard, if bindingIsSink then readsAnyW else anyW]
                    (substFreeOpen toInvCN (IRConst VAny) openO)
                Nothing -> return (constResult anyRefusal)
            let whenAny whenAnySink whenUneval
                  | bindingIsSink = IRIf readsAnyW whenUneval whenAnySink
                  | singleUse     = whenUneval
                  | otherwise     = anyRefusal
            let guardAny ok whenAnySink whenUneval = IRIf anyW (whenAny whenAnySink whenUneval) ok
            return (underLambdas lambdaVars (guardedZero (zip3Result guardAny combined bodyRes unevaluable)))
   -- A wildcard in a finite leaf of the witness that the body reads again
   -- (task any-mark-passed-as-recursive-call-state). The witness is the
   -- query slot itself, so an ANY there reaches every other read of the
   -- bound variable as a value: @draw e = ev prev in e : gen (snd e)@ at
   -- @[(0.0, ANY), ..]@ handed @gen@ the ANY as its state, every @prev == 0@
   -- test answered False, and the marginal was the @prev = 1@ arm alone. The
   -- slot is marginal, so it is summed out: where the leaf is ANY at run
   -- time (and its enclosing tuples are not), the binding's result is the
   -- mixture over the leaf's finite domain of the same result at the witness
   -- with that leaf fixed. The observation compares the fixed leaf against
   -- its ANY slot as a wildcard, the bound value's density is read at the
   -- fixed witness, and the body's other reads see a value. Exact by the law
   -- of total probability, whatever those reads do with it.
   --
   -- The result at a witness is compiled once, as a closure over the inverse
   -- ('pointInvertWith'), and called per leaf value, so the binding is not
   -- compiled once per value; the calls sit in the arm of the run-time test,
   -- so a query without the wildcard makes exactly the one call it made
   -- before. Only a leaf read by more than one occurrence, or by one that
   -- computes with it ('varFieldReads'), with a domain the bound value
   -- states ('fieldDomainOf'), qualifies; any other binding keeps its code.
   -- A point query of a value-typed body only: a closure-valued result has no
   -- mixture, and a cumulative one is left to the existing refusals.
   let enumLeaves =
         let occReads = varFieldReads (compilingProgram meta) (adtDecls meta) toInvCN (bindBody binding)
             overlapping p = [ r | r@(_, q) <- occReads, q `isPrefixOf` p || p `isPrefixOf` q ]
             readAgain p = let ov = overlapping p in length ov >= 2 || any (not . fst) ov
             leaves = [ (p, vals)
                      | p <- tupleLeafPaths (rType (getTypeInfo v)), readAgain p
                      , Just vals <- [fieldDomainOf (compilingProgram meta) 8 v p], not (null vals) ]
         -- At most 'wildcardLeafSumBound' witnesses per wildcard pattern. Not
         -- the materialization budget: that is the dense tables' off switch,
         -- and the sum is not a table.
         in if length occReads >= 2 && product (map (length . snd) leaves) <= wildcardLeafSumBound
              then leaves else []
   let isArrowRT = case rt of TArrow _ _ -> True; _ -> False
   let pointInvert chain
         | cumulative || isArrowRT || not (null lambdaVars) || null enumLeaves = pointInvertWith id chain
         | otherwise = do
            let sr = semiringOf meta
            invExprP <- pruneDeadLetIns <$> materializeAnchors meta (invValue chain)
            invExprGuard <- pruneDeadLetIns <$> materializeAnchors meta (invGuard chain)
            invExprReadsAny <- pruneDeadLetIns <$> materializeAnchors meta (invReadsAny chain)
            let lInv = IRLambda (boundVar ++ tag) invExprP
            let atSample e = IRApply (IRLambda (boundVar ++ tag) e) sample
            -- Whether the witness may be evaluated at all: inside the
            -- inverse's domain and not computed from a wildcard.
            let evaluable = IRIf (atSample invExprReadsAny) constFalseIR (atSample invExprGuard)
            inverseParam <- mkVariable "inverse"
            atWitness <- mkVariable "at_witness"
            resO <- scoped (pointInvertWith (const (IRVar inverseParam)) chain)
            setVariables [(atWitness, IRLambda inverseParam (closeExpr resO packResult))]
            argVar <- mkVariable "witness_arg"
            -- The result at the witness 'fixLeaves' makes of the inverse's.
            let callAt fixLeaves = do
                  r <- mkVariable "at_w"
                  setVariables [(r, IRApply (IRVar atWitness)
                                   (IRLambda argVar (fixLeaves (IRApply lInv (IRVar argVar)))))]
                  return (unpackResult r)
            let leafIsAny w [] = IRUnaryOp OpIsAny w
                leafIsAny w (st : rest) = IRIf (IRUnaryOp OpIsAny w) constFalseIR (leafIsAny (fieldStepIR st w) rest)
            let go [] fixLeaves = callAt fixLeaves
                go ((p, vals) : rest) fixLeaves = do
                  let w = fixLeaves (IRApply lInv sample)
                  summedO <- scoped $ do
                    terms <- forM vals $ \k ->
                      go rest (\x -> setFieldIR p (IRConst (valueToIR k)) (fixLeaves x))
                    foldM (\a b -> mixP sr (IROp OpPlus (rBranches a) (rBranches b)) a b) (head terms) (tail terms)
                  keptO <- scoped (go rest fixLeaves)
                  r <- mkVariable "marginal_leaf"
                  setVariables [(r, IRIf (IRIf evaluable (leafIsAny w p) constFalseIR)
                                       (closeExpr summedO packResult) (closeExpr keptO packResult))]
                  return (unpackResult r)
            go enumLeaves id
   -- The engines of a probabilistic application, as data, in dispatch order
   -- ('engineOrder', the one statement of it, which the modality engine's
   -- 'bindingCerts' lists certificates in too): each entry's applicability is
   -- the predicate the modality engine's let rule reads, and its
   -- construction. First applicable wins. A construction that declines
   -- ('Left') passes its diagnostic on to the next applicable engine; one
   -- that refuses refuses the variant. Enumeration is first in the order but
   -- is not constructed here: it is tried at the Apply arm's earlier
   -- equations ('isEnumerableApplication', under the materialization budget),
   -- ahead of the dead-binding and leading-argument handling a 'Binding'
   -- needs, so a binding reaching this point is one it declined.
   -- Where none applies, the set-witness engine is asked anyway, for its
   -- diagnostic: its predicate is its necessary condition only.
   let engineFor k = case k of
         EnumerationEngine -> Nothing
         PlanEngine -> planApplicable meta rt binding <&> \_ _ ->
              planWitnessApply meta cumulative rt binding sample
         PointInversionEngine -> pointInversion <&> \chain diag -> do
              bound <- bindIfConditions meta binding chain
              case bound of
                Just chain' -> Right <$> pointInvert chain'
                Nothing -> return (Left diag)
         AffineEngine -> affineMarginalisable meta rt binding <&> \(x, lamBody) _ ->
              Right <$> affineCollapse x lamBody
         JointAffineEngine -> jointAffineApplicable meta rt binding <&> \ja _ ->
              jointAffineApply meta cumulative binding ja sample
         WorldsEngine -> setWitnessApplicable meta binding <&> \_ diag ->
              Right <$> setWitnessApply meta cumulative rt binding diag sample
         -- Last, after the set-witness engine's fallback below too: that
         -- one can answer where the set-witness predicate, only its
         -- necessary condition, declined (the all-ANY mask variant of
         -- let-bindings/letWitnessedChain), and must keep doing so.
         InPlaceEngine -> Nothing
   let engines = [ (engineLabel k, engineFor k) | k <- engineOrder ]
   -- Set-valued witnesses invert the observation structurally into guarded
   -- constraint sets on the bound variable (intervals from comparisons, case
   -- splits from ifs, intersections across occurrences) and measure them
   -- against the bound distribution (design set-valued-witnesses).
   let compiledFrom name = when (verbose (compilerConfig meta) >= 1) $
         traceM ("binding of '" ++ userBound ++ "' (" ++ lChainName ++ ", "
                 ++ (if cumulative then "integrate" else "probability") ++ ") compiled by " ++ name)
       userBound = case l of Expr _ (Lambda n _) -> n; _ -> toInvCN
   -- Where no engine applies, the set-witness engine is asked anyway, and
   -- where it refuses, the in-place engine answers if it applies.
   let fallback diag = case inPlaceApplicable rt binding of
         Nothing -> setWitnessApply meta cumulative rt binding diag sample
         Just inPlace -> do
           sw <- (Right <$> scoped (setWitnessApply meta cumulative rt binding diag sample)) `catchError` (return . Left)
           case sw of
             Right o -> inline o
             Left _ -> do
               compiledFrom (engineLabel InPlaceEngine)
               toIRInference meta cumulative inPlace sample
   dispatchEngines compiledFrom engines fallback
