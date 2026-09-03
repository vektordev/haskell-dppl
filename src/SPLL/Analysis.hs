module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  annotateConditionalProg,
  materializationDomain,
  withinMaterializationBudget
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import Data.Maybe (maybeToList)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (setTags)
import PredefinedFunctions
import Utils
import SPLL.Typing.ForwardChaining (FCData, ExprInfo (LambdaInfo), findEquivalentExpression, findExprWithCN)

type TagEnv = [(String, [Tag])]

-- | The top-level function bodies, so 'annotate' can look *through* an
-- application to the callee's body (see 'applyTags'). Held separately from
-- 'TagEnv' because a function has no one fixed tag: what its result enumerates
-- over depends on what its argument enumerates over.
type FunEnv = [(String, Expr)]

annotateEnumsProg :: Program -> Program
annotateEnumsProg p@Program {functions=f, neurals=n, adts=adtsDecls} = p{functions = finalExprEnv}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    finalExprEnv = fixpoint iterateExprEnv []
    iterateExprEnv eEnv = map (second (annotate adtsDecls f (neuralEnv ++ map (second $ tags . getTypeInfo) eEnv))) f
    -- Resolve "_" (MultiAuto) placeholders against the declared output/input type before
    -- this MultiValue is used for discrete-value propagation.
    -- A MultiValue with a continuous (Real) leaf has no finite enumeration; tagging it
    -- would make the enumeration machinery sum over only its discrete residue, silently
    -- dropping the continuous probability mass. Decline to tag instead, the same as a
    -- neural with no `of` annotation at all.
    neuralEnv = [(name, [DiscreteValues mv]) | (name, declType, Just rawMv) <- n,
                 let mv = resolveTag declType rawMv,
                 not (multiValueContainsContinuous mv)]
    resolveTag declType mv = maybe mv (\ty -> resolveMultiAuto adtsDecls ty mv) (neuralValueType declType)

annotate :: [ADTDecl] -> FunEnv -> TagEnv -> Expr -> Expr
annotate adtsParam funEnv = annotateIn adtsParam funEnv []

-- | 'annotate', carrying the set of top-level function names currently being
-- looked through by 'applyTags'. Re-entering one of them would not terminate,
-- so it refuses instead (see 'applyTags').
annotateIn :: [ADTDecl] -> FunEnv -> [String] -> TagEnv -> Expr -> Expr
--annotateIn _ _ _ e | trace ((show e)) False = undefined
annotateIn _ _ _ env e@(Expr ti (Var n)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotateIn _ _ _ env e@(Expr ti (ReadNN n _)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotateIn adtsParam funEnv visited env e = withNewTypeInfo
  where
    rec = annotateIn adtsParam funEnv visited env
    oldTags = tags $ getTypeInfo e
    -- A directly-applied lambda is `let`: inside the body the parameter *is* the
    -- argument, so the body is annotated with the argument's tags bound to it.
    -- Without this a `let`-bound enumerable is invisible to its own body.
    withNewSubExpr = case e of
      Expr _ (Apply l@(Expr _ (Lambda param lamBody)) v) ->
        let annotatedV = rec v
            bodyEnv = (param, tags (getTypeInfo annotatedV)) : env
            annotatedL = setSubExprs l [annotateIn adtsParam funEnv visited bodyEnv lamBody]
        in setSubExprs e [annotatedL, annotatedV]
      _ -> setSubExprs e (map rec (getSubExprs e))
    valueTgs = discretesTags adtsParam funEnv visited env withNewSubExpr
    -- Idempotent in DiscreteValues: this pass owns that tag, so re-annotating a
    -- node replaces its tag rather than appending a second one -- which
    -- 'getValuesFromExpr' treats as an error. 'applyTags' re-annotates an inline
    -- lambda's body that the enclosing traversal has already annotated, so this
    -- is reached on every `(\x -> ..) v` under an application spine.
    newTags = valueTgs ++ filter (not . isDiscreteValues) oldTags
    isDiscreteValues (DiscreteValues _) = True
    isDiscreteValues IsConditional = False
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) newTags)

discretesTags :: [ADTDecl] -> FunEnv -> [String] -> TagEnv -> Expr -> [Tag]
-- The continuous-leaf filter mirrors neuralEnv above: never emit a DiscreteValues
-- tag whose enumeration would be a discrete residue of a partly-continuous set.
discretesTags adtsParam funEnv visited env e = case e of
  (Expr _ (Apply _ _)) -> applyTags adtsParam funEnv visited env e
  _ -> [DiscreteValues mv | mv <- maybeToList values, not (multiValueContainsContinuous mv)]
  where
    values = case e of
      (Expr _ (Constant a)) -> Just $ MultiDiscretes [a]
      -- Comparisons (gt/lt) are Bool-valued, hence finitely enumerable regardless
      -- of whether their operands are, unlike the generic InjF case below (which
      -- requires every operand to already carry a DiscreteValues tag). Tagging
      -- them lets and/or (and any boolean InjF above them) take the
      -- discrete-enumeration path. Must come before the generic InjF case.
      (Expr _ (InjF (Named name) [_, _])) | name `elem` ["gt", "lt"] -> Just $ MultiDiscretes [VBool True, VBool False]
      (Expr _ (InjF (Named name) params)) -> do
        paramValues <- mapM getValuesFromExpr params
        let unpackedMultiVals = map multiValueToValueList paramValues
        -- No values at all is an *absence* of a domain, not an empty one: either
        -- the forward function could not be evaluated, or (for a partial ADT
        -- accessor) no operand value is in its domain. Tagging that as an empty
        -- enumeration would make downstream inference sum over nothing and
        -- report probability zero, so decline the tag instead.
        case nub (propagateValues adtsParam name unpackedMultiVals) of
          [] -> Nothing
          vals -> return (valueListToMultiValue vals)
      (Expr _ (IfThenElse _ left right)) -> do
        valuesLeft <- getValuesFromExpr left
        valuesRight <- getValuesFromExpr right
        return $ unionMultiValues valuesLeft valuesRight
      _ -> Nothing

-- | The 'DiscreteValues' tag of a one-argument application.
--
-- An arrow-typed callee cannot carry one fixed tag in the 'TagEnv' -- what its
-- result enumerates over depends on what its argument enumerates over -- so the
-- tag has to be computed per call site. This resolves the application's head to
-- a lambda (a literal one, or a top-level function looked up in the 'FunEnv'),
-- binds the argument's tags to the parameter, and re-annotates the body under
-- that environment: the body's own 'InjF'/'IfThenElse' cases then fire exactly
-- as they do when the helper is inlined by hand.
--
-- Without it, `f x ++ f y` has no tag on either operand, so IRCompiler's
-- enumerate-both clauses never match and the enclosing 'InjF' falls off the end
-- of 'toIRInference' (task enumerable-injf-operand-loses-tag-across-apply).
--
-- Everything it cannot resolve answers @[]@ -- the status quo before this
-- existed -- rather than a guess:
--
--   * a head that is neither a lambda nor a known top-level function
--     (a higher-order parameter, a projection out of a tuple),
--   * a curried spine of two or more arguments. In `f a b`, `a` sits where
--     IRCompiler's enumerate path cannot reach it: 'enumerateAppliedLambda'
--     marginalises the argument of the single 'Apply' node it is handed, and the
--     partial application `f a` is not even tagged 'IsConditional' (only 'Var'
--     and 'Lambda' nodes are). Tagging the spine would advertise a marginal the
--     compiler then cannot compute -- it takes an enumerate clause and dies
--     inverting the partial application (testCases/sharedLatentNestedLet is the
--     canary). Deciding it per argument position would need 'pType', which this
--     pass runs too early to see (ModalityInfer comes after it).
--   * a partial application: the result is still arrow-typed, so it enumerates
--     over nothing. This needs no case of its own -- the callee's body is then
--     another 'Lambda', which has no 'DiscreteValues' of its own.
--   * recursion: a function already being looked through. Unrolling it has no
--     termination story, and the enclosing fixpoint would not converge, so the
--     recursive call site is left untagged. This is why @visited@ is threaded
--     through 'annotateIn' rather than being local here.
applyTags :: [ADTDecl] -> FunEnv -> [String] -> TagEnv -> Expr -> [Tag]
applyTags adtsParam funEnv visited env e = case appSpine e of
  (Expr _ (Var n), [arg])
    | n `notElem` visited
    , Just calleeBody <- lookup n funEnv -> tagOf (n:visited) calleeBody arg
  (l@(Expr _ (Lambda _ _)), [arg]) -> tagOf visited l arg
  _ -> []
  where
    -- The argument sits at the call site, so it is already annotated in the right
    -- environment; only the callee's body needs re-annotating, with the
    -- argument's tags bound to the parameter.
    tagOf vis (Expr _ (Lambda param lamBody)) a =
      let bodyEnv = (param, tags (getTypeInfo a)) : env
      in [DiscreteValues mv | DiscreteValues mv <- tags (getTypeInfo (annotateIn adtsParam funEnv vis bodyEnv lamBody))]
    -- A named callee whose body is not a lambda at all: it takes no argument, so
    -- this application is over-applied and has no result to enumerate.
    tagOf _ _ _ = []

-- | An application split into its head and its arguments, outermost-last:
-- @f a b@ is @(f, [a, b])@.
appSpine :: Expr -> (Expr, [Expr])
appSpine (Expr _ (Apply l v)) = let (h, as) = appSpine l in (h, as ++ [v])
appSpine e = (e, [])

getValuesFromExpr :: Expr -> Maybe MultiValue
getValuesFromExpr e = case [mv | DiscreteValues mv <- tags $ getTypeInfo e] of
  [mv] -> Just mv
  [] -> Nothing
  -- Annotation is written once per node; a second tag means an earlier pass
  -- ran twice or disagreed with itself, and silently picking one would hide it.
  mvs -> error ("getValuesFromExpr: " ++ show (length mvs) ++ " DiscreteValues tags on one node")

-- The FCData certificate is built once in 'Prelude.compile' and threaded in,
-- rather than rebuilt here (modality-split-forwardchaining).
annotateConditionalProg :: FCData -> Program -> Program
annotateConditionalProg fcData p@Program {functions=fs} = p{functions=map (Data.Bifunctor.second (tMap (tagConditional fcData p))) fs}

tagConditional :: FCData -> Program -> Expr -> TypeInfo
tagConditional fcData p (Expr ti (Lambda _ b)) = if isConditional fcData p [] b then ti{tags=IsConditional:tags ti} else ti
tagConditional fcData p e@(Expr ti (Var _)) = if isConditional fcData p [] e then ti{tags=IsConditional:tags ti} else ti
tagConditional _ _ x = getTypeInfo x

isConditional :: FCData -> Program -> [ChainName] -> Expr -> Bool
isConditional _ _ visited e | chainName (getTypeInfo e) `elem` visited = False
isConditional _ _ _ (Expr _ (IfThenElse _ _ _)) = True
isConditional _ _ _ (Expr _ (Lambda _ _)) = False
-- An application is conditional if the applied function or any argument is:
-- the enumeration fallback in toIREnumerate evaluates the whole application
-- forward, so conditionality anywhere below makes the result conditional.
-- A directly-applied lambda (as produced by `let` desugaring) is looked through
-- into its body -- the body *is* evaluated by the application, unlike a bare
-- (un-applied) lambda which is a closure value. This lets nested enumerable
-- `let`s (let c = .. in let d = .. in ..) propagate conditionality outward.
isConditional fcData p visited (Expr _ (Apply (Expr _ (Lambda _ b)) v)) = isConditional fcData p visited b || isConditional fcData p visited v
isConditional fcData p visited (Expr _ (Apply l v)) = isConditional fcData p visited l || isConditional fcData p visited v
isConditional fcData p visited (Expr (TypeInfo{chainName=cn}) (Var _)) = case findEquivalentExpression fcData cn of
  -- A named function reference resolves to its (possibly curried) lambda body. Strip
  -- the leading lambdas of a multi-argument function so the conditional inside a helper
  -- like `contrib u x = if u then x else 0` is reached, rather than stopping at the
  -- intermediate `\x -> ...` lambda.
  Just (_, LambdaInfo _ bodyCn, _) -> isConditional fcData p (cn:visited) (stripLambdas (findExprWithCN (map snd (functions p)) bodyCn))
  _ -> False
isConditional fcData p visited x = any (isConditional fcData p visited) (getSubExprs x)

-- Strip leading lambdas from a (curried) function body.
stripLambdas :: Expr -> Expr
stripLambdas (Expr _ (Lambda _ b)) = stripLambdas b
stripLambdas e = e

-- ===== Cardinality guard for marginal materialization =====
-- (task materialization-cardinality-guard, design materialized-marginals-semiring)

-- | The finite domain a node's marginal may be materialized over, or 'Nothing'
-- if it may not be -- the decidable guard that lets Tier 0 marginal
-- materialization (IRCompiler's 'materializeOperandTable') proceed WITHOUT the
-- "coarsest sufficient statistic for the downstream query" analysis the parent
-- design firewalls out: set- and bag-valued intermediates have 2^k domains, and
-- this refuses them rather than analysing them.
--
-- @bound@ is 'materializationCardinality' from the 'CompilerConfig'. The
-- predicate is cheap by construction: the domains are already computed --
-- 'annotateEnumsProg' above tags every enumerable node with a 'DiscreteValues'
-- range via 'propagateValues' -- so this reads a number already sitting in the
-- node's tags. No new analysis, no new pass.
--
-- It is TOTAL: every node gets an answer, and anything unannotated, non-finite
-- (a continuous leaf, an unresolved @_@ / type reference), or over budget
-- answers "do not materialize". Being over-conservative costs performance;
-- being wrong costs correctness silently, so every unknown resolves to
-- 'Nothing'.
--
-- LOAD-BEARING COINCIDENCE, do not let it drift: this is the SAME predicate as
-- the let-unrolling affordability condition. Tier 0 materializes a table as
-- let-bound scalar cells rather than as a runtime array (IRExpr has no dense
-- array type; @IRBuiltin BListIndex@ is an O(n) cons-cell walk), so "the domain
-- is small enough to tabulate" and "the unrolling is affordable" are one
-- question, not two. A change to either side has to be made on both.
materializationDomain :: Int -> [Tag] -> Maybe [Value]
materializationDomain bound tgs = case [mv | DiscreteValues mv <- tgs] of
  (mv:_) | multiValueIsFinite mv
         , let vals = multiValueToValueList mv
         , withinMaterializationBudget bound (length vals) -> Just vals
  _ -> Nothing

-- | Is a cell count within the materialization budget? Split out from
-- 'materializationDomain' because the same budget also bounds the operand GRID
-- a convolution unrolls (@|D_left| * |D_right|@ compile-time pairs), which is
-- not any node's own tag but is the same "how much unrolling is affordable"
-- question -- see the note above. A non-positive @bound@ disables
-- materialization entirely, which is the off-switch differential tests use.
withinMaterializationBudget :: Int -> Int -> Bool
withinMaterializationBudget bound n = n > 0 && n <= bound
