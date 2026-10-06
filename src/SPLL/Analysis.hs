{-# LANGUAGE LambdaCase #-}
module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  definitelyUntagged,
  annotateConditionalProg,
  materializationDomain,
  withinMaterializationBudget,
  structuralTag,
  listedTag
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import Data.Maybe (maybeToList)
import Data.Either (isRight)
import Data.List (genericLength, genericTake, nub)
import Data.Bifunctor
import Control.Monad (guard)
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
annotateEnumsProg p@Program {functions=f, neurals=n, adts=adtsDecls, writeLogitsDecls=registry} = p{functions = finalExprEnv}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    finalExprEnv = fixpoint iterateExprEnv []
    iterateExprEnv eEnv = map (second (annotate adtsDecls f (neuralEnv ++ map (second $ tags . getTypeInfo) eEnv))) f
    -- Every read is tagged with its declaration's resolved annotation, whether
    -- or not an `of` was written: no clause means `of _`, so the two cannot
    -- route differently (task of-annotation-and-auto-derived-enumeration-divergence).
    -- A continuous leaf stays in the tag rather than voiding it -- an explicit
    -- clause is never discarded. A node is enumerable only if its OWN domain
    -- is wholly discrete ('IRCompiler.isEnumerable' and the other consumers
    -- check), so `fst s` off a `([0,1,2], Real)` read enumerates while `s` and
    -- `snd s` do not. A declaration whose annotation does not resolve gets no
    -- tag here; 'SPLL.Prelude.compile' has already refused it with that
    -- diagnostic ('resolveNeuralDecls').
    neuralEnv = [(name, [DiscreteValues mv]) | decl@(name, _, _) <- n,
                 Right mv <- [resolveNeuralAnnotation adtsDecls registry decl]]

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
    --
    -- DO NOT delete this case as dead code, however green the end-to-end suite
    -- looks. Removing it and falling back to the generic recursion emits
    -- byte-identical Python for all 266 corpus programs (investigation
    -- analysis-lambda-discrete-binding). That is not because it is redundant
    -- but because 'applyTags' independently recomputes the same tag for the
    -- 'Apply' node itself, so only *interior* nodes -- the bound variable's own
    -- 'Var' occurrences, and any 'InjF' whose operand set they complete -- lose
    -- their 'DiscreteValues'. Nothing downstream happens to read those today.
    --
    -- What does catch the deletion is the unit test group "let binder threads
    -- DiscreteValues into the body" in test/TestInternals.hs, which asserts on
    -- those interior tags directly (task pin-analysis-let-binder-tag). It has
    -- to be a unit test rather than a '.tst' corpus entry precisely because no
    -- end-to-end program distinguishes the two behaviours.
    --
    -- It has already been deleted once on exactly that reasoning: the binding
    -- sat here unused from 985d450 (2024-10-17), was swept as an unused-binding
    -- warning in e0993e8 (2026-06-06), and had to be reinstated and actually
    -- threaded in c63277a (2026-08-30) to fix
    -- enumerable-injf-operand-loses-tag-across-apply.
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
-- A tag may carry continuous leaves (see neuralEnv above): it is then the
-- node's value *shape*, which the structural accessors below read through, but
-- not an enumeration -- every consumer that loops over a tag refuses one with
-- a continuous leaf. The generic InjF case below finds no values in such a
-- domain ('multiValueToValueList') and leaves the node untagged.
discretesTags adtsParam funEnv visited env e = case e of
  (Expr _ (Apply _ _)) -> applyTags adtsParam funEnv visited env e
  _ -> [DiscreteValues mv | mv <- maybeToList values]
  where
    values = case e of
      -- A pruned observation's HOLE (design witnessed-per-query-capability,
      -- task observation-mask-analysis): `Constant VAny` marks a slot the query
      -- masked, which `SPLL.ObservationMask.pruneObservation` substituted for
      -- the slot's sub-expression. Its domain is ABSENT, not the singleton
      -- {ANY} -- tagging it would make the enumerated sum below range over a
      -- wildcard and report a meaningless mass. Must precede the generic
      -- Constant case. (`Constant VAny` cannot occur in a user program;
      -- `SPLL.Validator` forbids it, so this only ever fires on a hole.)
      (Expr _ (Constant VAny)) -> Nothing
      (Expr _ (Constant a)) -> Just $ MultiDiscretes [a]
      -- Comparisons (gt/lt) are Bool-valued, hence finitely enumerable regardless
      -- of whether their operands are, unlike the generic InjF case below (which
      -- requires every operand to already carry a DiscreteValues tag). Tagging
      -- them lets and/or (and any boolean InjF above them) take the
      -- discrete-enumeration path. Must come before the generic InjF case.
      (Expr _ (InjF (Named name) [_, _])) | name `elem` ["gt", "lt"] -> Just $ MultiDiscretes [VBool True, VBool False]
      -- Structural InjFs (tuple/Either/ADT accessors, constructor tests and
      -- constructors) act on the operand's value set itself rather than on
      -- its listed elements ('structuralTag'), so the cross product a
      -- structured domain stands for is never enumerated just to take it
      -- apart again. Must precede the generic InjF case.
      (Expr _ (InjF (Named name) params))
        | Just rule <- structuralTag adtsParam name
        , Just operands <- mapM getValuesFromExpr params
        , Just answer <- rule operands -> answer
      (Expr _ (InjF (Named name) params)) -> do
        -- Decided from shape first, so an operand that can never be tagged
        -- refutes the node before a sibling's value set is forced (see
        -- 'definitelyUntagged').
        guard (not (any untagged params))
        paramValues <- mapM getValuesFromExpr params
        listedTag adtsParam resultCap name paramValues
      (Expr _ (IfThenElse _ left right)) -> do
        guard (not (untagged left || untagged right))
        valuesLeft <- getValuesFromExpr left
        valuesRight <- getValuesFromExpr right
        return $ unionMultiValues valuesLeft valuesRight
      _ -> Nothing
    untagged = definitelyUntagged funEnv visited
    -- How many distinct values the node's result type has at most, when that is
    -- finite and known: once that many have turned up, the rest of the operand
    -- cross product cannot add one, so 'distinctUpTo' stops there. This is what
    -- keeps `a == b` over two V-value operands at O(V) rather than evaluating
    -- all V^2 pairs to find {True, False} (task
    -- agreement-compile-time-quadratic-in-domain).
    resultCap = case autoDeriveMultiValue adtsParam (rType (getTypeInfo e)) of
      Right mv | not (multiValueContainsContinuous mv) -> multiValueCardinality mv
      _ -> Nothing

-- | The value set of an InjF application, by listing: the forward function is
-- evaluated over the cross product of its operands' listed values, capped at
-- the result type's size ('distinctUpTo').
--
-- No values at all is an *absence* of a domain, not an empty one: either the
-- forward function could not be evaluated, or (for a partial ADT accessor) no
-- operand value is in its domain. Tagging that as an empty enumeration would
-- make downstream inference sum over nothing and report probability zero, so
-- it answers 'Nothing' instead.
listedTag :: [ADTDecl] -> Maybe Integer -> String -> [MultiValue] -> Maybe MultiValue
listedTag adtsParam cap name operands =
  case distinctUpTo cap (propagateValuesLazily adtsParam name (map multiValueToValueList operands)) of
    [] -> Nothing
    vals -> Just (valueListToMultiValue vals)

-- | The value set of a structural InjF, computed from its operands' value
-- sets without listing them (task
-- of-annotation-and-auto-derived-enumeration-divergence). 'Nothing' for any
-- other InjF, which keeps the generic, listing path. The rule's own 'Nothing'
-- is the absent domain the listing path gives when no value comes out.
--
-- Each rule is the listing path's answer, in its canonical form
-- ('valueListToMultiValue' of the listed results, in their order): @fst@ of
-- @A x B@ is @A@ when @B@ has a value, and so on. That is pinned per corpus
-- node by @Internals@' structural-propagation differential. A wholly
-- discrete operand of a non-canonical shape -- a tuple constant is the flat
-- @MultiDiscretes [VTuple ..]@ -- falls back to listing, so the answer is
-- never a guess.
--
-- Where listing voids a tag because one evaluation failed -- @fromRightPartial@
-- over a set that also holds a @Left@ -- the rule answers the values that do
-- exist, the filtering listing already applies to an ADT field accessor
-- (@implicitFunctionApplicable@). That is a refinement of listing's answer,
-- never a different set.
--
-- What the listing path cannot do is see through a continuous leaf, since
-- such a set has no listed values at all: @fst@ of a @([0,1,2], Real)@ read
-- has no tag on that path. Here it is @[0,1,2]@, an ordinary enumerable
-- domain, which is what makes a written @Real@ beside a discrete slot cost
-- that slot nothing.
structuralTag :: [ADTDecl] -> String -> Maybe ([MultiValue] -> Maybe (Maybe MultiValue))
structuralTag adtDecls name = fmap (\rule operands -> if all canonical operands then rule operands else Nothing) $ case name of
  "fst"              -> Just $ unary $ \case MultiTuple a b -> Just (keepIf (inhabited b) a); _ -> Nothing
  "snd"              -> Just $ unary $ \case MultiTuple a b -> Just (keepIf (inhabited a) b); _ -> Nothing
  "fromLeftPartial"  -> Just $ unary $ \case MultiEither l _ -> Just (keepIf True l); _ -> Nothing
  "fromRightPartial" -> Just $ unary $ \case MultiEither _ r -> Just (keepIf True r); _ -> Nothing
  "isLeft"           -> Just $ unary $ \case MultiEither l r -> Just (bools [(inhabited l, True), (inhabited r, False)]); _ -> Nothing
  "isRight"          -> Just $ unary $ \case MultiEither l r -> Just (bools [(inhabited l, False), (inhabited r, True)]); _ -> Nothing
  -- The Maybe-valued extractors: @fromLeft (left a) = right a@, and a Right
  -- operand gives @left ()@.
  "fromLeft"         -> Just $ unary $ \case MultiEither l r -> Just (maybeOf (inhabited r) l); _ -> Nothing
  "fromRight"        -> Just $ unary $ \case MultiEither l r -> Just (maybeOf (inhabited l) r); _ -> Nothing
  "TCons"            -> Just $ \case [a, b] -> Just (keepIf (inhabited a && inhabited b) (MultiTuple a b)); _ -> Nothing
  "left"             -> Just $ \case [a] -> Just (keepIf (inhabited a) (MultiEither a (MultiDiscretes []))); _ -> Nothing
  "right"            -> Just $ \case [b] -> Just (keepIf (inhabited b) (MultiEither (MultiDiscretes []) b)); _ -> Nothing
  _ | name `elem` constructorNames ->
        Just $ \fields -> Just (keepIf (all inhabited fields) (MultiADT [(name, fields)]))
    | Just ctor <- lookup name ctorTests ->
        Just $ unary $ \case
          MultiADT cs -> Just (bools [(all inhabited fs, cn == ctor) | (cn, fs) <- cs])
          _ -> Nothing
    | Just (owner, idx) <- lookup name accessors ->
        Just $ unary $ \case
          MultiADT cs -> Just $ case lookup owner cs of
            Just fs | all inhabited fs, idx < length fs -> Just (fs !! idx)
            _ -> Nothing
          _ -> Nothing
    | otherwise -> Nothing
  where
    -- A rule that does not recognise its operand's shape -- or is handed a
    -- non-canonical one -- answers the outer 'Nothing', which falls back to
    -- listing.
    unary f [mv] = f mv
    unary _ _ = Nothing
    keepIf ok mv = if ok then Just mv else Nothing
    bools cases = case nubValues [VBool b | (True, b) <- cases] of
      [] -> Nothing
      vs -> Just (MultiDiscretes vs)
    maybeOf otherSide payload
      | not (inhabited payload) && not otherSide = Nothing
      | otherwise = Just (MultiEither (MultiDiscretes [VUnit | otherSide])
                                      (if inhabited payload then payload else MultiDiscretes []))
    constructorNames = [cn | adt <- adtDecls, (cn, _) <- constructors adt]
    ctorTests = [("is" ++ cn, cn) | adt <- adtDecls, (cn, _) <- constructors adt]
    accessors = [(fName, (cn, idx)) | adt <- adtDecls, (cn, fs) <- constructors adt, (idx, (fName, _)) <- zip [0..] fs]

-- | Does a value set have at least one value? A continuous leaf does; an
-- empty enumeration, and any product with an empty factor, does not.
inhabited :: MultiValue -> Bool
inhabited mv = case mv of
  MultiDiscretes vs -> not (null vs)
  MultiTuple a b    -> inhabited a && inhabited b
  MultiEither l r   -> inhabited l || inhabited r
  MultiADT cs       -> any (all inhabited . snd) cs
  _                 -> True

-- | Is this set already in the shape 'valueListToMultiValue' would give its
-- listed values? Only then can a constructor rule build its result
-- structurally and still agree with the listing path: a flat
-- @MultiDiscretes [VTuple ..]@ (a tuple constant) is re-factored by listing.
-- Continuous leaves count as canonical; listing could not see them anyway.
canonical :: MultiValue -> Bool
canonical mv = case mv of
  MultiDiscretes vs -> all scalar vs && length (nubValues vs) == length vs
  MultiTuple a b    -> canonical a && canonical b
  MultiEither l r   -> canonical l && canonical r
  MultiADT cs       -> all (all canonical . snd) cs && all (all inhabited . snd) cs
                         && length (nub (map fst cs)) == length cs
  _                 -> True
  where
    scalar v = case v of
      VTuple _ _ -> False
      VEither _  -> False
      VADT _ _   -> False
      _          -> True

-- | The distinct values of a lazily produced result list, in order of first
-- occurrence (what 'nub' gives), or @[]@ if an evaluation fails -- the absence
-- of a domain, as for 'propagateValues'.
--
-- Given a cap, it stops as soon as that many distinct values are in hand, and
-- then answers them even if a later evaluation would have failed: the cap is
-- the size of the whole result type, so what it has is already every value the
-- node can take, and a failure among the unevaluated rest could not make that
-- set any smaller or any less sound.
distinctUpTo :: Maybe Integer -> [Either String Value] -> [Value]
distinctUpTo cap results = case cap of
  Just c | let saturated = genericTake c vals, genericLength saturated == c -> saturated
  _ | null failures -> vals
    | otherwise -> []
  where
    -- Both lazy: 'nubValues' yields each value at its first occurrence, so
    -- taking the cap's worth of them evaluates only as far as the last one.
    (oks, failures) = span isRight results
    vals = nubValues [v | Right v <- oks]

-- | The 'DiscreteValues' tag of an application, one argument or a whole
-- saturated curried spine.
--
-- An arrow-typed callee cannot carry one fixed tag in the 'TagEnv' -- what its
-- result enumerates over depends on what its arguments enumerate over -- so the
-- tag has to be computed per call site. This resolves the application's head to
-- a lambda (a literal one, or a top-level function looked up in the 'FunEnv'),
-- binds each argument's tags to the matching parameter, and re-annotates the
-- body under that environment: the body's own 'InjF'/'IfThenElse' cases then
-- fire exactly as they do when the helper is inlined by hand.
--
-- Without it, `f x ++ f y` has no tag on either operand, so IRCompiler's
-- enumerate-both clauses never match and the enclosing 'InjF' falls off the end
-- of 'toIRInference' (task enumerable-injf-operand-loses-tag-across-apply).
--
-- A curried spine `f a b` is tagged the same way (task
-- shared-enumerated-latent-loses-per-slot-factorization). It used to be
-- refused, because the enumerate path only marginalised the argument of the
-- single 'Apply' node it was handed and a random @a@ sat out of its reach. That
-- is decided in IRCompiler now, where 'pType' is known: a spine whose leading
-- arguments are deterministic -- once the enclosing enumerated latents are
-- fixed -- enumerates its last argument ('enumerateCurriedArgument'), and an
-- enumerated binding measures its argument with those latents fixed, which is
-- what the spine needs when its random argument is a leading one
-- (test/cases/let-bindings/sharedLatentNestedLet is the canary for that).
--
-- Everything it cannot resolve answers @[]@ -- the status quo before this
-- existed -- rather than a guess:
--
--   * a head that is neither a lambda nor a known top-level function
--     (a higher-order parameter, a projection out of a tuple),
--   * a partial application: the result is still arrow-typed, so it enumerates
--     over nothing. This needs no case of its own -- the callee's body is then
--     another 'Lambda', which has no 'DiscreteValues' of its own.
--   * an over-application (more arguments than the callee has parameters),
--   * recursion: a function already being looked through. Unrolling it has no
--     termination story, and the enclosing fixpoint would not converge, so the
--     recursive call site is left untagged. This is why @visited@ is threaded
--     through 'annotateIn' rather than being local here.
applyTags :: [ADTDecl] -> FunEnv -> [String] -> TagEnv -> Expr -> [Tag]
applyTags adtsParam funEnv visited env e = case appSpine e of
  (Expr _ (Var n), args@(_:_))
    | n `notElem` visited
    , Just calleeBody <- lookup n funEnv -> tagOf (n:visited) calleeBody args
  -- A literal lambda head applied to one argument: 'annotateIn' reaches here
  -- only through its @Apply (Lambda ..) v@ case, which has just annotated this
  -- very body under the environment 'tagOf' would build (the parameter bound to
  -- the annotated argument's tags, same @visited@). Its tags are already the
  -- answer. Re-annotating it was a second full walk of the body per `let`,
  -- which is 2^K for K nested lets (task
  -- chained-gaussian-trajectory-compile-exponential). A longer curried spine
  -- has no such case, so it is re-annotated.
  (Expr _ (Lambda _ lamBody), [_]) ->
    [DiscreteValues mv | DiscreteValues mv <- tags (getTypeInfo lamBody)]
  (l@(Expr _ (Lambda _ _)), args@(_:_)) -> tagOf visited l args
  _ -> []
  where
    -- The arguments sit at the call site, so they are already annotated in the
    -- right environment; only the callee's body needs re-annotating, with each
    -- argument's tags bound to its parameter (a later parameter shadowing an
    -- earlier one of the same name, as it does in the body).
    tagOf vis callee as = case bindParams callee as env of
      Just (calleeBody, bodyEnv) ->
        [DiscreteValues mv | DiscreteValues mv <- tags (getTypeInfo (annotateIn adtsParam funEnv vis bodyEnv calleeBody))]
      Nothing -> []
    bindParams b [] en = Just (b, en)
    bindParams (Expr _ (Lambda param lamBody)) (a:as) en = bindParams lamBody as ((param, tags (getTypeInfo a)) : en)
    -- More arguments than parameters: over-applied, no result to enumerate.
    bindParams _ _ _ = Nothing

-- | An application split into its head and its arguments, outermost-last:
-- @f a b@ is @(f, [a, b])@.
appSpine :: Expr -> (Expr, [Expr])
appSpine (Expr _ (Apply l v)) = let (h, as) = appSpine l in (h, as ++ [v])
appSpine e = (e, [])

-- | 'True' only if 'annotateIn' is certain to give the node no
-- 'DiscreteValues' tag, judged from the program's shape alone. No value set is
-- read, so answering forces no propagation.
--
-- Knowing whether a node is tagged normally costs its whole value set: an
-- 'InjF' tag is 'Nothing' when its propagation comes back empty, so even
-- @isJust@ has to run it. That is the wrong order when a sibling can never be
-- tagged. The case that makes it matter is recursion through more than one
-- function. At @main@'s call @oddSum ds@, with @ds@ bound to an @of@
-- annotation's dense enumeration, 'applyTags' looks through @oddSum@ and then,
-- since @evenSum@ is not yet visited, through @evenSum (rest ds)@ as well.
-- @evenSum@'s body reads its parameter, which propagates @rest@ over every
-- enumerated list, and only afterwards reaches @oddSum (rest ..)@, which is
-- refused as visited. So the @plus@ above it is untagged and all of that work
-- is thrown away. A self-recursive fold never pays this, because its recursive
-- call is refused before its argument is looked at (task
-- plan-fold-mutual-recursion-blowup: 36 GB of wasted allocation and 3x the
-- residency at depth 6).
--
-- This mirrors 'discretesTags' and 'applyTags' case for case, and every
-- 'False' is a "maybe". A 'Var' or 'ReadNN' takes its tags from the
-- environment, which may be an expensive thunk, so it answers 'False' rather
-- than look. Wherever the real pass answers 'Nothing' or @[]@ from shape
-- (a visited or unknown head, an over- or partial application, an
-- unhandled node, the @VAny@ hole), this answers 'True'. Because a 'True'
-- only ever short-circuits a result that was already 'Nothing', the tags the
-- pass computes are exactly what they were before this existed.
definitelyUntagged :: FunEnv -> [String] -> Expr -> Bool
definitelyUntagged funEnv visited e = case e of
  Expr _ (Apply _ _) -> case appSpine e of
    (Expr _ (Var n), args@(_:_))
      | n `notElem` visited
      , Just calleeBody <- lookup n funEnv -> bodyUntagged (n:visited) calleeBody (length args)
    (Expr _ (Lambda _ lamBody), [_]) -> definitelyUntagged funEnv visited lamBody
    (l@(Expr _ (Lambda _ _)), args@(_:_)) -> bodyUntagged visited l (length args)
    _ -> True
  Expr _ (Var _) -> False
  Expr _ (ReadNN _ _) -> False
  Expr _ (Constant VAny) -> True
  Expr _ (Constant _) -> False
  Expr _ (InjF (Named name) [_, _]) | name `elem` ["gt", "lt"] -> False
  Expr _ (InjF _ params) -> any (definitelyUntagged funEnv visited) params
  Expr _ (IfThenElse _ l r) -> definitelyUntagged funEnv visited l || definitelyUntagged funEnv visited r
  _ -> True
  where
    -- 'applyTags'' @bindParams@: strip one lambda per argument. Running out of
    -- lambdas first is an over-application; what is left after a partial
    -- application is a 'Lambda', which falls to the catch-all above.
    bodyUntagged vis b 0 = definitelyUntagged funEnv vis b
    bodyUntagged vis (Expr _ (Lambda _ b)) k = bodyUntagged vis b (k - 1)
    bodyUntagged _ _ _ = True

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
-- `a && b` is `if a then b else False` and `a || b` is `if a then True else b`:
-- the same many-to-one case split, just spelled as an InjF. Without this a body
-- (or helper) using the connective was not enumerated where its `if` spelling
-- was, and fell to the set-witness engine, which has no arm for a list
-- element or a named call (task and-inside-list-or-helper-over-draws-refused).
isConditional _ _ _ (Expr _ (InjF (Named n) _)) | n `elem` ["and", "or"] = True
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
