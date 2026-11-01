{-# LANGUAGE LambdaCase #-}
module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  definitelyUntagged,
  enumerableApplication,
  headIsConditional,
  enumerableDomain,
  getValuesFromExpr,
  materializationDomain,
  withinMaterializationBudget,
  structuralTag,
  listedTag,
  isEnumerable,
  LatentScope,
  LatentBinder(..),
  latentDependencies,
  bindLatent,
  sharesEnumeratedLatent,
  isCandidateBinaryEnumInjF,
  injFLatentVerdicts,
  materializationVerdicts,
  materializationScopes,
  sharesLatentGiven,
  bindLambdaParam
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import Data.Maybe (maybeToList, isJust)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Either (isRight)
import Data.List (genericLength, genericTake, nub)
import Data.Bifunctor
import Control.Monad (guard)
import SPLL.Typing.Typing (setTags)
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import PredefinedFunctions
import Utils
import SPLL.CompilerConfig (defaultMaterializationCardinality)
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
annotate adtsParam funEnv = annotateIn adtsParam funEnv unrollFuel []

-- | 'annotate', carrying the set of top-level function names currently being
-- looked through by 'applyTags'. Re-entering one of them would not terminate,
-- so it refuses instead (see 'applyTags').
--
-- @fuel@ bounds how many calls deep 'applyTags' may still unroll a recursive
-- function called on constant arguments (see 'unrollFuel').
annotateIn :: [ADTDecl] -> FunEnv -> Int -> [String] -> TagEnv -> Expr -> Expr
--annotateIn _ _ _ _ e | trace ((show e)) False = undefined
annotateIn _ _ _ _ env e@(Expr ti (Var n)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotateIn _ _ _ _ env e@(Expr ti (ReadNN n _)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotateIn adtsParam funEnv fuel visited env e = withNewTypeInfo
  where
    rec = annotateIn adtsParam funEnv fuel visited env
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
      -- Inside an unrolled body (@fuel@ below 'unrollFuel', where the
      -- annotated tree is discarded for its tag), a closed constant bound
      -- by a `let` is substituted like the unrolled callee's own parameters
      -- ('applyTags'), so an alias of one (@rollout k = draw j = k in ..@)
      -- still decides the arm ('liveArm') and leaves the recursive call's
      -- arguments closed (task
      -- alias-of-recursive-helper-parameter-refuses-with-random-argument).
      Expr _ (Apply l@(Expr _ (Lambda param lamBody)) v)
        | fuel < unrollFuel, closedConstant v ->
            setSubExprs e [setSubExprs l [rec (substituteVar param v lamBody)], rec v]
      Expr _ (Apply l@(Expr _ (Lambda param lamBody)) v) ->
        let annotatedV = rec v
            bodyEnv = (param, tags (getTypeInfo annotatedV)) : env
            annotatedL = setSubExprs l [annotateIn adtsParam funEnv fuel visited bodyEnv lamBody]
        in setSubExprs e [annotatedL, annotatedV]
      -- A condition that is a closed constant decides the arm ('liveArm'). The
      -- dead arm is annotated with no unrolling fuel: inside an unrolled
      -- recursion it is the branch past the base case (@rollout (0 - 1)@), and
      -- unrolling it would run until the fuel ran out. With no fuel it is
      -- annotated exactly as it was before unrolling existed.
      Expr _ (IfThenElse c l r) ->
        let c' = rec c
            dead = annotateIn adtsParam funEnv 0 visited env
        in case liveArm fuel c' of
             Just True  -> setSubExprs e [c', rec l, dead r]
             Just False -> setSubExprs e [c', dead l, rec r]
             Nothing    -> setSubExprs e [c', rec l, rec r]
      _ -> setSubExprs e (map rec (getSubExprs e))
    valueTgs = discretesTags adtsParam funEnv fuel visited env withNewSubExpr
    -- Idempotent in DiscreteValues: this pass owns that tag, so re-annotating a
    -- node replaces its tag rather than appending a second one -- which
    -- 'getValuesFromExpr' treats as an error. 'applyTags' re-annotates an inline
    -- lambda's body that the enclosing traversal has already annotated, so this
    -- is reached on every `(\x -> ..) v` under an application spine.
    newTags = valueTgs ++ filter (not . isDiscreteValues) oldTags
    isDiscreteValues (DiscreteValues _) = True
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) newTags)

discretesTags :: [ADTDecl] -> FunEnv -> Int -> [String] -> TagEnv -> Expr -> [Tag]
-- A tag may carry continuous leaves (see neuralEnv above): it is then the
-- node's value *shape*, which the structural accessors below read through, but
-- not an enumeration -- every consumer that loops over a tag refuses one with
-- a continuous leaf. The generic InjF case below finds no values in such a
-- domain ('multiValueToValueList') and leaves the node untagged.
discretesTags adtsParam funEnv fuel visited env e = case e of
  (Expr _ (Apply _ _)) -> applyTags adtsParam funEnv fuel visited env e
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
      -- 'collapse' is a Gaussian, not an image of its operand's values: listing
      -- its (identity) forward over a discrete operand would claim the operand's
      -- support for a continuous law.
      (Expr _ (InjF (Named name) _)) | isCollapse name -> Nothing
      -- A list cell's domain is the product of its head's and its tail's, so a
      -- list literal of N two-valued reads has 2^N values, and no structured
      -- shape holds a list domain the way 'MultiADT' holds a record's: it has to
      -- be listed. Past 'listDomainBound' it is left untagged ("no known
      -- domain"), which the dense enumeration gate would refuse at that size
      -- anyway; listing it cost exponential compile time on a literal that is
      -- only ever inverted per element (task
      -- list-of-field-reads-compile-exponential). Must precede the structural
      -- case, whose Cons rule lists.
      (Expr _ (InjF (Named "Cons") [h, t]))
        | not (untagged h || untagged t)
        , Just hv <- getValuesFromExpr h
        , Just tv <- getValuesFromExpr t
        , maybe True (> listDomainBound) ((*) <$> multiValueCardinality hv <*> multiValueCardinality tv) -> Nothing
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
      -- A closed-constant condition: the value set is the live arm's alone
      -- (the dead arm may well be untagged, see 'annotateIn').
      (Expr _ (IfThenElse c left right))
        | Just b <- liveArm fuel c -> do
            let arm = if b then left else right
            guard (not (untagged arm))
            getValuesFromExpr arm
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
  -- A list cell, one list per head value and tail list in listing's order,
  -- built without the interpreter.
  "Cons"             -> Just $ \case
    [h, MultiDiscretes ts] | Just tls <- mapM listCells ts ->
      Just $ case nubValues [VList (ListCont x tl) | x <- multiValueToValueList h, tl <- tls] of
        [] -> Nothing
        vals -> Just (MultiDiscretes vals)
    _ -> Nothing
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
    listCells v = case v of
      VList l -> Just l
      _ -> Nothing
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

-- | The most values a list-valued node's tag may list (see the Cons case of
-- 'discretesTags'): the default dense-enumeration budget, past which no list
-- domain is enumerated densely.
listDomainBound :: Integer
listDomainBound = toInteger defaultMaterializationCardinality

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
-- fixed -- enumerates its last argument ('enumerateCurriedArgument'; a lone
-- random leading argument likewise where binding it refuses,
-- 'leadingEnumerableArgument'), and an
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
--   * recursion: a function already being looked through. Unrolling it in
--     general has no termination story, and the enclosing fixpoint would not
--     converge, so the recursive call site is left untagged. This is why
--     @visited@ is threaded through 'annotateIn' rather than being local here.
--
-- The one recursion that does unroll is a call whose arguments are all closed
-- constants (@rollout 3@, and inside it @rollout (3 - 1)@): the constants are
-- substituted for the parameters, so every condition on them is itself a
-- closed constant, which decides its arm ('liveArm'), and the base case stops
-- the unrolling where the program's own evaluation stops. Such a call does not
-- join @visited@. Two things bound it: 'unrollFuel' calls deep, after which it
-- falls back to the ordinary look-through, and only a callee with at most one
-- call that can recurse back into it is unrolled ('unrollableCallee'), so the
-- unrolling is a chain, never a tree (@fib 30@ stays untagged rather than
-- costing 2^30 annotations). Task recursive-consumer-of-recursive-random-list-refused:
-- @len (rollout 3) < 2@ needs @rollout 3@'s list domain to enumerate @len@'s
-- argument.
applyTags :: [ADTDecl] -> FunEnv -> Int -> [String] -> TagEnv -> Expr -> [Tag]
applyTags adtsParam funEnv fuel visited env e = case appSpine e of
  (Expr _ (Var n), args@(_:_))
    | fuel > 0
    , Just calleeBody <- lookup n funEnv
    , all closedConstant args
    , unrollableCallee funEnv n calleeBody
    , Just consts <- mapM constantOf args
    , Just unrolled <- substParams calleeBody consts ->
        [DiscreteValues mv | DiscreteValues mv <- tags (getTypeInfo (annotateIn adtsParam funEnv (fuel - 1) visited env unrolled))]
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
        [DiscreteValues mv | DiscreteValues mv <- tags (getTypeInfo (annotateIn adtsParam funEnv fuel vis bodyEnv calleeBody))]
      Nothing -> []
    bindParams b [] en = Just (b, en)
    bindParams (Expr _ (Lambda param lamBody)) (a:as) en = bindParams lamBody as ((param, tags (getTypeInfo a)) : en)
    -- More arguments than parameters: over-applied, no result to enumerate.
    bindParams _ _ _ = Nothing
    -- The argument's one value, from its (already computed, and for a closed
    -- constant cheap) tag, as a literal carrying the argument's annotation.
    constantOf a = case getValuesFromExpr a of
      Just mv | not (multiValueContainsContinuous mv)
              , [v] <- multiValueToValueList mv
              , v /= VAny -> Just (Expr (getTypeInfo a) (Constant v))
      _ -> Nothing
    -- Strip one lambda per argument, substituting the constant for its
    -- parameter; partial and over-application are not unrolled.
    substParams b [] = case b of
      Expr _ (Lambda _ _) -> Nothing
      _ -> Just b
    substParams (Expr _ (Lambda param lamBody)) (c:cs) = substParams (substituteVar param c lamBody) cs
    substParams _ _ = Nothing

-- | How many calls deep 'applyTags' unrolls a recursion on constant
-- arguments. Past it, the call is looked through the ordinary way, where the
-- recursive call is refused as visited.
unrollFuel :: Int
unrollFuel = 64

-- | An argument that is a closed constant by shape: a literal, or a
-- deterministic 'InjF' of closed constants. Decided without reading any tag, so
-- 'definitelyUntagged' can ask it too. ('Uniform' and 'Normal' are 'Var's,
-- so they are not closed; 'collapse' is a Gaussian, not a function.)
closedConstant :: Expr -> Bool
closedConstant e = case e of
  Expr _ (Constant VAny) -> False
  Expr _ (Constant _) -> True
  Expr _ (InjF (Named name) params) -> not (isCollapse name) && all closedConstant params
  _ -> False

-- | The arm a closed-constant condition selects, when its tag says it is one
-- Bool. Only a condition that is closed by shape counts, so that
-- 'definitelyUntagged' can tell from shape where the real pass may read one
-- arm.
--
-- Only inside an unrolled body (@fuel@ below 'unrollFuel'), where it is what
-- stops the unrolling at the base case and the annotated body is discarded
-- for its tag. Elsewhere the union of both arms stays: a program's own
-- @if False then .. else ..@ keeps the tags it had, which IRCompiler routes
-- on (refining them at top level gave decreasingRecursionEnumeratedArgument's
-- @loop@ a new copy fan-out in the duplication census).
liveArm :: Int -> Expr -> Maybe Bool
liveArm fuel c
  | fuel < unrollFuel
  , closedConstant c
  , Just mv <- getValuesFromExpr c
  , [VBool b] <- multiValueToValueList mv = Just b
  | otherwise = Nothing

-- | Does the callee's body hold at most one call that can lead back into it?
-- Each unrolled level then spawns at most one more, so unrolling costs
-- linear, not exponential, annotation work. Counted syntactically over every
-- 'Var' naming a top-level function (a shadowing local over-counts, which only
-- declines).
unrollableCallee :: FunEnv -> String -> Expr -> Bool
unrollableCallee funEnv n calleeBody = length (filter (reachesBack n) (topLevelRefs calleeBody)) <= 1
  where
    topLevelRefs ex = [v | Expr _ (Var v) <- universe ex, isJust (lookup v funEnv)]
    universe ex = ex : concatMap universe (getSubExprs ex)
    reachesBack target start = go [] [start]
      where
        go _ [] = False
        go seen (g:gs)
          | g == target = True
          | g `elem` seen = go seen gs
          | otherwise = go (g : seen) (maybe [] topLevelRefs (lookup g funEnv) ++ gs)

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
    -- 'applyTags' may unroll it, visited or not: a "maybe".
    (Expr _ (Var n), args@(_:_))
      | all closedConstant args
      , Just calleeBody <- lookup n funEnv
      , unrollableCallee funEnv n calleeBody -> False
    (Expr _ (Var n), args@(_:_))
      | n `notElem` visited
      , Just calleeBody <- lookup n funEnv -> bodyUntagged (n:visited) calleeBody (length args)
    -- Inside an unrolled body a closed constant's `let` is substituted
    -- ('annotateIn'), which may close a condition or a recursive call's
    -- arguments: a "maybe".
    (Expr _ (Lambda _ _), [v]) | closedConstant v -> False
    (Expr _ (Lambda _ lamBody), [_]) -> definitelyUntagged funEnv visited lamBody
    (l@(Expr _ (Lambda _ _)), args@(_:_)) -> bodyUntagged visited l (length args)
    _ -> True
  Expr _ (Var _) -> False
  Expr _ (ReadNN _ _) -> False
  Expr _ (Constant VAny) -> True
  Expr _ (Constant _) -> False
  Expr _ (InjF (Named name) [_, _]) | name `elem` ["gt", "lt"] -> False
  Expr _ (InjF (Named name) _) | isCollapse name -> True
  Expr _ (InjF _ params) -> any (definitelyUntagged funEnv visited) params
  -- A closed-constant condition reads one arm only ('liveArm'), which this
  -- does not evaluate: untagged only if both arms are.
  Expr _ (IfThenElse c l r)
    | closedConstant c -> definitelyUntagged funEnv visited l && definitelyUntagged funEnv visited r
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

-- | The enumeration engine's applicability to an application @l v@ (design
-- law-carrying-modality M5): the head is conditional ('headIsConditional')
-- and the argument is a random value with an enumerable domain, which is the
-- certificate. Read alike by the modality engine's let rule and by
-- IRCompiler's dispatch. The engine's own budget gate
-- ('enumerationWithinMaterializationBudget') stays at the dispatch: over
-- budget, the application falls through to the next engine.
enumerableApplication :: FCData -> Program -> Expr -> Expr -> Maybe MultiValue
enumerableApplication fcData p l v
  | headIsConditionalWith cmps fcData p l
  , pType (getTypeInfo v) /= Deterministic
  , not (returnsFunction (rType (getTypeInfo l)))
  = enumerableDomain (tags (getTypeInfo v))
  | otherwise = Nothing
  where
    returnsFunction (TArrow _ (TArrow _ _)) = True
    returnsFunction _ = False
    -- A comparison (@==@, @<@, @>@) is a many-to-one case split of its
    -- operands, like an @if@: @c == c@ or @fst p < snd p@ at the query root
    -- was refused (or generate-only) where @if c == c then True else False@
    -- enumerated (tasks bare-equality-of-shared-draw-reads-refused,
    -- enumerated-int-pair-comparison-no-probability). Not for a neural read:
    -- the plan engine, next in dispatch order, measures a comparison of its
    -- leaves per slot ('PLeafEq', the two-leaf coupling) where enumerating
    -- the whole read would call the network once per value.
    cmps = not (isNeuralRead v)
    isNeuralRead (Expr _ (ReadNN _ _)) = True
    isNeuralRead (Expr _ (InjF _ [e])) = isNeuralRead e
    isNeuralRead _ = False

-- | Is an application head conditional ('isConditional'): a lambda whose body
-- is, or a reference resolving to such a function. Any other head is not.
-- The FCData certificate is built once in 'Prelude.compile' and threaded in
-- (modality-split-forwardchaining).
headIsConditional :: FCData -> Program -> Expr -> Bool
headIsConditional = headIsConditionalWith False

-- | 'headIsConditional', counting a comparison as a case split when @cmps@
-- holds ('enumerableApplication').
headIsConditionalWith :: Bool -> FCData -> Program -> Expr -> Bool
headIsConditionalWith cmps fcData p (Expr _ (Lambda _ b)) = isConditionalWith cmps fcData p [] b
headIsConditionalWith cmps fcData p e@(Expr _ (Var _)) = isConditionalWith cmps fcData p [] e
headIsConditionalWith _ _ _ _ = False

-- | Is an expression a many-to-one case split ('headIsConditional'): an
-- @if@, a connective, and with @cmps@ a comparison, anywhere in it or in a
-- function it calls.
isConditionalWith :: Bool -> FCData -> Program -> [ChainName] -> Expr -> Bool
isConditionalWith _ _ _ visited e | chainName (getTypeInfo e) `elem` visited = False
isConditionalWith _ _ _ _ (Expr _ (IfThenElse _ _ _)) = True
-- `a && b` is `if a then b else False` and `a || b` is `if a then True else b`:
-- the same many-to-one case split, just spelled as an InjF. Without this a body
-- (or helper) using the connective was not enumerated where its `if` spelling
-- was, and fell to the set-witness engine, which has no arm for a list
-- element or a named call (task and-inside-list-or-helper-over-draws-refused).
isConditionalWith _ _ _ _ (Expr _ (InjF (Named n) _)) | n `elem` ["and", "or"] = True
-- A comparison, where the caller counts it ('enumerableApplication').
isConditionalWith True _ _ _ (Expr _ (InjF (Named n) _)) | n `elem` ["eq", "lt", "gt"] = True
isConditionalWith _ _ _ _ (Expr _ (Lambda _ _)) = False
-- An application is conditional if the applied function or any argument is:
-- the enumeration fallback in toIREnumerate evaluates the whole application
-- forward, so conditionality anywhere below makes the result conditional.
-- A directly-applied lambda (as produced by `let` desugaring) is looked through
-- into its body -- the body *is* evaluated by the application, unlike a bare
-- (un-applied) lambda which is a closure value. This lets nested enumerable
-- `let`s (let c = .. in let d = .. in ..) propagate conditionality outward.
isConditionalWith cmps fcData p visited (Expr _ (Apply (Expr _ (Lambda _ b)) v)) = isConditionalWith cmps fcData p visited b || isConditionalWith cmps fcData p visited v
isConditionalWith cmps fcData p visited (Expr _ (Apply l v)) = isConditionalWith cmps fcData p visited l || isConditionalWith cmps fcData p visited v
isConditionalWith cmps fcData p visited (Expr (TypeInfo{chainName=cn}) (Var _)) = case findEquivalentExpression fcData cn of
  -- A named function reference resolves to its (possibly curried) lambda body. Strip
  -- the leading lambdas of a multi-argument function so the conditional inside a helper
  -- like `contrib u x = if u then x else 0` is reached, rather than stopping at the
  -- intermediate `\x -> ...` lambda.
  Just (_, LambdaInfo _ bodyCn, _) -> isConditionalWith cmps fcData p (cn:visited) (stripLambdas (findExprWithCN (map snd (functions p)) bodyCn))
  _ -> False
isConditionalWith cmps fcData p visited x = any (isConditionalWith cmps fcData p visited) (getSubExprs x)

-- Strip leading lambdas from a (curried) function body.
stripLambdas :: Expr -> Expr
stripLambdas (Expr _ (Lambda _ b)) = stripLambdas b
stripLambdas e = e

-- ===== Enumerable domain =====

-- | The node's enumerable domain: its 'DiscreteValues' tag, when it has one
-- and no leaf of it is continuous. The single producer of the "enumerable
-- domain" fact (task finiteness-single-producer). Every enumeration equation
-- in 'SPLL.IRCompiler' ('isEnumerable', 'isEnumerableApplication', the
-- enumerate-both grids, @sampleDom@), 'SPLL.Typing.ModalityInfer''s
-- comparison rule, and the modality lattice's @Fin = Finite@
-- ('SPLL.Typing.Modality.finFromTags') all ask this, and nothing else.
--
-- A tag with a continuous leaf is a value shape, not an enumerable domain
-- (task of-annotation-and-auto-derived-enumeration-divergence): walking its
-- discrete residue would silently drop the continuous mass. Analysis keeps at
-- most one 'DiscreteValues' tag per node ('getValuesFromExpr').
--
-- This answers "is there something to loop over", not "is it affordable to
-- materialize": 'materializationDomain' adds the budget, and the stricter
-- non-emptiness test 'multiValueIsFinite' its callers need for the values.
enumerableDomain :: [Tag] -> Maybe MultiValue
enumerableDomain tgs = case [mv | DiscreteValues mv <- tgs] of
  (mv:_) | not (multiValueContainsContinuous mv) -> Just mv
  _ -> Nothing

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
materializationDomain bound tgs = case enumerableDomain tgs of
  Just mv | multiValueIsFinite mv
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

-- | Does the node carry an enumerable domain ('SPLL.Analysis.enumerableDomain',
-- the one producer of that fact)?
isEnumerable :: [Tag] -> Bool
isEnumerable = isJust . enumerableDomain

-- ===== Decomposability gate (design decomposability-gate-shared-latent) =====
--
-- A static analysis answering, for a binary enumerable InjF node, whether its
-- two operands may share an *enumerated latent* -- a 'let'-bound enumerable,
-- non-deterministic value that both operands' subtrees read, directly or
-- through tuple/ADT components or a user-function's parameters. If they do,
-- the operands are NOT independent and must not be tabulated (weighted and
-- summed) separately; the correct answer requires enumerating the shared
-- latent jointly. This is the correctness precondition for a future
-- per-operand marginal tabulation (design materialize-discrete-marginals);
-- it is pure analysis with no consumer yet, so it does not gate any of this
-- module's existing compilation decisions and changes no emitted code. See
-- TestInternals for direct unit coverage of the predicate.
--
-- Mechanism: track, per in-scope local variable, the set of latent chain
-- names ('LatentScope') its value structurally depends on -- 'Nothing' means
-- unknown/unanalysable rather than "no dependency", so it propagates through
-- later reads of that variable instead of silently looking independent. A
-- scope is NOT optional: an operand's free variables only resolve relative
-- to the 'let's that lexically enclose it, so the gate must be queried with
-- the scope in effect at that point in the program (see 'injFLatentVerdicts'
-- for a whole-program walk that builds it correctly; querying with an empty
-- scope on an operand pulled from deep inside nested 'let's silently answers
-- "independent" for everything, which is the false negative this analysis
-- exists to avoid).
--
-- A 'let x = v in body' (@Apply (Lambda x body) v@, 'bindLatent') looks up
-- whatever 'v' itself depends on and, if 'v' is itself a fresh enumerable
-- non-deterministic draw, mints a new latent identity keyed by 'v's own
-- chain name -- so two textually identical-looking draws bound by two
-- distinct 'let's are never conflated (chain names are unique per AST
-- occurrence). A saturated call to a top-level function needs no body
-- inlining to catch latents crossing the call boundary: since SPLL has no
-- closures over a caller's 'let's, a callee can only see its own parameters,
-- so the latent set of `f a1 .. an` is exactly the union of the arguments'
-- latent sets, and the generic 'Apply'-chain case below already computes
-- that by unrolling currying. Anything this can't see through -- a
-- first-class 'Lambda' value reached anywhere other than directly as a
-- 'let' RHS -- reports unknown ('Nothing'), which 'sharesEnumeratedLatent'
-- treats conservatively as "may share": an unnecessary refusal costs
-- performance, a missed one costs correctness silently.
type LatentScope = Map.Map String (Maybe (Set.Set ChainName))

latentDependencies :: LatentScope -> Expr -> Maybe (Set.Set ChainName)
latentDependencies scope (Expr _ (Var x))       = Map.findWithDefault (Just Set.empty) x scope
latentDependencies _     (Expr _ (Constant _))  = Just Set.empty
latentDependencies _     (Expr _ (Lambda _ _))  = Nothing
latentDependencies scope (Expr _ (ThetaI e _))  = latentDependencies scope e
latentDependencies scope (Expr _ (Subtree e _)) = latentDependencies scope e
latentDependencies scope (Expr _ (ReadNN _ e))  = latentDependencies scope e
latentDependencies scope (Expr _ (IfThenElse c t e)) =
  mconcat <$> mapM (latentDependencies scope) [c, t, e]
latentDependencies scope (Expr _ (InjF _ params)) =
  mconcat <$> mapM (latentDependencies scope) params
latentDependencies scope (Expr _ (Apply (Expr _ (Lambda x lambdaBody)) v)) =
  latentDependencies (bindLatent scope x v) lambdaBody
latentDependencies scope (Expr _ (Apply l v)) =
  mconcat <$> mapM (latentDependencies scope) [l, v]

-- | Extend a 'LatentScope' with a 'let x = v in ...' binding: 'x' depends on
-- whatever 'v' depends on, plus (if 'v' is itself a fresh enumerable
-- non-deterministic draw) a new latent identity of its own. Shared between
-- 'latentDependencies' (which needs it to descend into a 'let's body) and
-- 'injFLatentVerdicts' (which needs it to build the scope for OTHER nodes
-- reached later in the same walk) so the two never disagree on what a 'let'
-- binds.
bindLatent :: LatentScope -> String -> Expr -> LatentScope
bindLatent scope x v = Map.insert x xLatent scope
  where
    vTi = getTypeInfo v
    freshLatent
      | isEnumerable (tags vTi) && pType vTi /= Deterministic = Set.singleton (chainName vTi)
      | otherwise = Set.empty
    xLatent = (<> freshLatent) <$> latentDependencies scope v

-- | The gate itself: under the given scope, may these two operands of a
-- binary node (typically a binary enumerable InjF) share an enumerated
-- latent? Conservative on the unknown case -- see 'latentDependencies'.
sharesEnumeratedLatent :: LatentScope -> Expr -> Expr -> Bool
sharesEnumeratedLatent scope l r =
  case (latentDependencies scope l, latentDependencies scope r) of
    (Just ls, Just rs) -> not (Set.disjoint ls rs)
    _                  -> True

-- | True for the exact shape the per-operand tabulation paths above
-- (isEnumerable/isEnumerable && non-Deterministic/non-Deterministic guards
-- on 'left'/'right', e.g. the enumerate-both and invert-one-side InjF
-- clauses) require of a binary InjF's two operands. Today's Analysis pass
-- only tags DiscreteValues on a handful of shapes (ReadNN, InjF-of-enum,
-- discrete-conditioned IfThenElse, Constant, ADT accessors -- see
-- Analysis.md), NOT on the result of an ordinary user-function call; so a
-- node like `(contrib u 1) ++ (contrib u 1)`, whose operands are finite Ints
-- in the shape's own logic but untagged, does not currently satisfy this
-- narrower predicate even though 'sharesEnumeratedLatent' answers it fine.
-- That tag-propagation gap is a separate, pre-existing concern; this
-- predicate names what a consumer wired into the paths above must ALSO
-- require; it deliberately does not filter 'injFLatentVerdicts' itself.
-- Tier 0 marginal materialization is that consumer ('isNestedEnumInjF').
isCandidateBinaryEnumInjF :: Expr -> Expr -> Bool
isCandidateBinaryEnumInjF l r =
     isEnumerable (tags (getTypeInfo l)) && pType (getTypeInfo l) /= Deterministic
  && isEnumerable (tags (getTypeInfo r)) && pType (getTypeInfo r) /= Deterministic

-- | Every binary InjF node inside 'e', paired with the gate's verdict for
-- its own two operands, evaluated under the 'let'-scope actually in effect
-- at that node -- built by this same top-down walk via 'bindLatent', so
-- each node's free variables resolve against exactly the 'let's lexically
-- enclosing it. Deliberately not filtered to 'isCandidateBinaryEnumInjF'
-- (see its doc): the latent-sharing question is well-defined for any binary
-- InjF regardless of today's tag coverage, and a real consumer can intersect
-- with that narrower predicate itself. Exposed purely for direct testing
-- (see TestInternals); not wired into any compilation decision.
injFLatentVerdicts :: Expr -> [(ChainName, Bool)]
injFLatentVerdicts = latentVerdictWalk False

-- | 'injFLatentVerdicts' for the whole program, with bare (non-'let') lambda
-- parameters bound rather than left to default to "depends on no latent" --
-- and keyed by chain name, which is unique program-wide, so one map answers
-- for every function.
--
-- The parameter handling is the difference between an analysis and a
-- CONSUMER-GRADE analysis, and it is the unsound direction if skipped:
-- 'injFLatentVerdicts' walks each function body from an empty scope, so a
-- parameter read is an unbound 'Var' and 'latentDependencies' answers
-- @Just empty@ for it -- making @f x = x ++ x@ (and every latent that reaches
-- a callee through an argument) read as INDEPENDENT. That is harmless for the
-- pure analysis, whose fixtures all query 'main' where the 'let's are in
-- scope, but it is the unsound direction for a materializer, which sees the
-- callee's node too. 'bindLambdaParam' closes it -- defence in depth rather
-- than a live hole, since such a node is not a materialization candidate for
-- an independent reason spelled out there.
materializationVerdicts :: Program -> Map.Map ChainName Bool
materializationVerdicts p =
  Map.fromList (concatMap (latentVerdictWalk True . snd) (functions p))

-- | A binder enclosing a binary InjF node, outermost first: what
-- 'latentVerdictWalk' folds into the node's 'LatentScope'.
data LatentBinder = LetBinder String Expr | ParamBinder ChainName String

-- | Every binary InjF node of the program with the binders enclosing it and its
-- two operands, keyed by chain name: 'materializationVerdicts' before the
-- verdict is taken, so that it can be retaken /given/ some enumerated
-- bindings ('sharesLatentGiven').
materializationScopes :: Program -> Map.Map ChainName ([LatentBinder], Expr, Expr)
materializationScopes p = Map.fromList (concatMap (go [] . snd) (functions p))
  where
    go binders e = case node e of
      InjF _ [l, r] ->
        (chainName (getTypeInfo e), (reverse binders, l, r)) : go binders l ++ go binders r
      Apply (Expr _ (Lambda x lambdaBody)) v -> go (LetBinder x v : binders) lambdaBody ++ go binders v
      Lambda x lambdaBody -> go (ParamBinder (chainName (getTypeInfo e)) x : binders) lambdaBody
      _ -> concatMap (go binders) (getSubExprs e)

-- | The decomposability verdict of 'materializationVerdicts', retaken with the
-- enumerated bindings whose draws (by chain name) are in @fixed@ each holding
-- one value, as they do inside their enumeration loops: such a binding
-- contributes no latent, so two operands that read it and share nothing else
-- are independent given it. Consumed by Tier 0 materialization, whose tables
-- are built inside those loops; this is what lets
-- @draw c = readQ q in match c (readC s1) ++ match c (readC s2) ++ ..@
-- tabulate its per-slot chain inside the loop over @c@ (task
-- shared-enumerated-latent-loses-per-slot-factorization). A variable bound
-- from @c@ inside the loop is fixed along with it, since the scope is rebuilt
-- binder by binder rather than patched afterwards.
--
-- A lambda parameter is fixed along the same lines when every read of it the
-- verdict can see -- in either operand or in an enclosing @let@'s right-hand
-- side -- is 'Deterministic': it is then one value per call, an input rather
-- than a latent, and two operands that both read it are independent given it.
-- That is the shape draw sinking leaves for a product-ADT neural scene,
-- @hit (o1 (readScene s)) + hit (o2 (readScene s)) + ..@, every slot reading
-- the entry's symbol parameter (task
-- product-scene-discrete-count-enumerates-slot-patterns: untabulated, the
-- count enumerated the C(10, k) slot-hit patterns). Done here, not in
-- 'bindLambdaParam', so the occurrence pTypes are forced only at a candidate
-- node the whole-program verdict already flagged (see that function on why
-- forcing them program-wide is not affordable).
sharesLatentGiven :: Set.Set ChainName -> ([LatentBinder], Expr, Expr) -> Bool
sharesLatentGiven fixed (binders, l, r) = sharesEnumeratedLatent (foldl bind Map.empty binders) l r
  where
    bind scope (LetBinder x v)
      | chainName (getTypeInfo v) `Set.member` fixed = Map.insert x (Just Set.empty) scope
      | otherwise = bindLatent scope x v
    bind scope (ParamBinder cn x)
      | all ((== Deterministic) . pType . getTypeInfo) (concatMap (varReads x) visible) =
          Map.insert x (Just Set.empty) scope
      | otherwise = bindLambdaParam scope cn x
    visible = l : r : [v | LetBinder _ v <- binders]
    -- Every 'Var' node named @x@, shadowing ignored: a shadowed read is one
    -- more read to check, which can only keep the parameter's identity.
    varReads x e = case node e of
      Var y | y == x -> [e]
      _ -> concatMap (varReads x) (getSubExprs e)

-- | Shared implementation of the two walks above. @bindVars@ selects
-- whether a bare 'Lambda' binds its parameter ('bindLambdaParam') or is
-- descended into with the parameter left unbound (the historical behaviour
-- 'injFLatentVerdicts' pins).
latentVerdictWalk :: Bool -> Expr -> [(ChainName, Bool)]
latentVerdictWalk bindVars = go Map.empty
  where
    go scope e = case node e of
      InjF _ [l, r] ->
        (chainName (getTypeInfo e), sharesEnumeratedLatent scope l r) : go scope l ++ go scope r
      Apply (Expr _ (Lambda x lambdaBody)) v -> go (bindLatent scope x v) lambdaBody ++ go scope v
      Lambda x lambdaBody | bindVars -> go (bindLambdaParam scope (chainName (getTypeInfo e)) x) lambdaBody
      _ -> concatMap (go scope) (getSubExprs e)

-- | Bind a bare lambda parameter, whose value comes from a call site this walk
-- cannot see, to a latent identity of its OWN -- keyed by the binding lambda's
-- chain name, so it can never collide with a real draw's identity or with
-- another parameter's. Two operands that both read the same parameter therefore
-- report "may share" (@twice x = x ++ x@), while operands reading different
-- parameters stay independent -- which is what lets
-- @main a b = readMNist(a) ++ readMNist(b)@ be tabulated at all.
--
-- Two parameters of the same function CAN receive correlated arguments
-- (@pair (f u) (g u)@), and this does not see that: answering it needs a
-- whole-program call-site aliasing analysis Tier 0 deliberately does not build.
-- What makes the gap unreachable rather than merely unlikely is the compiler's
-- own convention for callee bodies: a parameter is typed 'Deterministic' there
-- (it is fixed by the enumeration the CALLER compiles a probabilistic argument
-- into), and 'Analysis' propagates no 'DiscreteValues' tag through one -- so any
-- operand whose randomness comes from a parameter fails
-- 'isCandidateBinaryEnumInjF' on both counts and never reaches the materializer.
-- Testing the parameter's own pType here instead would be the direct statement
-- of that argument, and is deliberately NOT done: forcing a parameter
-- occurrence's pType is exponential in the number of parameters (~7x per added
-- one, 9s at seven), a pre-existing property of the modality annotations that
-- no other consumer happens to hit.
bindLambdaParam :: LatentScope -> ChainName -> String -> LatentScope
bindLambdaParam scope lambdaCn x =
  Map.insert x (Just (Set.singleton ("param:" ++ lambdaCn ++ ":" ++ x))) scope
