-- | Binding resolution: the one application rule ('Binding'), entering a
-- callee's scope, field reads, and the inversion helpers the engines share.
module SPLL.IRCompiler.Binding (
  resolveBinding,
  bindInline,
  leadingArgBinding,
  replaceSpineArg,
  enterBindingScope,
  enteredScope,
  bindRenamed,
  deadBindingBodyCN,
  readsOnlyScope,
  calleeBodyInScope,
  deadBindingBody,
  equivalentChainName,
  inverseDerivative,
  theProbIndex,
  extendMetaForLambda,
  occursUnderFieldCtor,
  wildcardLeafSumBound,
  fieldStepIR,
  setFieldIR,
  tupleLeafPaths,
  varFieldReads,
  fieldDomainOf,
  reinferRecovered,
  usesThroughBinders,
  mkDeepAnyCheck,
  mkSafeInvExpr
) where

import SPLL.ReservedNames (distributionPrimitiveNames)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Analysis (enumerableDomain)
import SPLL.Typing.PType
import Data.Maybe
import Data.List (nub)
import SPLL.Typing.ForwardChaining
import SPLL.Typing.ModalityInfer (reinferGiven, lambdaParamLaw)
import SPLL.Semiring
import Control.Monad (forM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import SPLL.IRCompiler.Monad

-- | Resolve the application @l v@ ('Binding'). Partial like
-- 'equivalentLambda': the probabilistic 'Apply' arm checks first that the head
-- resolves to a lambda.
resolveBinding :: CompilerMetadata -> Expr -> Expr -> Binding
resolveBinding meta l v = Binding
  { bindHead = l, bindArg = v, bindLambda = lamCN, bindVar = param
  , bindBodyCN = bodyCN, bindTag = tag
  , bindOccs = fromMaybe [] (Map.lookup lamCN (lambdaVarOccurrences (fcData meta)))
  , bindBody = if null tag then reinferRecovered meta (recoveredVars meta) (exprWithCN meta bodyCN)
                             else exprWithCN meta bodyCN
  , bindOuterVars = snd (unwrapLambdas (fcData meta) bodyCN)
  , bindLeadingArg = False
  , bindScope = scope, bindTopLevel = fst <$> spine }
  where
    (lamCN, param, bodyCN, tag) = equivalentLambda "resolveBinding" (fcData meta) (chainName (getTypeInfo l))
    -- The top-level function whose lambda spine holds the resolved lambda, and
    -- the parameters of that spine enclosing it.
    spine = listToMaybe [ (f, ps) | (f, e) <- functions (compilingProgram meta)
                                  , Just ps <- [outerParams [] e] ]
    outerParams acc e@(Expr _ (Lambda p b))
      | chainName (getTypeInfo e) == lamCN = Just (reverse acc)
      | otherwise = outerParams (p : acc) b
    outerParams _ _ = Nothing
    scope
      | null tag = Just []
      | Just (f, params) <- spine = if null params then Just [] else do
          (Expr _ (Var g), args) <- Just (flattenApplySpine (reinferRecovered meta (recoveredVars meta) l))
          if g == f && length args == length params
               && all ((== Deterministic) . pType . getTypeInfo) args
            then Just (zip params args)
            else Nothing
      | readsOnlyScope meta [param] (exprWithCN meta bodyCN) = Just []
      | otherwise = Nothing

-- | Whether a binding's body factor may be compiled inline, in this scope: its
-- body is meaningful here ('bindScope' with no leading parameter to bind) and
-- it is not a top-level function's ('bindTopLevel'). A leading-argument
-- binding's body is the call it was taken from, which is meaningful here by
-- construction.
bindInline :: Binding -> Bool
bindInline b = bindLeadingArg b || (bindScope b == Just [] && isNothing (bindTopLevel b))

-- | A call of a top-level function whose leading arguments are not all
-- deterministic: @f a1 .. an@, saturated, with @a_i@ (@i < n@) the first
-- random argument. The binding of @f@'s i-th parameter to @a_i@ is taken
-- first, in parameter order, as a curried lambda in place binds
-- (@(\p1 -> (\p2 -> body) a2) a1@, which CalleeNormalize makes of
-- @(\p1 -> \p2 -> body) a1 a2@). Taking the last parameter first instead, as
-- the call's own outermost application would, leaves the body reading a
-- parameter bound to a random argument, which no engine can do.
--
-- The witness of @p_i@ is read from forward chaining's per-invocation copy of
-- @f@'s body, seeded at the call's observed result. The body factor is the
-- call itself with @a_i@ replaced by the recovered variable, so the next
-- random argument is bound by the next step, and once only the last one is
-- left, the ordinary binding of the call ('namedCall') takes over. Nothing is
-- inlined: @f@'s body is never compiled here by this binding, whose body is
-- the call.
--
-- 'Nothing' where the shape is not that. The body factor reads the recovered
-- variable as an argument rather than in a slot of the observation, so an
-- @ANY@ in its witnessing slot is refused at run time ('bindLeadingArg' makes
-- it not single-use).
leadingArgBinding :: CompilerMetadata -> Expr -> CompilerMonad (Maybe Binding)
leadingArgBinding meta expr0
  | not (isTArrowType (rType (getTypeInfo expr)))
  , (Expr _ (Var f), args) <- flattenApplySpine expr
  , Just (TArrow _ _, True) <- lookup f (typeEnv meta)
  , i <- length (takeWhile isDet args)
  , i < length args - 1
  , Just (Expr _ (Lambda param _)) <- lambdaAt i <$> lookup f (functions (compilingProgram meta))
  = do
      let prefix = spinePrefixes expr !! i
          ai = args !! i
          b0 = resolveBinding meta prefix ai
      fresh <- mkVariable param
      let wVar = Expr ((getTypeInfo ai) { pType = Deterministic }) (Var fresh)
      return (Just b0 { bindVar = fresh, bindBody = replaceSpineArg (length args - 1 - i) wVar expr
                      , bindOccs = [chainName (getTypeInfo ai)], bindOuterVars = []
                      , bindLeadingArg = True, bindScope = Just [], bindTopLevel = Nothing })
  | otherwise = return Nothing
  where
    expr = reinferRecovered meta (recoveredVars meta) expr0
    isDet a = pType (getTypeInfo a) == Deterministic
    lambdaAt :: Int -> Expr -> Expr
    lambdaAt 0 e = e
    lambdaAt k (Expr _ (Lambda _ b)) = lambdaAt (k - 1) b
    lambdaAt _ e = e
    -- The spine's own nodes, head first: @[f, f a1, f a1 a2, ..]@.
    spinePrefixes e@(Expr _ (Apply g _)) = spinePrefixes g ++ [e]
    spinePrefixes e = [e]

-- | Replace the argument @k@ applications up from the end of a curried call
-- spine (@k = 0@ is the last argument).
replaceSpineArg :: Int -> Expr -> Expr -> Expr
replaceSpineArg 0 w (Expr t (Apply g _)) = Expr t (Apply g w)
replaceSpineArg k w (Expr t (Apply g a)) = Expr t (Apply (replaceSpineArg (k - 1) w g) a)
replaceSpineArg _ _ e = e

-- | Make a binding's body meaningful in this scope: each leading parameter of
-- 'bindScope' is renamed to a fresh variable let-bound to its argument, and
-- recorded as recovered, exactly as 'enumerateAppliedLambda' binds its loop
-- variable. Answers the extended metadata and the renamed body, or 'Nothing'
-- where 'bindScope' says the body cannot be compiled here. No leading
-- parameter (the common case) binds nothing and answers the body as it is.
enterBindingScope :: CompilerMetadata -> Binding -> CompilerMonad (Maybe (CompilerMetadata, Expr))
enterBindingScope meta0 b = case bindScope b of
  Nothing -> return Nothing
  Just leading -> do
    renames <- forM leading $ \(param, arg) -> do
      fresh <- mkVariable param
      argIR <- toIRGenerate meta0 arg
      setVariables [(fresh, argIR)]
      return (param, fresh, rType (getTypeInfo arg))
    let meta = enteredScope (bindBody b) [ (param, fresh) | (param, fresh, _) <- renames ]
                 (bindRenamed meta0 [ (fresh, rty, arg) | ((_, arg), (_, fresh, rty)) <- zip leading renames ])
    let scopedBody = foldr (\(param, fresh, _) -> renameFreeVar param fresh) (bindBody b) renames
    return (Just (withBindingLaw meta b (bindVar b), scopedBody))

-- | Record a callee body entered here with these leading parameters renamed
-- to fresh names ('enteredScopes'), for the anchors materialized in it.
enteredScope :: Expr -> [(String, String)] -> CompilerMetadata -> CompilerMetadata
enteredScope _ [] meta = meta
enteredScope calleeBody renames meta =
  meta { enteredScopes = (nodeChainNames calleeBody, renames) : enteredScopes meta }

-- | The metadata once each of these fresh variables is let-bound to its
-- (deterministic) argument: in scope, recovered, and where the argument is a
-- lambda this compile can see, recorded in 'boundLambdas'.
bindRenamed :: CompilerMetadata -> [(String, RType, Expr)] -> CompilerMetadata
bindRenamed meta [] = meta
bindRenamed meta binds =
  meta { typeEnv = [ (fresh, (rty, hasInf rty)) | (fresh, rty, _) <- binds ] ++ typeEnv meta
       , boundLambdas = [ (fresh, lam) | (fresh, _, arg) <- binds, Just lam <- [visibleLambda arg] ]
                        ++ boundLambdas meta
       , lawEnv = foldr (\(fresh, _, arg) -> Map.insert fresh ((boundAt (nodeLaw meta arg)) { bvRecovered = True })) (lawEnv meta) binds }
  where
    hasInf (TArrow (TArrow _ _) _) = True
    hasInf _ = False
    visibleLambda e@(Expr _ (Lambda _ _)) = Just e
    visibleLambda (Expr _ (Var n)) = lookup n (boundLambdas meta)
    visibleLambda _ = Nothing

-- | The body of the lambda applied at an @Apply l v@ node, when the application
-- is a *dead* binding: the bound variable has no occurrence in that body, so the
-- argument's value is never read and @p(l v = s) = p(body = s)@.
--
-- 'Nothing' when the callee does not resolve to a lambda at all, or when the
-- binding is live. Total where 'equivalentLambda' is partial, because the
-- Bottom-argument arm asks the question about callees the tractable arms never
-- reach: an unknown chain name answers "not a dead binding" rather than
-- crashing. A chain name that resolves to a lambda but carries no
-- 'lambdaVarOccurrences' entry counts as dead, matching the @fromMaybe []@ the
-- probabilistic arm's own check uses.
deadBindingBodyCN :: CompilerMetadata -> Expr -> Maybe ChainName
deadBindingBodyCN meta l = do
  let fcd = fcData meta
  let cn = chainName (getTypeInfo l)
  _ <- Map.lookup cn (chainNameInfo fcd)
  (resolvedCN, info, _) <- findEquivalentExpression fcd cn
  bodyCN <- case info of
    LambdaInfo _ b -> Just b
    _ -> Nothing
  -- The body is compiled in the CURRENT scope, so it may only read names in
  -- scope here. A lambda reached through an application -- @(\a -> \b -> a)
  -- 0.0 v@, where @l@ is @(\a -> ..) 0.0@ -- has a body reading @a@, which
  -- that inner application binds and this scope never entered; compiling it
  -- here died on an unbound name (fuzz-admission-oracle-bugs item 7). Such a
  -- binding is left to the general arms.
  if null (fromMaybe [] (Map.lookup resolvedCN (lambdaVarOccurrences fcd))) && readsOnlyScope meta [] (exprWithCN meta bodyCN)
    then Just bodyCN
    else Nothing

-- | Does @e@ read only names in scope at this point of the compile (bound
-- locally, a top-level function, a distribution primitive), apart from
-- @binders@? Every arm that compiles a callee's lambda body in the caller's
-- scope -- the dead-binding shortcut, 'enumerateAppliedLambda' -- needs this:
-- a lambda reached through an application (@(\a -> \b -> a) 0.0 v@, where
-- the callee is @(\a -> ..) 0.0@) has a body reading @a@, which that inner
-- application binds and this scope never entered, and compiling it here died
-- on an unbound name (fuzz-admission-oracle-bugs item 7). Such a callee is
-- left to the arms that compile the application as a whole.
readsOnlyScope :: CompilerMetadata -> [String] -> Expr -> Bool
readsOnlyScope meta binders e = all inScope (Set.toList (freeVarsExpr e))
  where
    Program{functions=fs} = compilingProgram meta
    inScope v = v `elem` binders || isJust (lookup v (typeEnv meta)) || isJust (lookup v fs)
                || v `elem` distributionPrimitiveNames

-- | 'readsOnlyScope' for the lambda a callee resolves to, its own parameter
-- bound. A callee that resolves to no lambda is not this check's business.
calleeBodyInScope :: CompilerMetadata -> Expr -> Bool
calleeBodyInScope meta l = case findEquivalentExpression (fcData meta) (chainName (getTypeInfo l)) of
  Just (lamCN, LambdaInfo _ bodyCN, _) ->
    readsOnlyScope meta [ n | Expr _ (Lambda n _) <- [exprWithCN meta lamCN] ] (exprWithCN meta bodyCN)
  _ -> True

-- | 'deadBindingBodyCN' resolved to the body expression itself.
deadBindingBody :: CompilerMetadata -> Expr -> Maybe Expr
deadBindingBody meta l = exprWithCN meta <$> deadBindingBodyCN meta l

-- | As 'equivalentLambda', but where only the resolved chain name is wanted and
-- the expression behind it need not be a lambda.
equivalentChainName :: String -> FCData -> ChainName -> ChainName
equivalentChainName ctx fcd cn = case findEquivalentExpression fcd cn of
  Just (equivCN, _, _) -> equivCN
  Nothing -> error (ctx ++ ": chain name '" ++ cn ++ "' has no equivalent expression")

-- | The derivative of an inverse with respect to the variable it solves for.
-- Declared alongside the inverse body, so a miss is a gap in the InjF table.
inverseDerivative :: String -> String -> [(String, IRExpr)] -> IRExpr
inverseDerivative name v derivs = fromMaybe
  (error ("The inverse of InjF '" ++ name ++ "' declares no derivative for '" ++ v ++ "'"))
  (lookup v derivs)

-- | The index of the single probabilistic parameter, on the paths whose guard
-- has already established that there is exactly one.
theProbIndex :: String -> [Expr] -> Int
theProbIndex name params = fromMaybe
  (error ("InjF '" ++ name ++ "' was selected for single-probabilistic-parameter inference, but no parameter is probabilistic"))
  (getProbIndex params)

-- | Extend the type environment for a Lambda parameter: determine whether the
-- parameter itself takes a function argument (hasInference = True, so that
-- downstream Var lookups append _gen/_prob/_integ suffixes when the parameter is
-- applied) or is a plain value (False).
extendMetaForLambda :: CompilerMetadata -> TypeInfo -> String -> CompilerMetadata
extendMetaForLambda meta t name =
  let paramRType = case rType t of
        TArrow p _ -> p
        other -> error ("extendMetaForLambda: parameter '" ++ name ++ "' of a non-function type " ++ show other)
      hasInference = case paramRType of { TArrow (TArrow _ _) _ -> True; _ -> False }
  in meta { typeEnv = (name, (paramRType, hasInference)) : typeEnv meta
          , lawEnv = Map.insert name (boundAt (lambdaParamLaw t)) (lawEnv meta) }

-- | Whether variable @x@ occurs free in @e@ underneath a field constructor
-- (@Cons@, @TCons@, a user ADT constructor). Shadowing-aware, and followed
-- through binders as 'usesThroughBinders' is: in @draw y = x in (y, y + 1.0)@
-- the value of @x@ reaches two fields through @y@, and a single witness
-- would drop the other one.
occursUnderFieldCtor :: [ADTDecl] -> String -> Expr -> Bool
occursUnderFieldCtor adtDs x = go False
  where
    go under (Expr _ (Var n)) = under && n == x
    go _ (Expr _ (Lambda n _)) | n == x = False
    go under (Expr _ (Apply (Expr _ (Lambda y b)) arg))
      | y /= x && x `Set.member` freeVarsExpr arg && occursUnderFieldCtor adtDs y b = True
      | y == x = go under arg
      | otherwise = go under arg || go under b
    go under e@(Expr _ (InjF (Named n) _)) | isFieldConstructor adtDs n = any (go True) (getSubExprs e)
                                           | otherwise = any (go under) (getSubExprs e)
    go under e = any (go under) (getSubExprs e)

-- | How many fixed witnesses 'applyBinding''s sum over the wildcard leaves of
-- a point witness may take, the product of the leaves' domain sizes.
wildcardLeafSumBound :: Int
wildcardLeafSumBound = 64

-- | One step into a tuple: its first or its second field.
data FieldStep = FieldFst | FieldSnd deriving (Eq, Show)

fieldStepIR :: FieldStep -> IRExpr -> IRExpr
fieldStepIR FieldFst = IRDestruct AcFst
fieldStepIR FieldSnd = IRDestruct AcSnd

-- | @setFieldIR p k w@: the tuple @w@ with the field at path @p@ replaced by @k@.
setFieldIR :: [FieldStep] -> IRExpr -> IRExpr -> IRExpr
setFieldIR [] k _ = k
setFieldIR (FieldFst : r) k w = IRConstruct TgTuple [setFieldIR r k (IRDestruct AcFst w), IRDestruct AcSnd w]
setFieldIR (FieldSnd : r) k w = IRConstruct TgTuple [IRDestruct AcFst w, setFieldIR r k (IRDestruct AcSnd w)]

-- | The paths to the leaves of a (nested) tuple type; a non-tuple is its own
-- single leaf.
tupleLeafPaths :: RType -> [[FieldStep]]
tupleLeafPaths (Tuple a b) = map (FieldFst :) (tupleLeafPaths a) ++ map (FieldSnd :) (tupleLeafPaths b)
tupleLeafPaths _ = [[]]

-- | Each free occurrence of variable @x@ in @e@, as the tuple path its
-- @fst@/@snd@ projections read, and whether it sits in an output position:
-- reached from the root through field constructors, @if@ arms and let
-- bodies only, so its value is compared against the observation (as a
-- wildcard where the observation is one) rather than computed with.
--
-- The reads are followed through the spellings that only rename the value
-- (slow-tier follow-up of task any-mark-passed-as-recursive-call-state, the
-- rewrite-invariance net): a projection of @x@ bound by a @draw y = ..@
-- reads @x@ wherever the body reads @y@, and a projection of @x@ passed to a
-- top-level function reads @x@ wherever that function's body reads the
-- parameter (in output position only where the call itself is, and at most
-- @fuel@ calls deep). Where the fuel runs out, the argument counts as one
-- computing read of the whole projection, which is the conservative answer:
-- an extra read only costs the sum, it never makes it wrong.
varFieldReads :: Program -> [ADTDecl] -> String -> Expr -> [(Bool, [FieldStep])]
varFieldReads prog adtDs x0 = readsOf (4 :: Int) x0 True
  where
    -- the reads of @x@ in @e@, where @e@'s value is an output iff @out@
    readsOf fuel x = go
      where
        go out e | Just (n, p) <- projectionOf e = [(out, p) | n == x]
        go _ (Expr _ (Lambda n b)) = if n == x then [] else go False b
        go out (Expr _ (Apply (Expr _ (Lambda y b)) arg))
          | Just (n, p) <- projectionOf arg, n == x =
              aliased p (readsOf fuel y out b) ++ (if y == x then [] else go out b)
          | y == x = go False arg
          | otherwise = go False arg ++ go out b
        go out (Expr _ (IfThenElse c a b)) = go False c ++ go out a ++ go out b
        go out (Expr _ (InjF (Named n) args)) | isFieldConstructor adtDs n = concatMap (go out) args
        go out e
          | fuel > 0
          , (Expr _ (Var f), args@(_ : _)) <- flattenApplySpine e
          , f /= x
          , Just (params, fBody) <- lookup f (functions prog) >>= paramsN (length args) =
              concat [ case projectionOf a of
                         Just (n, p) | n == x -> aliased p (readsOf (fuel - 1) prm out fBody)
                         _ -> go False a
                     | (a, prm) <- zip args params ]
        go _ e = concatMap (go False) (getSubExprs e)
    aliased p rs = [ (o, p ++ q) | (o, q) <- rs ]
    projectionOf (Expr _ (Var n)) = Just (n, [])
    projectionOf (Expr _ (InjF (Named "fst") [a])) = fmap (++ [FieldFst]) <$> projectionOf a
    projectionOf (Expr _ (InjF (Named "snd") [a])) = fmap (++ [FieldSnd]) <$> projectionOf a
    projectionOf _ = Nothing
    paramsN :: Int -> Expr -> Maybe ([String], Expr)
    paramsN 0 b = Just ([], b)
    paramsN n (Expr _ (Lambda v b)) = (\(vs, r) -> (v : vs, r)) <$> paramsN (n - 1) b
    paramsN _ _ = Nothing

-- | The finite set of values the field at path @p@ of @e@'s value can take,
-- where the program states one: the node's own enumerable domain, else
-- through a tuple constructor, a @fst@/@snd@ projection, both arms of an
-- @if@, a let body, or the body of a called (or nullary) top-level function
-- (at most @fuel@ calls deep). A superset is
-- sound for a sum over it (a value the field cannot take has no mass).
fieldDomainOf :: Program -> Int -> Expr -> [FieldStep] -> Maybe [Value]
fieldDomainOf prog = go
  where
    go fuel e path
      | fuel <= (0 :: Int) = Nothing
      | Just mv <- enumerableDomain (tags (getTypeInfo e)) = project mv path
      | otherwise = case e of
          Expr _ (InjF (Named "TCons") [a, b]) -> case path of
            FieldFst : r -> go fuel a r
            FieldSnd : r -> go fuel b r
            [] -> Nothing
          Expr _ (IfThenElse _ a b) -> (\xs ys -> nub (xs ++ ys)) <$> go fuel a path <*> go fuel b path
          Expr _ (InjF (Named "fst") [a]) -> go fuel a (FieldFst : path)
          Expr _ (InjF (Named "snd") [a]) -> go fuel a (FieldSnd : path)
          Expr _ (Apply (Expr _ (Lambda _ b)) _) -> go fuel b path
          _ | (Expr _ (Var f), args) <- flattenApplySpine e
            , Just fBody <- lookup f (functions prog)
            , Just b <- stripN (length args) fBody -> go (fuel - 1) b path
          _ -> Nothing
    project mv [] | multiValueIsFinite mv = Just (multiValueToValueList mv)
                  | otherwise = Nothing
    project (MultiTuple a _) (FieldFst : r) = project a r
    project (MultiTuple _ b) (FieldSnd : r) = project b r
    project _ _ = Nothing
    stripN :: Int -> Expr -> Maybe Expr
    stripN 0 b = Just b
    stripN n (Expr _ (Lambda _ b)) = stripN (n - 1) b
    stripN _ _ = Nothing

-- | Re-annotate an expression for dispatch, given that the named variables
-- have been recovered by enclosing constructs -- a witness fold, an
-- enumeration loop, a residue factor (design law-carrying-modality §D,
-- @modality-witnessed-inference@ at the codegen level): the sub-inference
-- must see a recovered variable as Deterministic so e.g. an inner
-- @plus[y, z]@ with both operands recovered routes to generate-and-compare
-- instead of an inversion arm that needs a random operand.
--
-- This is 'SPLL.Typing.ModalityInfer.reinferGiven', the modality engine
-- itself, run under an environment binding those variables 'Exact'; it used
-- to be a syntactic re-typing (@retypeDetGiven@) of the names and the pure
-- 'InjF'/@if@ nodes over them, which did not follow a binder: after
-- @draw y = x * 2.0@ with @x@ recovered, @y@ kept its standalone 'PNormal'
-- and the catch-all handed @Var y@ to 'toIRNormalParams'.
reinferRecovered :: CompilerMetadata -> [String] -> Expr -> Expr
reinferRecovered _ [] e = e
reinferRecovered meta names e = reinferGiven (reinferContext meta) names e

-- | How many places the value of variable @x@ reaches in @e@: its free
-- occurrences, where an occurrence inside the value of a @draw y = ..@ counts
-- once for each use of @y@ in turn (at least once, so a dead binding reading
-- @x@ still counts as a use). The witness fold's sink test asks this rather
-- than the syntactic occurrence count, which an alias hides.
usesThroughBinders :: String -> Expr -> Int
usesThroughBinders x = go
  where
    go (Expr _ (Var n)) = if n == x then 1 else 0
    go (Expr _ (Lambda y b)) = if y == x then 0 else go b
    go (Expr _ (Apply (Expr _ (Lambda y b)) arg))
      | y == x = go arg
      | otherwise = go arg * max 1 (usesThroughBinders y b) + go b
    go e = sum (map go (getSubExprs e))

-- | True when `sample` is VAny or contains VAny one level inside a Left/Right wrapper.
-- Used to detect samples like (Left ANY) that would crash arithmetic inverses.
-- Only the Either tag test and payload accessors are used here; these are already VAny-safe.
mkDeepAnyCheck :: RType -> IRExpr -> IRExpr
mkDeepAnyCheck (TEither _ _) sample =
  IRIf (IRUnaryOp OpIsAny sample)
    (IRConst (VBool True))
    (IRIf (IRDestruct AcIsLeft sample)
      (IRUnaryOp OpIsAny (IRDestruct AcFromLeft sample))
      (IRUnaryOp OpIsAny (IRDestruct AcFromRight sample)))
mkDeepAnyCheck _ sample = IRUnaryOp OpIsAny sample

-- | For a deconstructing Either InjF, returns a safe alternative invExpr that avoids
-- arithmetic on VAny. The result mirrors the arm of `sample` but uses VAny as the inner
-- value, so downstream OpEq comparisons handle it correctly.
mkSafeInvExpr :: IRExpr -> IRExpr
mkSafeInvExpr sample =
  IRIf (IRDestruct AcIsLeft sample)
    (IRConstruct TgLeft [IRConst VAny])
    (IRConstruct TgRight [IRConst VAny])

getProbIndex :: HasCallStack => [Expr] -> Maybe Int
--getProbIndex es | traceShow es False = undefined
getProbIndex es =
  case filter (\(p, _) -> p == Integrate || p == PNormal || p == PLogNormal) zipped of
    [(_, i)] -> Just i
    [] -> Nothing
    -- Invariant, not a refusal (task static-refusals-become-absent-variants): guards count probabilistic parameters first (a miss is filed: bare-equality-of-two-neural-reads-crashes).
    _ -> error "More than one probabilistic argument found"
  where
    pt x = pType (getTypeInfo x)
    pTypes = map pt es
    zipped = zip pTypes [0..]
