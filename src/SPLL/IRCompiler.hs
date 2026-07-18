module SPLL.IRCompiler (
  envToIR,
  envToIRUnoptimized,
  stripBranchCount,
  toIRNormal
)where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.IROptimizer
import PredefinedFunctions
import SPLL.Typing.PType
import Data.Maybe
import Data.Either (isRight, partitionEithers)
import Data.List (isPrefixOf, (\\), find, elemIndex, nub)
import Data.Char (isDigit)
import Data.Functor ((<&>))
import Control.Monad.Writer.Lazy
import SPLL.AutoNeural
import SPLL.Typing.ForwardChaining
import SPLL.Typing.AlgebraicDataTypes
import Data.Bifunctor (Bifunctor(bimap))
import Utils
import Control.Monad (foldM, forM, when)
import Control.Monad.State.Strict (StateT, evalStateT, get, gets, put, modify)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)

type CompilerMonad a = WriterT [(String, IRExpr)] Supply a

type CompilationResult = (IRExpr, IRExpr, IRExpr)

-- (name, ((RType of (Var name)), (Has _gen _prop _integ (if applicable) functions)))
type TypeEnv = [(String, (RType, Bool))]

data CompilerMetadata = CompilerMetadata {
  compilerConfig :: CompilerConfig,
  fcData :: FCData,
  typeEnv :: TypeEnv,
  adtDecls :: [ADTDecl],
  compilingProgram :: Program,
  accProb :: IRExpr,
  -- | Variables already recovered by an enclosing body-factor fold. Body
  -- expressions are re-fetched from the (original) program at every fold
  -- level, so the deterministic re-typing must be replayed with the full set.
  recoveredVars :: [String]
}

envToIR :: CompilerConfig -> FCData -> Program -> IREnv
envToIR conf fcDat p
  | any (null . chainName . getTypeInfo . snd) (functions p) =
      error "envToIR: one or more top-level expressions have empty chainNames — did you call annotateProg before envToIR?"
  | otherwise =
      let unopt   = envToIRUnoptimized conf fcDat p
          stripped = if countBranches conf then unopt else stripBranchCount unopt
      in optimizeEnv conf stripped

-- The FCData certificate is built once in 'Prelude.compile' and threaded in,
-- rather than rebuilt here (modality-split-forwardchaining).
envToIRUnoptimized :: CompilerConfig -> FCData -> Program -> IREnv
envToIRUnoptimized conf@CompilerConfig{noIntegrate=noInteg, noProbability=noProb, noGenerate=noGen} fcDat p@Program{adts=adts} = IREnv (
  map (makeAutoNeural adts conf (encodeDecls p)) (neurals p) ++
  concatMap (\(name, binding) ->
    let typeEnv = getGlobalTypeEnv p
        bindingParamNames = extractParamNames binding
        pt = pType $ getTypeInfo binding
        -- Every logit-representable top-level function gets its own encodeFun, keyed to its
        -- own <name>_prob / <name>_normal functions, with no neural declaration required
        -- (task encode-per-function-endpoints; `main` is just the name == "main" case).
        -- Lazily references baseFunGroup/tupleNormalFuns to read whether this function's
        -- prob/normal functions were generated; non-representable functions keep
        -- encodeFun = Nothing (purely additive, no new error surface).
        encodeF =
              makeTopLevelEncodeFun adts conf (encodeDecls p)
                name
                (rType (getTypeInfo (stripLambdas binding)))
                bindingParamNames
                (isJust (probFun baseFunGroup))
                (baseFunGroup : tupleNormalFuns)
        -- The type the query value must structurally match: the function's result
        -- type with any outer parameter lambdas stripped. Backs the query-type guard.
        returnRType = rType (getTypeInfo (stripLambdas binding))
        -- Wrap a value-returning inference body so a wrong-typed query value fails
        -- with a clear diagnostic (see IRConformsTo) instead of a silent bogus
        -- number or a deep "not a boolean" panic. `sample` is already bound by the
        -- enclosing IRLambda. Gated on checkQueryType (default on, independent of -O).
        -- Pushed under any outer parameter lambdas (via guardUnderLambdas) so those
        -- stay at the function head where codegen collects them into the signature.
        guardQuery kind = guardUnderLambdas
          where
            guardUnderLambdas (IRLambda n b) = IRLambda n (guardUnderLambdas b)
            guardUnderLambdas bodyExpr
              | checkQueryType conf =
                  IRIf (IRConformsTo returnRType (IRVar "sample"))
                       bodyExpr
                       (IRError (kind ++ "(" ++ name ++ "): query value does not conform to return type " ++ show returnRType))
              | otherwise = bodyExpr
        -- Appended to the guarded function's doc (emitted as a comment by codegen)
        -- so the generated code points at the flag that produced the check.
        guardNote = if checkQueryType conf
                    then "\nQuery-type guard active: rejects a query value not matching return type " ++ show returnRType ++ " (disable with --noTypeCheck)."
                    else ""
        appendDoc note (e, d) = (e, d ++ note)
        baseFunGroup = IRFunGroup {groupName=name, encodeFun=encodeF,
         integFun =
          if not noInteg && (pt == Deterministic || pt == Integrate || pt == PNormal || pt == PLogNormal) then
            Just (appendDoc guardNote (toIntegDecl name (IRLambda "sample" (guardQuery "cdf" (runCompile (meta typeEnv) (toIRInferenceSave (meta typeEnv) True binding (IRVar "sample")))))))
          else Nothing,
          probFun =
            if not noProb && (pt == Deterministic || pt == Integrate || pt == PNormal || pt == PLogNormal) then
              let metaBase = meta typeEnv
                  body m = runCompile m (toIRInferenceSave m False binding (IRVar "sample"))
              in Just (appendDoc guardNote $ toProbDecl name $ case topKThreshold conf of
                   Just _ -> IRLambda "sample" $ IRLambda "acc_prob" $ guardQuery "p" $ body (metaBase { accProb = IRVar "acc_prob" })
                   Nothing -> IRLambda "sample" $ guardQuery "p" $ body metaBase)
            else Nothing,
          genFun =
            if not noGen then
              Just (toGenDecl name (fst $ evalSupply $ runWriterT $ toIRGenerate (meta typeEnv) binding))
            else
              Nothing,
          normalFun =
            if (pt == PNormal || pt == PLogNormal) && isNormalExtractable binding then
              Just (toNormalDecl name (compileNormalExpr (meta typeEnv) binding))
            else
              Nothing,
          groupDoc="Function group " ++ name}
        -- Generate per-component normal functions for tuple outputs
        tupleNormalFuns = generateTupleComponentNormalFunctions (meta typeEnv) name binding
    in [baseFunGroup] ++ tupleNormalFuns) (functions p))
  adts
  (case topKThreshold conf of
    Just thresh -> [("TOP_K_CUTOFF", VFloat thresh)]
    Nothing     -> [])

  where
    toGenDecl name expr = (expr, "Generates a random sample of the " ++ name ++ " function")
    toProbDecl name expr =
      (expr, "Calculates the probability of the sample parameter being returned from the " ++ name ++ "function")
    toIntegDecl name expr = (expr, "Calculates the probability of the sample parameter being less than or equal to the " ++ name ++ " function")
    toNormalDecl name expr = (expr, "Returns (mu, sigma) normal distribution parameters for the " ++ name ++ " function")
    meta typeEnv = CompilerMetadata conf fcDat typeEnv adts p (IRConst (VFloat 1.0)) []
    extractParamNames (Lambda _ name body) = name : extractParamNames body
    extractParamNames _ = []
    stripLambdas (Lambda _ _ body) = stripLambdas body
    stripLambdas e = e


runCompile :: CompilerMetadata -> CompilerMonad CompilationResult -> IRExpr
runCompile meta codeGen = generateLetInBlock meta (evalSupply $ runWriterT $ do
  (p, d, bc) <- codeGen
  case p of
    IRLambda _ _ -> return (p, d, bc)
    _ -> tell [("l_p", p), ("l_d", d), ("l_bc", bc)] >>
                return (IRVar "l_p", IRVar "l_d", IRVar "l_bc")
  --
  )

generateLetInBlock :: CompilerMetadata -> (CompilationResult, [(String, IRExpr)]) -> IRExpr
generateLetInBlock _ codeGen =
  case m of
    (IRLambda _ _) -> (foldr (\(var, val) expr  -> IRLetIn var val expr) m binds) --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> generateLetInExpr binds (IRTCons m (IRTCons dim bc))
  where
    ((m, dim, bc), binds) = codeGen

generateLetInExpr ::  [(Varname, IRExpr)] -> IRExpr -> IRExpr
generateLetInExpr binds e = foldr (\(var, val) expr  -> IRLetIn var val expr) e binds

-- | Compile a PNormal/PLogNormal expression to a function returning (mu, sigma) as
-- an IRTCons pair.  Lambda wrappers are preserved so the result has the same arity
-- as the original binding; parameter types are added to the type environment so that
-- inner Var references resolve correctly.
compileNormalExpr :: CompilerMetadata -> Expr -> IRExpr
compileNormalExpr meta (Lambda _ name subExpr) =
  let newMeta = meta { typeEnv = (name, (rType (getTypeInfo subExpr), False)) : typeEnv meta }
  in IRLambda name (compileNormalExpr newMeta subExpr)
compileNormalExpr meta expr =
  let ((mu, sigma), binds) = evalSupply $ runWriterT $ toIRNormal meta expr
  in generateLetInExpr binds (IRTCons mu sigma)

-- | True when the expression (with lambdas stripped) has its own toIRInference
-- handler and cannot be processed by toIRNormalParams.  Mirrors the
-- hasOwnInferenceHandler predicate used by toIRInference.
isNormalExtractable :: Expr -> Bool
isNormalExtractable (Lambda _ _ body)            = isNormalExtractable body
isNormalExtractable (Apply  _ _ _)               = False
isNormalExtractable (InjF _ (Named "Cons")  _)   = False
isNormalExtractable (InjF _ (Named "TCons") _)   = False
isNormalExtractable _                            = True

-- | Generate per-component normal functions for tuple expressions.
-- For a tuple (fst, snd) where both parts are PNormal/PLogNormal, generates:
--   {name}_normal_fst :: extracting normal params from fst
--   {name}_normal_snd :: extracting normal params from snd
-- Lambda wrappers are stripped to reach the TCons, then re-applied to each component.
-- Functions are registered via the _component_ prefix mechanism in reduceIREnv.
generateTupleComponentNormalFunctions :: CompilerMetadata -> String -> Expr -> [IRFunGroup]
generateTupleComponentNormalFunctions meta baseName expr = go expr id
  where
    go (Lambda ti name body) wrap = go body (\e -> wrap (Lambda ti name e))
    go (InjF _ (Named "TCons") [fstExpr, sndExpr]) wrap =
      catMaybes
        [ generateComponentNormalFunction meta (baseName ++ "_normal_fst") (wrap fstExpr) (getTypeInfo fstExpr)
        , generateComponentNormalFunction meta (baseName ++ "_normal_snd") (wrap sndExpr) (getTypeInfo sndExpr)
        ]
    go _ _ = []

-- | Generate a single per-component normal function if the expression is extractable and PNormal/PLogNormal.
-- Stored in normalFun field and registered via _component_ prefix in reduceIREnv (bare name, no suffix).
generateComponentNormalFunction :: CompilerMetadata -> String -> Expr -> TypeInfo -> Maybe IRFunGroup
generateComponentNormalFunction meta fullName expr ti
  | (pType ti == PNormal || pType ti == PLogNormal) && isNormalExtractable expr =
      let compiled = compileNormalExpr meta expr
      in Just $ IRFunGroup ("_component_" ++ fullName)
           Nothing
           Nothing
           Nothing
           Nothing
           (Just (compiled, "Per-component normal extraction for tuple element: " ++ fullName))
           ""
  | otherwise = Nothing

-- Return type (name, rType, hasInferenceFunctions)
getGlobalTypeEnv :: Program -> TypeEnv
getGlobalTypeEnv p = funcEnv ++ implicitFuncEnv ++ neuralEnv
  where funcEnv = map (\(name, expr) -> (name, (rType (getTypeInfo expr), True))) (functions p)
        implicitFuncEnv = map (\(name, rt) -> (name, (rt, False))) (implicitFunctionsRTypeProg p)
        neuralEnv = map (\(name, rt, _) -> (name, (rt, False))) (neurals p)

mkVariable :: String -> CompilerMonad  Varname
mkVariable suffix = do
  varID <- demandUniqueNumber
  return ("l_" ++ show varID ++ "_" ++ suffix)

setVariables :: [(String, IRExpr)] -> CompilerMonad ()
setVariables = tell

-- | True if any tag on the expression marks it as enumerable (carries DiscreteValues).
-- A MultiValue with a continuous (Real) leaf is refused: it has no finite enumeration,
-- and walking its discrete residue would silently drop the continuous probability mass.
-- (The enum-annotation pass already declines to produce such tags; this guards any
-- other producer.)
isEnumerable :: [Tag] -> Bool
isEnumerable = any isDiscrete
  where isDiscrete (DiscreteValues mv) = not (multiValueContainsContinuous mv)
        isDiscrete _                   = False

-- | True when `Apply l v` should be compiled by enumerating the argument's discrete
-- support (marginalising over a random draw). This requires:
--   * the applied function is conditional (its body is enumerable-compilable, not
--     something forward chaining must algebraically invert), and
--   * the argument is a *probabilistic* discrete draw -- it carries DiscreteValues and
--     is not Deterministic. The Deterministic exclusion is essential: a constant or
--     deterministic input (e.g. `dice 4.0`, where `4.0` carries a DiscreteValues tag)
--     is a fixed value with nothing to marginalise over, and must take the ordinary
--     application path instead of being enumerated.
isEnumerableApplication :: Expr -> Expr -> Bool
isEnumerableApplication l v =
     IsConditional `elem` tags (getTypeInfo l)
  && isEnumerable (tags (getTypeInfo v))
  && pType (getTypeInfo v) /= Deterministic

const0 :: IRExpr
const0 = IRConst (VFloat 0)

-- | Map the polymorphic InjF name to the concrete integer variant when the
-- resolved return type is TInt.  For all other types the name is unchanged.
-- Safe to pattern-match only on TInt: the CNum class constraint check upstream
-- has already rejected non-numeric types, so only TFloat and TInt reach here.
resolveInjF :: RType -> String -> String
resolveInjF TInt "plus" = "plusI"
resolveInjF TInt "mult" = "multI"
resolveInjF TInt "neg"  = "negI"
resolveInjF _    n      = n

-- | True if the named InjF is forward-only (no inverse declarations), e.g. and/or.
-- Such ops cannot be inverted to recover an operand from the result, so their
-- discrete inference enumerates both operand grids and filters by the forward value
-- rather than inverting one side.
isForwardOnly :: [ADTDecl] -> String -> Bool
isForwardOnly adts name = case lookup name (globalFEnv adts) of
  Just (FPair _ []) -> True
  _                 -> False

-- | Extend the type environment for a Lambda parameter: determine whether the
-- parameter itself takes a function argument (hasInference = True, so that
-- downstream Var lookups append _gen/_prob/_integ suffixes when the parameter is
-- applied) or is a plain value (False).
extendMetaForLambda :: CompilerMetadata -> TypeInfo -> String -> CompilerMetadata
extendMetaForLambda meta t name =
  let (TArrow paramRType _) = rType t
      hasInference = case paramRType of { TArrow (TArrow _ _) _ -> True; _ -> False }
  in meta { typeEnv = (name, (paramRType, hasInference)) : typeEnv meta }

-- | True if the expression is a literal lambda (as opposed to a function reached
-- through the higher-order equivalence machinery, e.g. a Var or an Apply result).
isLambdaExpr :: Expr -> Bool
isLambdaExpr (Lambda {}) = True
isLambdaExpr _ = False

-- | Re-type a body factor for dispatch, given that the named variables have
-- been recovered by enclosing folds (design @modality-witnessed-inference@,
-- codegen level: the body sub-inference must see a recovered variable as
-- Deterministic so e.g. an inner @plus[y, z]@ with both operands recovered
-- routes to generate-and-compare instead of an inversion arm that needs a
-- random operand). Occurrences of the recovered variables become
-- 'Deterministic'; pure 'InjF' nodes whose operands are all deterministic
-- follow. Shadowing lambdas stop the substitution for their own name. Other
-- node kinds keep their annotations — their arms dispatch on operand types.
retypeDetGiven :: [String] -> Expr -> Expr
retypeDetGiven [] e = e
retypeDetGiven names e = go names e
  where
    go ns (Var ti n) | n `elem` ns = Var (ti {pType = Deterministic}) n
    go ns (Lambda ti n body) = Lambda ti n (go (filter (/= n) ns) body)
    go ns ex =
      let ex' = setSubExprs ex (map (go ns) (getSubExprs ex))
      in case ex' of
           InjF ti f params
             | all ((== Deterministic) . pType . getTypeInfo) params ->
                 InjF (ti {pType = Deterministic}) f params
           _ -> ex'

-- | True if the expression contains a source of randomness: a reference to a
-- non-deterministic variable (the builtin distributions @Uniform@/@Normal@ are
-- 'Var' nodes, as are references to probabilistic top-level functions) or a
-- neural-network read. Run this on a body already passed through
-- 'retypeDetGiven', so recovered variables are 'Deterministic' and don't count.
containsRandomSource :: Expr -> Bool
containsRandomSource e = isSource e || any containsRandomSource (getSubExprs e)
  where
    isSource (Var ti _)  = pType ti /= Deterministic
    isSource (ReadNN {}) = True
    isSource _           = False

-- | Drop dead let-bindings from a forward-chaining inverse expression.
-- 'toValueExpr' deliberately over-emits: its letin chain can bind clause
-- values unrelated to the recovered variable ("superfluous clauses ... easily
-- detected by an optimizer"). Relying on the optimizer for that is not just a
-- performance matter: 'IRLetIn' is strict, so under a marginal (ANY) query an
-- unrelated binding can run arithmetic on VAny and crash an unoptimized run
-- even though the live inverse path never touches the ANY slot. Prune to the
-- live chain at emission time.
pruneDeadLetIns :: IRExpr -> IRExpr
pruneDeadLetIns e =
  let e' = irMap prune e
  in if e' == e then e' else pruneDeadLetIns e'
  where
    prune (IRLetIn n _ b) | not (freeInIR n b) = b
    prune x = x

negInf :: IRExpr
negInf = IRConst (VFloat (-9999999))

posInf :: IRExpr
posInf = IRConst (VFloat 9999999)

-- | True if the given variable name appears free in an IR expression.
freeInIR :: String -> IRExpr -> Bool
freeInIR v (IRVar v')           = v == v'
freeInIR v (IRLetIn n val body) = freeInIR v val || (v /= n && freeInIR v body)
freeInIR v (IRLambda n body)    = v /= n && freeInIR v body
freeInIR v (IRApply f a)        = freeInIR v f  || freeInIR v a
freeInIR v (IROp _ a b)         = freeInIR v a  || freeInIR v b
freeInIR v (IRUnaryOp _ e)      = freeInIR v e
freeInIR v (IRIf c a b)         = freeInIR v c  || freeInIR v a  || freeInIR v b
freeInIR v (IRTCons a b)        = freeInIR v a  || freeInIR v b
freeInIR v (IRTFst a)           = freeInIR v a
freeInIR v (IRTSnd a)           = freeInIR v a
freeInIR v (IRHead a)           = freeInIR v a
freeInIR v (IRTail a)           = freeInIR v a
freeInIR v (IRLeft a)           = freeInIR v a
freeInIR v (IRRight a)          = freeInIR v a
freeInIR v (IRFromLeft a)       = freeInIR v a
freeInIR v (IRFromRight a)      = freeInIR v a
freeInIR v (IRIsLeft a)         = freeInIR v a
freeInIR v (IRIsRight a)        = freeInIR v a
freeInIR v (IRCons a b)         = freeInIR v a  || freeInIR v b
freeInIR v (IRElementOf a b)    = freeInIR v a  || freeInIR v b
freeInIR v (IRIndex a b)        = freeInIR v a  || freeInIR v b
freeInIR v (IRMap f x)          = freeInIR v f  || freeInIR v x
freeInIR v (IREnumSum n _ body) = v /= n && freeInIR v body
freeInIR v (IRDensity _ x)      = freeInIR v x
freeInIR v (IRCumulative _ x)   = freeInIR v x
freeInIR v (IRIsPossible _ x)   = freeInIR v x
freeInIR v (IRTheta x _)        = freeInIR v x
freeInIR v (IRSubtree x _)      = freeInIR v x
freeInIR _ _                    = False

-- | Flatten all leading IRLetIn bindings into a list, returning the core expression.
flattenLetIns :: IRExpr -> ([(String, IRExpr)], IRExpr)
flattenLetIns (IRLetIn n v body) = let (rest, core) = flattenLetIns body in ((n, v) : rest, core)
flattenLetIns e = ([], e)

-- | Rebuild an IRLetIn chain from a list of bindings around a core expression.
buildLetIns :: [(String, IRExpr)] -> IRExpr -> IRExpr
buildLetIns binds core = foldr (\(n, v) e -> IRLetIn n v e) core binds

-- | Split the bindings of an IRLetIn chain into those that are loop-invariant
-- (do not mention `loopVar` and do not depend on any variant binding) and the
-- rest.  Both sublists preserve their original relative order.  Returns
-- (invariant bindings, remaining IRExpr with variant bindings).
hoistInvariantBindings :: String -> IRExpr -> ([(String, IRExpr)], IRExpr)
hoistInvariantBindings loopVar expr =
  let (allBinds, core) = flattenLetIns expr
      (invBinds, varBinds) = partition' loopVar allBinds []
  in (invBinds, buildLetIns varBinds core)
  where
    partition' _ [] _ = ([], [])
    partition' lv ((n, v) : rest) varNames
      | not (lv `freeInIR` v) && not (any (`freeInIR` v) varNames) =
          let (inv, var) = partition' lv rest varNames
          in ((n, v) : inv, var)
      | otherwise =
          let (inv, var) = partition' lv rest (n : varNames)
          in (inv, (n, v) : var)

-- | True when `sample` is VAny or contains VAny one level inside a Left/Right wrapper.
-- Used to detect samples like (Left ANY) that would crash arithmetic inverses.
-- Only IRIsLeft/IRFromLeft/IRFromRight are used here; these are already VAny-safe.
mkDeepAnyCheck :: RType -> IRExpr -> IRExpr
mkDeepAnyCheck (TEither _ _) sample =
  IRIf (IRUnaryOp OpIsAny sample)
    (IRConst (VBool True))
    (IRIf (IRIsLeft sample)
      (IRUnaryOp OpIsAny (IRFromLeft sample))
      (IRUnaryOp OpIsAny (IRFromRight sample)))
mkDeepAnyCheck _ sample = IRUnaryOp OpIsAny sample

-- | For a deconstructing Either InjF, returns a safe alternative invExpr that avoids
-- arithmetic on VAny. The result mirrors the arm of `sample` but uses VAny as the inner
-- value, so downstream OpEq comparisons handle it correctly.
mkSafeInvExpr :: IRExpr -> IRExpr
mkSafeInvExpr sample =
  IRIf (IRIsLeft sample)
    (IRLeft (IRConst VAny))
    (IRRight (IRConst VAny))

renameVar :: String -> String -> IRExpr -> IRExpr
renameVar old new = irMap (renameVar' old new)

renameVar' :: String -> String -> IRExpr -> IRExpr
renameVar' old new (IRVar n) | n == old = IRVar new
renameVar' _ _ x = x

toIRInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad CompilationResult
toIRInferenceSave meta cumulative (Lambda t name subExpr) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- lift (runWriterT (toIRInferenceSave newMeta cumulative subExpr sample)) <&> generateLetInBlock meta
  return (IRLambda name irTuple, const0, const0)
toIRInferenceSave meta cumulative expr sample = do
  ((probExpr, probDim, probBranches), letins) <- lift $ runWriterT $ toIRInference meta cumulative expr sample
  let wrap inner = generateLetInExpr letins inner
  return ( IRIf (IRUnaryOp OpIsAny sample) (IRConst (VFloat 1)) (wrap probExpr)
         , IRIf (IRUnaryOp OpIsAny sample) const0 (wrap probDim)
         , IRIf (IRUnaryOp OpIsAny sample) const0 (wrap probBranches)
         )


-- | Dispatch to the appropriate param extractor based on PType.
-- Returns (mu, sigma) for PNormal and (mu_log, sigma) for PLogNormal.
toIRNormal :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
toIRNormal meta e
  | pType (getTypeInfo e) == PNormal    = toIRNormalParams meta e
  | pType (getTypeInfo e) == PLogNormal = toIRLogNormalParams meta e
  | otherwise = error $ "toIRNormal: expression is neither PNormal nor PLogNormal: " ++ show (pType (getTypeInfo e))

irSqrt :: IRExpr -> IRExpr
irSqrt x = IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog x))

-- | Recursively extract (mu, sigma) as IRExprs from a PNormal-typed expression.
toIRNormalParams :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
toIRNormalParams _ (Var _ "Normal") = return (IRConst (VFloat 0), IRConst (VFloat 1))
toIRNormalParams meta (InjF _ (Named "plus") [e0, e1])
  | pType (getTypeInfo e0) == PNormal, pType (getTypeInfo e1) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      (mu1, s1) <- toIRNormalParams meta e1
      return (IROp OpPlus mu0 mu1, irSqrt (IROp OpPlus (IROp OpMult s0 s0) (IROp OpMult s1 s1)))
toIRNormalParams meta (InjF _ (Named "plus") [e0, e1])
  | pType (getTypeInfo e0) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpPlus mu0 det1, s0)
toIRNormalParams meta (InjF _ (Named "plus") [e0, e1])
  | pType (getTypeInfo e1) == PNormal = do
      (mu1, s1) <- toIRNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpPlus mu1 det0, s1)
toIRNormalParams meta (InjF _ (Named "mult") [e0, e1])
  | pType (getTypeInfo e0) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpMult mu0 det1, IROp OpMult s0 (IRUnaryOp OpAbs det1))
toIRNormalParams meta (InjF _ (Named "mult") [e0, e1])
  | pType (getTypeInfo e1) == PNormal = do
      (mu1, s1) <- toIRNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpMult mu1 det0, IROp OpMult s1 (IRUnaryOp OpAbs det0))
toIRNormalParams meta (InjF _ (Named "neg") [e])
  | pType (getTypeInfo e) == PNormal = do
      (mu, s) <- toIRNormalParams meta e
      return (IRUnaryOp OpNeg mu, s)
toIRNormalParams meta (InjF _ (Named "log") [e])
  | pType (getTypeInfo e) == PLogNormal = toIRLogNormalParams meta e
-- Tuple-field projection: the marginal of a literal tuple's field is that
-- field's own law, so extraction descends into the projected component. The
-- modality engine's IProd projection types e.g. @fst (Normal, Uniform * 2)@ as
-- PNormal, a shape PInfer2 never produced.
toIRNormalParams meta (InjF _ (Named "fst") [InjF _ (Named "TCons") [a, _]])
  | pType (getTypeInfo a) == PNormal = toIRNormalParams meta a
toIRNormalParams meta (InjF _ (Named "snd") [InjF _ (Named "TCons") [_, b]])
  | pType (getTypeInfo b) == PNormal = toIRNormalParams meta b
toIRNormalParams meta (InjF ti f@(Named n) [Var _ name])
  | n `elem` ["fst", "snd"]
  , Just expr <- lookup name (functions (compilingProgram meta)) =
      toIRNormalParams meta (InjF ti f [expr])
toIRNormalParams meta (Var _ name)
  | Just expr <- lookup name (functions (compilingProgram meta)) = toIRNormalParams meta expr
toIRNormalParams meta (ReadNN _ name arg) = do
  sym <- toIRGenerate meta arg
  var <- mkVariable "nn_out"
  setVariables [(var, IRApply (IRVar name) sym)]
  return (IRIndex (IRVar var) (IRConst (VInt 0)), IRIndex (IRVar var) (IRConst (VInt 1)))
toIRNormalParams _ e = error $ "toIRNormalParams: cannot extract Normal params from " ++ show (pType (getTypeInfo e)) ++ " | expr: " ++ show e

-- | Standard-normal CDF at 0 of the difference of two PNormal expressions.
-- left - right ~ Normal(muL - muR, sqrt(sL^2 + sR^2)); returns Phi((0 - mu) / sigma),
-- which is p(left < right). Used to give P-mode a closed form for Gaussian-vs-Gaussian
-- comparisons, where neither side is a deterministic bound.
normalDiffCdfAtZero :: CompilerMetadata -> Expr -> Expr -> CompilerMonad IRExpr
normalDiffCdfAtZero meta left right = do
  (muL, sL) <- toIRNormalParams meta left
  (muR, sR) <- toIRNormalParams meta right
  let mu = IROp OpSub muL muR
      sigma = irSqrt (IROp OpPlus (IROp OpMult sL sL) (IROp OpMult sR sR))
  return (IRCumulative IRNormal (IROp OpDiv (IROp OpSub (IRConst (VFloat 0)) mu) sigma))

-- | Recursively extract (mu_log, sigma) as IRExprs from a PLogNormal-typed expression.
toIRLogNormalParams :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
toIRLogNormalParams meta (InjF _ (Named "exp") [e])
  | pType (getTypeInfo e) == PNormal = toIRNormalParams meta e
toIRLogNormalParams meta (InjF _ (Named "mult") [e0, e1])
  | pType (getTypeInfo e0) == PLogNormal, pType (getTypeInfo e1) == PLogNormal = do
      (mu0, s0) <- toIRLogNormalParams meta e0
      (mu1, s1) <- toIRLogNormalParams meta e1
      return (IROp OpPlus mu0 mu1, irSqrt (IROp OpPlus (IROp OpMult s0 s0) (IROp OpMult s1 s1)))
toIRLogNormalParams meta (InjF _ (Named "mult") [e0, e1])
  | pType (getTypeInfo e0) == PLogNormal = do
      (mu0, s0) <- toIRLogNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpPlus mu0 (IRUnaryOp OpLog det1), s0)
toIRLogNormalParams meta (InjF _ (Named "mult") [e0, e1])
  | pType (getTypeInfo e1) == PLogNormal = do
      (mu1, s1) <- toIRLogNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpPlus mu1 (IRUnaryOp OpLog det0), s1)
-- sqrt(exp x) = exp(x/2): the log-space variable is halved, so (mu_log, sigma) -> (mu_log/2, sigma/2).
toIRLogNormalParams meta (InjF _ (Named "sqrt") [e])
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IROp OpMult (IRConst (VFloat 0.5)) mu, IROp OpMult (IRConst (VFloat 0.5)) s)
-- sq(exp x) = (exp x)^2 = exp(2x): the log-space variable is doubled, so (mu_log, sigma) -> (2 mu_log, 2 sigma).
toIRLogNormalParams meta (InjF _ (Named "sq") [e])
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IROp OpMult (IRConst (VFloat 2)) mu, IROp OpMult (IRConst (VFloat 2)) s)
-- recip(exp x) = 1/exp x = exp(-x): the log-space variable is negated, so (mu_log, sigma) -> (-mu_log, sigma).
toIRLogNormalParams meta (InjF _ (Named "recip") [e])
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IRUnaryOp OpNeg mu, s)
-- Tuple-field projection, mirroring toIRNormalParams.
toIRLogNormalParams meta (InjF _ (Named "fst") [InjF _ (Named "TCons") [a, _]])
  | pType (getTypeInfo a) == PLogNormal = toIRLogNormalParams meta a
toIRLogNormalParams meta (InjF _ (Named "snd") [InjF _ (Named "TCons") [_, b]])
  | pType (getTypeInfo b) == PLogNormal = toIRLogNormalParams meta b
toIRLogNormalParams meta (InjF ti f@(Named n) [Var _ name])
  | n `elem` ["fst", "snd"]
  , Just expr <- lookup name (functions (compilingProgram meta)) =
      toIRLogNormalParams meta (InjF ti f [expr])
toIRLogNormalParams meta (Var _ name)
  | Just expr <- lookup name (functions (compilingProgram meta)) = toIRLogNormalParams meta expr
toIRLogNormalParams _ e = error $ "toIRLogNormalParams: cannot extract LogNormal params from " ++ show (pType (getTypeInfo e))

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
-- | Expressions that have their own toIRInference handlers and must not be
-- intercepted by the PNormal/PLogNormal catch-alls below.
hasOwnInferenceHandler :: [ADTDecl] -> Expr -> Bool
hasOwnInferenceHandler _    (Apply _ _ _)            = True
-- Field constructors (Cons/TCons/user-ADT constructors) carry the PType of their
-- fields, which can be PNormal even though the container itself cannot be
-- inferred by toIRNormal. They have their own construction handler, so the
-- PNormal/PLogNormal catch-alls must not intercept them.
hasOwnInferenceHandler adts (InjF _ (Named name) _) = isFieldConstructor adts name
hasOwnInferenceHandler _    _                        = False

toIRInference :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad CompilationResult
--toIRInference meta cumulative expr sample | trace (show expr) False = undefined
-- CDFs on Booleans make little sense. We define that False < True. Therefor cdf(True) = 1 and cdf(False) = pdf(False)
toIRInference meta True expr sample | rType (getTypeInfo expr) == TBool = do
  (pFalse, _, bcFalse) <- toIRInference meta False expr (IRConst (VBool False))
  return (IRIf sample (IRConst (VFloat 1)) pFalse, const0, bcFalse)
toIRInference meta False e sample | pType (getTypeInfo e) == PNormal, not (hasOwnInferenceHandler (adtDecls meta) e) = do
  (mu, sigma) <- toIRNormalParams meta e
  let p = IROp OpDiv (IRDensity IRNormal (IROp OpDiv (IROp OpSub sample mu) sigma)) sigma
  return (p, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), IRConst (VFloat 1))
toIRInference meta True e sample | pType (getTypeInfo e) == PNormal, not (hasOwnInferenceHandler (adtDecls meta) e) = do
  (mu, sigma) <- toIRNormalParams meta e
  return (IRCumulative IRNormal (IROp OpDiv (IROp OpSub sample mu) sigma), const0, IRConst (VFloat 1))
toIRInference meta False e sample | pType (getTypeInfo e) == PLogNormal, not (hasOwnInferenceHandler (adtDecls meta) e) = do
  (mu, sigma) <- toIRLogNormalParams meta e
  let correctedSample = IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma
  let p = IROp OpDiv (IRDensity IRNormal correctedSample) (IROp OpMult sigma sample)
  let dim = IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1)
  let negativeGuard x = IRIf (IROp OpGreaterThan sample const0) x const0
  return (negativeGuard p, dim, IRConst (VFloat 1))
toIRInference meta True e sample | pType (getTypeInfo e) == PLogNormal, not (hasOwnInferenceHandler (adtDecls meta) e) = do
  (mu, sigma) <- toIRLogNormalParams meta e
  let correctedSample = IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma
  let negativeGuard x = IRIf (IROp OpGreaterThan sample const0) x const0
  return (negativeGuard (IRCumulative IRNormal correctedSample), const0, IRConst (VFloat 1))
-- Distribution primitives (reserved-name Vars). Normal usually reaches the PNormal
-- catch-all above; these equations are the direct density/CDF leaves for Uniform and
-- the defensive Normal fallback.
toIRInference _ False (Var _ "Normal") sample = return (IRDensity IRNormal sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), IRConst (VFloat 1))
toIRInference _ False (Var _ "Uniform") sample = return (IRDensity IRUniform sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), IRConst (VFloat 1))
toIRInference _ True (Var _ "Normal") sample = return (IRCumulative IRNormal sample, const0, IRConst (VFloat 1))
toIRInference _ True (Var _ "Uniform") sample = return (IRCumulative IRUniform sample, const0, IRConst (VFloat 1))
toIRInference _ _ (Constant _ (VError e)) _ = return (IRError e, const0, const0)
toIRInference _ False (Constant TypeInfo {rType=rt} value) sample = do
  let comp = case rt of
              TFloat   -> IROp OpApprox sample (IRConst (fmap failConversion value))
              TVarR _  -> IROp OpApprox sample (IRConst (fmap failConversion value))
              _        -> IROp OpEq sample (IRConst (fmap failConversion value))
  expr <- indicator comp
  return (expr, const0, IRConst (VFloat 1))
toIRInference _ True (Constant TypeInfo {rType=rt} value) sample = return (compareValueExpr rt (IRConst (valueToIR value)) sample, const0, IRConst (VFloat 1))
toIRInference meta True (ThetaI _ a i) sample = do
  a' <- toIRGenerate meta a
  return (IRIf (IROp OpLessThan sample (IRTheta a' i)) (IRConst $ VFloat 0) (IRConst $ VFloat 1), const0, IRConst (VFloat 1))
toIRInference meta False (ThetaI _ a i) sample = do
  a' <- toIRGenerate meta a
  expr <- indicator (IROp OpApprox sample (IRTheta a' i))
  return (expr, const0, IRConst (VFloat 1))
toIRInference meta cumulative (IfThenElse _ cond left right) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  (condTrueExpr, condTrueDim, condTrueBranches) <- toIRInference meta False  cond (IRConst (VBool True))
  (condFalseExpr, condFalseDim, _) <- toIRInference meta False cond (IRConst (VBool False))
  setVariables [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]
  -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
  let thr = topKThreshold (compilerConfig meta)

  -- We need to restart the monad stack, because variables inside the branches may not be valid outside
  -- E.g. if length(a) > 0 then a[0] else ...
  -- If we were to access a[0] outside of the branch we would error
  ((mul1Raw, leftBranches), binds1) <- lift (runWriterT (do
    let metaTrue = meta { accProb = IROp OpMult (accProb meta) (IRVar var_condT_p) }
    (leftExpr, leftDim, branches) <- toIRInference metaTrue cumulative left sample
    (IRVar var_condT_p, condTrueDim) `multP` (leftExpr, leftDim) <&> (\x -> (x, branches)))) -- We need the branches outside of this scope. Append it to the tuple
  let mul1 = bimap (generateLetInExpr binds1) (generateLetInExpr binds1) mul1Raw
  let leftBranchesExpr = generateLetInExpr binds1 leftBranches
  ((mul2Raw, rightBranches), binds2) <- lift (runWriterT (do
    let metaFalse = meta { accProb = IROp OpMult (accProb meta) (IRVar var_condF_p) }
    (rightExpr, rightDim, branches) <- toIRInference metaFalse cumulative right sample
    (IRVar var_condF_p, condFalseDim) `multP` (rightExpr, rightDim) <&> (\x -> (x, branches)))) -- We need the branches outside of this scope. Append it to the tuple
  let mul2 = bimap (generateLetInExpr binds2) (generateLetInExpr binds2) mul2Raw
  let rightBranchesExpr = generateLetInExpr binds2 rightBranches
  -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
  let zeroCheck c = IRIf (IROp OpApprox c const0) const0
  let mul1Zeroed = bimap (zeroCheck condTrueExpr) (zeroCheck condTrueExpr) mul1
  let mul2Zeroed = bimap (zeroCheck condFalseExpr) (zeroCheck condFalseExpr) mul2
  (addExpr, addDim) <- mul1Zeroed `addP` mul2Zeroed
  let branches = IROp OpSub (IROp OpPlus condTrueBranches (IROp OpPlus leftBranchesExpr rightBranchesExpr)) (IRConst (VFloat 1))
  case thr of
    Just _ -> do
      let accTrue = IROp OpMult (accProb meta) (IRVar var_condT_p)
      let accFalse = IROp OpMult (accProb meta) (IRVar var_condF_p)
      let returnExpr = IRIf
            (IROp OpLessThan accTrue (IRVar "TOP_K_CUTOFF"))
            -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
            (IRIf (IROp OpApprox condFalseExpr const0) const0 (fst mul2))
            (IRIf (IROp OpLessThan accFalse (IRVar "TOP_K_CUTOFF"))
              (IRIf (IROp OpApprox condTrueExpr const0) const0 (fst mul1))
              addExpr)
      let returnDim = IRIf
            (IROp OpLessThan accTrue (IRVar "TOP_K_CUTOFF"))
            (IRIf (IROp OpApprox condFalseExpr const0) const0 (snd mul2))
            (IRIf (IROp OpLessThan accFalse (IRVar "TOP_K_CUTOFF"))
              (IRIf (IROp OpApprox condTrueExpr const0) const0 (snd mul1))
              addDim)
      let returnBranches = IRIf
            (IROp OpLessThan accTrue (IRVar "TOP_K_CUTOFF"))
            rightBranchesExpr
            (IRIf (IROp OpLessThan accFalse (IRVar "TOP_K_CUTOFF"))
              leftBranchesExpr
              branches)
      return (returnExpr, returnDim, returnBranches)
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      return (addExpr, addDim, branches)
-- Both sides Gaussian: left - right ~ Normal(muL - muR, sqrt(sL^2 + sR^2)), so the
-- comparison is that difference's CDF evaluated at 0. Neither side is Deterministic,
-- so the bound-based equations below do not apply. resolveCompCons types this Bool
-- as Integrate (a closed-form discrete probability), matching the dim-0 result here.
toIRInference meta False (GreaterThan _ left right) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    cdfAt0 <- normalDiffCdfAtZero meta left right
    -- p(left > right) = p(diff > 0) = 1 - cdf(0)
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) cdfAt0) cdfAt0
    return (returnExpr, const0, IRConst (VFloat 1))
toIRInference meta False (LessThan _ left right) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    cdfAt0 <- normalDiffCdfAtZero meta left right
    -- p(left < right) = p(diff < 0) = cdf(0)
    let returnExpr = IRIf sample cdfAt0 (IROp OpSub (IRConst $ VFloat 1.0) cdfAt0)
    return (returnExpr, const0, IRConst (VFloat 1))
toIRInference meta False (GreaterThan _ left right) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    (integrate, _, integrateBranches) <- toIRInference meta True right (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    (integrate, _, integrateBranches) <- toIRInference meta True left (IRVar var)
    var2 <- mkVariable "lhs_integral"
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2)
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRInference meta False (LessThan _ left right) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    (integrate, _, integrateBranches) <- toIRInference meta True right (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2)
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    (integrate, _, integrateBranches) <- toIRInference meta True left (IRVar var)
    var2 <- mkVariable "lhs_integral"
    setVariables [(var2, integrate)]
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))
    return (returnExpr, const0, integrateBranches)
toIRInference meta _ (ReadNN _ name symbol) sample = do
  nnRaw <- mkVariable "nn_raw"
  var <- mkVariable "callNN"
  sym <- toIRGenerate meta symbol
  setVariables [(nnRaw, IRApply (IRVar name) sym)]
  setVariables [(var, IRApply (IRApply (IRVar (name ++ "_auto_prob")) (IRVar nnRaw)) sample)]
  return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
toIRInference meta cumulative (Lambda t name subExpr) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- lift (runWriterT (toIRInference newMeta cumulative subExpr sample)) <&> generateLetInBlock meta
  return (IRLambda name irTuple, const0, const0)
-- Deterministic lambda and bound expression PDF
toIRInference meta False (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retExpr <- indicator (IROp OpEq (IRApply lIR vIR) sample)
      return (retExpr, const0, const0)
-- Deterministic lambda and bound expression CDF
toIRInference meta True (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      return (compareValueExpr rt (IRApply lIR vIR) sample, const0, const0)
-- Enumerable conditional lambda applied to a probabilistic discrete argument:
-- enumerate the argument's discrete support and weight each value by its probability,
-- compiling the body via toIREnumerate. The body need not be deterministic given the
-- bound variable -- toIREnumerate recurses into further enumerable applications
-- (nested enumerable `let`s), so this rule no longer requires `pType l == Deterministic`.
toIRInference meta cumulative (Apply TypeInfo {rType=_} l v) sample
  | isEnumerableApplication l v =
  enumerateAppliedLambda meta cumulative l v sample
-- Deterministic bound expression
toIRInference meta cumulative (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  (lIR, _, _) <- toIRInference meta cumulative l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retVal <- mkVariable "call"
      setVariables [(retVal, IRApply lIR vIR)]
      return (IRTFst (IRVar retVal), IRTFst (IRTSnd (IRVar retVal)), IRTSnd (IRTSnd (IRVar retVal)))
-- Probabilistic bound expression
toIRInference meta cumulative (Apply TypeInfo{rType=_, chainName=_} l v) sample | isTArrow (rType (getTypeInfo v)) && (pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal) = do
  lIR <- toIRGenerate meta l
  (vIR, _, _) <- toIRInference meta cumulative v sample
  applied <- mkVariable "call"
  setVariables [(applied, IRApply lIR vIR)]
  return (IRTFst (IRVar applied), IRTFst (IRTSnd (IRVar applied)), IRTSnd (IRTSnd (IRVar applied)))
  where
    isTArrow (TArrow _ _) = True
    isTArrow _ = False
toIRInference meta cumulative (Apply TypeInfo{rType=rt, chainName=_} l v) sample | pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal = do
  -- This is the probabilistic inference of a known, deterministic lambda with a probabilistic parameter
  -- The inference looks like this: p(l(v) == sample) = p(l^-1(sample) == v)
  -- The inverse can not be created using recursive descend, therefor we use forward chaining for the inverse only
  -- Chain name of the callable
  let clauses = fcData meta
  let adts = adtDecls meta
  let lChainName = chainName (getTypeInfo l)

  -- This logic is here to wrap the expression back into lambdas if the lambda we look at returns a lambda
  let Just (lResolvedCN, LambdaInfo toInvCN lambdaBodyCN, tag) = findEquivalentExpression (fcData meta) lChainName
  let (boundVar, lambdaVars) = unwrapLambdas (fcData meta) lambdaBodyCN
  let wrapInLambdas ex = foldr IRLambda ex lambdaVars

  -- Dead binding: if the bound variable never appears in the body, the body is independent
  -- of the argument. In that case p(result = sample) = p(body = sample).
  -- Scoped to THIS lambda's body: a same-named variable bound elsewhere must not count.
  let deadBinding = null (fromMaybe [] (lookup lResolvedCN (lambdaVarOccurrences (fcData meta))))
  if deadBinding then do
    let Program{functions=fs} = compilingProgram meta
    let bodyExpr = findExprWithCN (map snd fs) lambdaBodyCN
    toIRInference meta cumulative bodyExpr sample
  else do
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
   planRes <- planWitnessApply meta cumulative rt lResolvedCN lambdaBodyCN tag v sample
   case planRes of
    Right result -> return result
    Left planDiag -> case toInvExprMaybe clauses adts lChainName of
     -- No occurrence of the bound variable is point-invertible from the
     -- observation either. Fall back to set-valued witnesses: invert the
     -- observation structurally into guarded constraint sets on the bound
     -- variable (intervals from comparisons, case splits from ifs,
     -- intersections across occurrences) and measure them against the bound
     -- distribution (design set-valued-witnesses).
     Nothing -> setWitnessApply meta cumulative rt l lResolvedCN lambdaBodyCN tag planDiag v sample
     Just (invExprP0, invExprCoV0, invExprGuard0) -> do
      invExprP     <- pruneDeadLetIns <$> materializeAnchors meta invExprP0
      invExprCoV   <- pruneDeadLetIns <$> materializeAnchors meta invExprCoV0
      invExprGuard <- pruneDeadLetIns <$> materializeAnchors meta invExprGuard0
      let appliedCoV = IRApply (IRLambda (boundVar ++ tag) invExprCoV) sample
      let lInv = IRLambda (boundVar ++ tag) invExprP
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
      let guard = IRApply (IRLambda (boundVar ++ tag) invExprGuard) sample
      -- Do probabilistic inference using the applied inverse
      (p, dim, bc) <- toIRInference meta cumulative v appliedSample

      let scale x = if not cumulative
                      then IROp OpMult x (IRIf (IROp OpEq dim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs appliedCoV))
                      else IRIf (IROp OpGreaterThan appliedCoV const0) x (IROp OpSub (IRConst (VFloat 1)) x)
      let guarded e zero = IRIf guard e zero
      case rt of
        TArrow _ _ -> return (guarded (wrapInLambdas (IRTCons (scale p) (IRTCons dim bc))) (wrapInLambdas (IRTCons const0 (IRTCons const0 const0))), const0, const0)
        _ | cumulative || not (isLambdaExpr l) || not (null tag) ->
              -- Keep the original single-witness behaviour when: (a) integrate mode, where
              -- tuple/multi-latent CDFs are ill-defined; (b) the callable is not a literal
              -- lambda, i.e. it is a function reached through the higher-order equivalence
              -- machinery (applied top-level fn / returned closure), whose body references
              -- tagged variables this folding would mis-bind; or (c) the lambda is applied
              -- under a tag (HO duplication). Body-factor folding is only sound for a plain
              -- value let-binding `Apply (Lambda x body) v`.
              return (wrapInLambdas $ guarded (scale p) const0, wrapInLambdas $ guarded dim const0, wrapInLambdas $ guarded bc const0)
        _ -> do
          -- The inversion above only recovers and infers the variable bound by THIS
          -- lambda. Any additional independent latents bound deeper in the body (e.g. a
          -- second `let` whose value is repacked alongside this one in a tuple) are not
          -- captured by the bound-value inference. Infer the body too and fold it in as an
          -- independent factor: probabilities multiply, dimensions add, branch counts add.
          -- For a body that is deterministic given the recovered variable, the exact
          -- inverse makes the body factor an always-true (dim-0) indicator, so the product
          -- collapses to the original result; only genuinely new latents add density/dim.
          let Program{functions=fs} = compilingProgram meta
          -- The recovered variable (and any recovered by enclosing folds) is
          -- Deterministic for the body's dispatch; re-typing happens after the
          -- fetch because the fetch always returns original annotations.
          let recovered = toInvCN : recoveredVars meta
          let bodyExpr = retypeDetGiven recovered (findExprWithCN (map snd fs) lambdaBodyCN)
          -- The body references the bound variable, so it must be in scope in the type
          -- environment (mirrors how the Lambda arm descends into a lambda body).
          let bodyMeta = (extendMetaForLambda meta (getTypeInfo l) toInvCN) { recoveredVars = recovered }
          -- Compile the body factor in its own let-in block: any bindings the recursion
          -- floats (e.g. the shared `l_*_call` triple of an inner Apply) must stay under
          -- the recovered-variable binding below -- evaluation is strict, so a floated
          -- binding that mentions the bound variable would otherwise be evaluated before
          -- the recovered value is in scope.
          bodyBlock <- lift (runWriterT (toIRInference bodyMeta cumulative bodyExpr sample)) <&> generateLetInBlock bodyMeta
          -- Bind the recovered value of the bound variable in scope so free occurrences in
          -- the body factor resolve (and redundant comparisons collapse to true). Kept
          -- inline (not hoisted through setVariables): stripBranchCount's genVar heuristic
          -- would shift projections from a hoisted binding as if it were a called-function
          -- pair, while the local triple value stays unshifted. CSE recovers the sharing.
          let bodyTriple = IRLetIn (toInvCN ++ tag) appliedSample bodyBlock
          let pBody   = IRTFst bodyTriple
              dimBody = IRTFst (IRTSnd bodyTriple)
              bcBody  = IRTSnd (IRTSnd bodyTriple)
          (combP, combDim) <- multP (scale p, dim) (pBody, dimBody)
          let combBC = IROp OpPlus bc bcBody
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
          let occurrences = fromMaybe [] (lookup lResolvedCN (lambdaVarOccurrences (fcData meta)))
          let bindingIsSink = length occurrences == 1 && not (containsRandomSource bodyExpr)
          let userVar = case l of Lambda _ n _ -> n; _ -> boundVar
          let refuse = IRError ("cannot compute marginal: binding '" ++ userVar
                ++ "' is unobserved (ANY in its witnessing slot), but its value feeds"
                ++ " observed slots or further randomness; integrating it out is beyond"
                ++ " this engine (design modality-witnessed-inference)")
          let anyW = IRUnaryOp OpIsAny appliedSample
          let guardAny ok whenAnySink = IRIf anyW (if bindingIsSink then whenAnySink else refuse) ok
          return ( wrapInLambdas (guarded (guardAny combP pBody) const0)
                 , wrapInLambdas (guarded (guardAny combDim dimBody) const0)
                 , wrapInLambdas (guarded (guardAny combBC bcBody) const0) )
    -- Forward chaining may have messed with the structure of the expression. We may have too many or too few lambdas.
    -- Every lambda, which is not applied, inside of the callable should be present in the retuned IRExpr.
    -- Exclude the lambda, which is applied here and all lambdas, which are already present
    {-let Just lBound = findBoundVariable clauses lChainName
    let freeVars = (getUnappliedLambdas clauses lChainName \\ [lBound]) \\ findLambdaVars p
    let wrapInLambdas ex = foldr IRLambda ex freeVars
    -- If the parameter is a lambda, the return value here is a lambda.
    -- We find the bound variable in the program and apply its value here
    let (retP, retD, retBC) = case rType (getTypeInfo v) of
          TArrow _ _ -> do
            let ret = IRInvoke (applyLambdas clauses adts p)
            if countBranches (compilerConfig meta) then
              (IRTFst ret, IRTFst (IRTSnd ret), IRTFst (IRTSnd ret))
            else
              (IRTFst ret, IRTSnd ret, const0)
          _ -> (p, d, bc)
    -- If the result is a function, we must wrap the return into a tuple
    case rt of
      TArrow _ _ -> return (wrapInLambdas (if countBranches (compilerConfig meta) then IRTCons retP (IRTCons retD retBC) else IRTCons retP retD), const0, const0)
      _ -> return (wrapInLambdas retP, wrapInLambdas retD, wrapInLambdas retBC)-}

toIRInference _ _ (Apply TypeInfo{rType=_} _ _) _ = error "This instance of apply is not yet implemented"
-- Generic inference for multi-field constructor InjFs (Cons, TCons, user-ADT
-- constructors). Each field is independently recoverable from the constructed
-- sample via a deconstructing inverse, so we infer each field against its
-- recovered sub-sample and combine: probabilities multiply, dimensions add,
-- branch counts add. The components are independent, hence product (not the
-- additive PlusConstraint) semantics. Fires for >= 1 probabilistic parameter;
-- the all-deterministic case is handled by the generate-and-compare branch below.
toIRInference meta cumulative (InjF TypeInfo{rType=rt} (Named name) params) sample
  | isFieldConstructor (adtDecls meta) name && countProbParams params >= 1 = do
  let resolvedName = resolveInjF rt name
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let FDecl {inputVars=inVars, outputVars=[outV]} = fwd
  -- Inline the sample directly into each inverse body (instead of binding it to
  -- outV) so the optimizer can fold deconstructions like head(prepend(s, ANY))
  -- back to s. A let-binding referenced by every field plus the guard would
  -- survive optimization and force materialising the reconstructed container.
  let inlineSample = irMap (\e -> case e of IRVar n | n == outV -> sample; _ -> e)
  fieldResults <- forM (zip inVars params) $ \(inV, p) -> do
    let [inv] = filter (\FDecl {outputVars=[w]} -> w == inV) inversions
    let FDecl {body=invBody, applicability=appT, deconstructing=decons} = inv
    -- Deconstructing inverses need the Any-safe inference variant.
    let probF = if decons then toIRInferenceSave else toIRInference
    (fp, fd, fbc) <- probF meta cumulative p (inlineSample invBody)
    return (fp, fd, fbc, inlineSample appT)
  let ((p0, d0, bc0, _) : rest) = fieldResults
  (combP, combDim) <- foldM (\acc (fp, fd, _, _) -> acc `multP` (fp, fd)) (p0, d0) rest
  let combBC = foldl (\acc (_, _, fbc, _) -> IROp OpPlus acc fbc) bc0 rest
  -- Guard the result by the conjunction of all field applicability tests (e.g.
  -- the non-empty-list test carried by the Cons inverses).
  let guardCond = foldr1 (IROp OpAnd) (map (\(_, _, _, a) -> a) fieldResults)
  let guarded e = IRIf guardCond e const0
  return (guarded combP, guarded combDim, guarded combBC)
toIRInference meta cumulative (InjF ti (Named name) params) sample | isHigherOrder (adtDecls meta) name = do
  let adts = adtDecls meta
  let resolvedName = resolveInjF (rType ti) name
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable adts resolvedName
  -- Unary InjF has a single inversion
  let FPair _ [inv] = fPair
  let FDecl {inputVars=inVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=derivs} = inv
  --Handle the function being in different positions of the signature
  let aPoss = [0 .. (length params - 1)] \\ getFunctionParamIdx adts name
  let aPos = case aPoss of
        [n] -> n
        x -> error $ "Expected exectly one non-ho parameter, but got " ++ show (length x)
  let a = params !! aPos
  let aVar = inVars !! aPos
  let fs = map (params !!) (getFunctionParamIdx adts name)
  let fVars = map (inVars !!) (getFunctionParamIdx adts name)
  let Just invDerivExpr = lookup aVar derivs
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
  (paramExpr, paramDim, paramBranches) <- probF meta cumulative a finalInvExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let scale x = if not cumulative
                  then IROp OpMult x (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDerivExpr))
                  else IRIf (IROp OpGreaterThan invDerivExpr (const0)) x (IROp OpSub (IRConst (VFloat 1)) x)
  let returnP = scale paramExpr
  let appTestExpr e = IRIf appTest e const0
  return (renVar (appTestExpr returnP), renVar (appTestExpr paramDim), renVar (appTestExpr paramBranches))
toIRInference meta False e@(InjF TypeInfo {tags=_, rType=rt} (Named _) params) sample
  | countProbParams params == 0 = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate meta e
  let cmp = case rt of
        TFloat   -> OpApprox
        TVarR _  -> OpApprox
        _        -> OpEq
  retExpr <- indicator $ IROp cmp expr sample
  return (retExpr, const0, const0)
toIRInference meta True e@(InjF TypeInfo {tags=_, rType=rt} (Named _) params) sample
  | countProbParams params == 0 = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is less than the sample
  expr <- toIRGenerate meta e
  return (compareValueExpr rt expr sample, const0, const0)
toIRInference meta cumulative (InjF TypeInfo {tags=_} (Named name) params) sample
  | hasAnyExcept (adtDecls meta) name = do
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) name
  let FDecl{inputVars=inVars, outputVars=[v1]} = fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let Just probIdx = getProbIndex params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let [invDecl] = filter (\FDecl {outputVars=[w1]} -> (inVars !! probIdx)==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  let IRIf (IRVar v1') invPosExpr invNegExpr = invExpr
  when (v1 /= v1') $ error $ "Form of InjF is not supported, sample has to be the condition: " ++ name
  let (isPosAny, nonAnyExpr, exceptExpr) =
        case (invPosExpr, invNegExpr) of
          (IRConst (VAnyExcept [expt]), non) -> (True, non, expt)
          (non, IRConst (VAnyExcept [expt])) -> (False, non, expt)
          _ -> error "AnyExcept in InjF must be the first expression inside the if"

  -- Find the relevant derivative of the inversion
  let Just invDeriv = lookup v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic subexpression
  (nonAnyIRExpr, nonAnyDim, nonAnyBranches) <- probF meta cumulative (params !! probIdx) nonAnyExpr
  (anyIRExpr, anyDim, _) <- toIRInferenceSave meta cumulative (params !! probIdx) (IRConst $ VAny)
  (exceptIRExpr, exceptDim, exceptBranches) <- probF meta cumulative (params !! probIdx) exceptExpr
  let ifSample a na = if isPosAny then IRIf (IRVar v1) a na else IRIf (IRVar v1) na a
  (subExpr, subDim) <- subP (anyIRExpr, anyDim) (exceptIRExpr, exceptDim)
  let ifExpr = ifSample subExpr nonAnyIRExpr
  let ifDim = ifSample subDim nonAnyDim
  let ifBranches = ifSample exceptBranches nonAnyBranches

  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  let scale x = if not cumulative
                  then IROp OpMult x (IRIf (IROp OpEq ifDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDeriv))
                  else IRIf (IROp OpGreaterThan invDeriv const0) x (IROp OpSub (IRConst (VFloat 1)) x)
  let returnP = scale ifExpr
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr ifDim, appTestExpr ifBranches)
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
toIRInference meta False (InjF TypeInfo {rType=rt} (Named name) [left, right]) sample
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
  let FDecl {inputVars=[v1, v2], body=f} = fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  (returnExpr, binds) <- lift $ runWriterT $ do
    (pRand, _, _) <- toIRInference meta False randExprSrc (IRVar randVar)
    return (IRIf (IROp OpEq f sample) pRand (IRConst (VFloat 0)))
  let (outerBinds, body') = hoistInvariantBindings randVar (buildLetIns binds returnExpr)
  setVariables outerBinds
  return (IREnumSum randVar enumList body', const0, const0)
-- Cumulative (cdf) counterpart of the single-operand enumeration case above.
toIRInference meta True (InjF TypeInfo {rType=rt} (Named name) [left, right]) sample
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
  let FDecl {inputVars=[v1, v2], body=f} = fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  (returnExpr, binds) <- lift $ runWriterT $ do
    (pRand, _, _) <- toIRInference meta False randExprSrc (IRVar randVar)
    return (IRIf (IROp OpLessThan sample f) (IRConst (VFloat 0)) pRand)
  let (outerBinds, body') = hoistInvariantBindings randVar (buildLetIns binds returnExpr)
  setVariables outerBinds
  return (IREnumSum randVar enumList body', const0, const0)
toIRInference meta cumulative (InjF TypeInfo {tags=_, rType=rt} (Named name) params) sample
  | countProbParams params == 1 = do
  let resolvedName = resolveInjF rt name
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let FDecl{inputVars=inVars, outputVars=[v1]} = fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let Just probIdx = getProbIndex params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let [invDecl] = filter (\FDecl {outputVars=[w1]} -> (inVars !! probIdx)==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  -- Find the relevant derivative of the inversion
  let Just invDeriv = lookup v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic subexpression
  (paramExpr, paramDim, paramBranches) <- probF meta cumulative (params !! probIdx) invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  let scale x = if not cumulative
                  then IROp OpMult x (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDeriv))
                  else IRIf (IROp OpGreaterThan invDeriv (const0)) x (IROp OpSub (IRConst (VFloat 1)) x)
  let returnP = scale paramExpr
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr paramDim, appTestExpr paramBranches)
-- Enumerate-both discrete path for forward-only binary InjFs (and/or). No point
-- inverse exists, so loop the |L|x|R| grid and keep cells where forward(l,r) == sample,
-- accumulating pLeft(l) * pRight(r). Mirrors the cumulative double-enum path below.
toIRInference meta False (InjF TypeInfo {rType=rt} (Named name) [left, right]) sample
  | isForwardOnly (adtDecls meta) (resolveInjF rt name)
    && isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  let enumListL = head [x | DiscreteValues x <- tags (getTypeInfo left)]
  let enumListR = head [x | DiscreteValues x <- tags (getTypeInfo right)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let FDecl {inputVars=[v1, v2], body=f} = fwd
  (returnExpr, binds) <- lift $ runWriterT $ do
    (pLeft, _, _) <- toIRInference meta False left (IRVar v1)
    (pRight, _, _) <- toIRInference meta False right (IRVar v2)
    return (IRIf (IROp OpEq f sample) (IROp OpMult pLeft pRight) (IRConst (VFloat 0)))
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (buildLetIns binds returnExpr)
  let innerSum = buildLetIns v2InvBinds (IREnumSum v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  return (IREnumSum v1 enumListL v1Body, const0, const0)
toIRInference meta False (InjF TypeInfo {rType=rt} (Named name) [left, right]) sample
  | isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head [x | DiscreteValues x <- extrasLeft]
  let enumListR = head [x | DiscreteValues x <- extrasRight]

  fPair <- instantiate mkVariable (adtDecls meta) resolvedName -- FPair of the InjF with unique names
  let FPair fwd inversions = fPair
  let FDecl {inputVars=[_, v3], outputVars=[_]} = fwd
  -- We get the inversion to the right side
  let [invDecl] = filter (\(FDecl {outputVars=[w1]}) -> v3==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=[x2, x3], body=invExpr} = invDecl

  -- We now compute
  -- for each e in leftEnum:
  --   sum += if invExpr(e, sample) in rightEnum then pLeft(e) * pRight(sample - e) else 0
  -- For that we name e like the lhs of
  -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
  irTuple <- lift (runWriterT (do
    -- the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    setVariables [(x3, sample)]
    (pLeft, _, _) <- toIRInference meta False left (IRVar x2)
    -- pRight is computed in a nested writer so its bindings can be guarded by the topK check,
    -- avoiding the inner right-side inference work whenever acc_prob * pLeft is already below cutoff.
    ((pRight, _, _), pRightBinds) <- lift $ runWriterT $ toIRInference meta False right invExpr
    let wrapR e = generateLetInExpr pRightBinds e
    let possible = IRIsPossible enumListR invExpr
    let cutoffOk = case topKThreshold (compilerConfig meta) of
          Nothing -> possible
          Just _  -> IROp OpAnd possible
                       (IROp OpGreaterThan
                          (IROp OpMult (accProb meta) pLeft)
                          (IRVar "TOP_K_CUTOFF"))
    let returnExpr   = IRIf cutoffOk (wrapR (IROp OpMult pLeft pRight)) (IRConst (VFloat 0))
    let branchesExpr = IRIf cutoffOk (IRConst (VFloat 1)) (IRConst (VFloat 0))
    return (returnExpr, const0, branchesExpr)
    )) <&> generateLetInBlock meta
  uniquePrefix <- mkVariable ""
  let applyUnique = irMap (uniqueify [x2, x3] uniquePrefix)
  let (outerBinds, innerTuple) = hoistInvariantBindings x2 irTuple
  let renameHoisted (n, v) = (if n `elem` [x2, x3] then uniquePrefix ++ n else n, applyUnique v)
  setVariables (map renameHoisted outerBinds)
  let enumSumExpr = IREnumSum x2 enumListL (IRTFst innerTuple)
  let branchCountSum = IREnumSum x2 enumListL (IRTSnd (IRTSnd innerTuple))
  return (applyUnique enumSumExpr, const0, applyUnique branchCountSum)
-- For the cumulative case we cant get around two enum sums
toIRInference meta True (InjF TypeInfo {rType=rt} (Named name) [left, right]) sample
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
  let FDecl {inputVars=[v1, v2], body=f} = fwd
  -- Compute the loop body in a nested writer so its bindings can be captured rather
  -- than leaking to the enclosing function scope: those bindings reference the enum
  -- variables v1/v2 (the coin_prob calls) and must be scoped *inside* the matching
  -- enumSum, not above it.
  (returnExpr, binds) <- lift $ runWriterT $ do
    (pLeft, _, _) <- toIRInference meta False left (IRVar v1)
    (pRight, _, _) <- toIRInference meta False right (IRVar v2)
    return (IRIf (IROp OpLessThan sample f) (IRConst (VFloat 0)) (IROp OpMult pLeft pRight))
  -- Place each binding at the outermost scope where it remains well-formed: fully
  -- invariant bindings are hoisted to the function top level, bindings depending only
  -- on v1 sit between the two enumSums, and bindings depending on v2 stay innermost.
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (buildLetIns binds returnExpr)
  let innerSum = buildLetIns v2InvBinds (IREnumSum v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  return (IREnumSum v1 enumListL v1Body, const0, const0)
toIRInference meta cumulative (Var TypeInfo {rType=rt} n) sample = do
  -- Variable might be a function
  let functionSuffix = if cumulative then "_integ" else "_prob"
  case lookup n (typeEnv meta) of
    -- Var is a function
    Just(TArrow _ _, hasInference) -> do
      var <- mkVariable "call"
      let name = if hasInference then n ++ functionSuffix else n
      let callExpr = if hasInference
            then case topKThreshold (compilerConfig meta) of
              Just _ -> IRApply (IRApply (IRVar name) sample) (accProb meta)
              Nothing -> IRApply (IRVar name) sample
            else IRApply (IRVar name) sample
      setVariables [(var, callExpr)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (IRVar var, const0, const0)
    -- Var is a top level declaration (an therefor has a _prob function)
    Just (_, True) -> do
      var <- mkVariable "call"
      let callExpr = case topKThreshold (compilerConfig meta) of
            Just _ -> IRApply (IRApply (IRVar (n ++ functionSuffix)) sample) (accProb meta)
            Nothing -> IRApply (IRVar (n ++ functionSuffix)) sample
      setVariables [(var, callExpr)]
      return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
    -- Var is a local variable
    Just (_, False) -> do
      if cumulative then
        return (compareValueExpr rt (IRVar n) sample, const0, const0)
      else do
        let comp = case rt of
              TFloat   -> IROp OpApprox sample (IRVar n)
              TVarR _  -> IROp OpApprox sample (IRVar n)
              _        -> IROp OpEq sample (IRVar n)
        expr <- indicator comp
        return (expr, const0, const0)
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRInference _ _ (Subtree _ _ _) _ = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRInference _ _ x _ = error ("found no way to convert to IR: " ++ show x)

multP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
multP (aM, aDim) (bM, bDim) = return (IROp OpMult aM bM, IROp OpPlus aDim bDim)

addP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
addP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  setVariables [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  -- Exact equality here, not OpApprox: this branch exists to detect a genuine
  -- indicator-zero (e.g. the wrong Either arm), which is always produced exactly
  -- by upstream indicator/comparison logic. A 1e-10 approx threshold instead
  -- wrongly discards legitimately tiny-but-nonzero continuous tail densities
  -- (see observe-partials-umbrella N4). Not total: a deep enough tail still
  -- underflows to a true float zero and hits this same ambiguity.
  return (IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
           (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
           (IROp OpPlus (IRVar pVarA) (IRVar pVarB))))),
           -- Dim
           IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
           (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
           (IRVar dimVarA)))))

subP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
subP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  setVariables [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  return (IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
         (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
         (IROp OpSub (IRVar pVarA) (IRVar pVarB))))),
         -- Dim
         IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
         (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
         (IRVar dimVarA)))))

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
    bindAnchor body cn = do
      anchorIR <- toIRGenerate meta (findExprWithCN fns (untag cn))
      return (IRLetIn cn anchorIR body)

createHOInverse :: CompilerMetadata -> (String, Expr) -> CompilerMonad (IRExpr -> IRExpr)
createHOInverse meta (fVar, f) = do
  let fcData' = fcData meta
  let adts = adtDecls meta
  -- NB: the applicability guard (3rd component, see observe-partials-umbrella
  -- N1b) is not threaded through the higher-order inverse path yet -- a
  -- deconstructing InjF crossed while inverting a user-defined function passed
  -- through createHOInverse can still crash. Not hit by any current test case;
  -- tracked as follow-up alongside the other HO-inverse gaps.
  let (inverseF0, inverseCoV0, _inverseGuard0) = toInvExpr fcData' adts (chainName $ getTypeInfo f)
  inverseF   <- materializeAnchors meta inverseF0
  inverseCoV <- materializeAnchors meta inverseCoV0
  let Just (_, LambdaInfo _ lBodyChainName, tag) = findEquivalentExpression fcData' (chainName $ getTypeInfo f)
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

getProbIndex :: HasCallStack => [Expr] -> Maybe Int
--getProbIndex es | traceShow es False = undefined
getProbIndex es =
  case filter (\(p, _) -> p == Integrate || p == PNormal || p == PLogNormal) zipped of
    [(_, i)] -> Just i
    [] -> Nothing
    _ -> error "More than one probabilistic argument found"
  where
    pt x = pType (getTypeInfo x)
    pTypes = map pt es
    zipped = zip pTypes [0..]

compareValueExpr :: RType -> IRExpr -> IRExpr -> IRExpr
compareValueExpr TFloat v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr TInt v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr TBool v sample = IRIf (IROp OpAnd (IRUnaryOp OpNot sample) v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr TUnit _ _ = IRConst (VFloat 1)
compareValueExpr (Tuple ft st) v sample = IROp OpMult (compareValueExpr ft (IRTFst v) (IRTFst sample)) (compareValueExpr st (IRTSnd v) (IRTSnd sample))
compareValueExpr (TEither lr rr) v sample =
  IRIf (IRIsLeft v)
    (IRIf (IRIsLeft sample) (compareValueExpr lr (IRFromLeft v) (IRFromLeft sample)) (IRConst $ VFloat 0))
    (IRIf (IRIsRight sample) (compareValueExpr rr (IRFromRight v) (IRFromRight sample)) (IRConst $ VFloat 0))
compareValueExpr (TVarR _) v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
-- A deterministic list contributes an equality indicator: it is 1 exactly when
-- the sample matches (in particular the empty-list base of a Cons chain yields
-- 1, the multiplicative identity, so a list CDF reduces to the product of its
-- element CDFs).
compareValueExpr (ListOf _) v sample = IRIf (IROp OpEq sample v) (IRConst $ VFloat 1) (IRConst $ VFloat 0)
compareValueExpr (TADT _) _ _= IRError "Not yet implemented" -- TODO implement for ADTs
compareValueExpr rt _ _ = error $ "Comparison not implemented for type: " ++ show rt



packParamsIntoLetinsProb :: [String] -> [Expr] -> IRExpr -> IRExpr -> Supply IRExpr
--packParamsIntoLetinsProb [] [] expr _ = do
--  return expr
--packParamsIntoLetinsProb [] _ _ _ = error "More parameters than variables"
--packParamsIntoLetinsProb _ [] _ _ = error "More variables than parameters"
--packParamsIntoLetinsProb (v:vars) (p:params) expr sample = do
--  e <- packParamsIntoLetinsProb vars params expr sample
--  return $ IRLetIn v sample e --TODO sample austauschen durch teil von sample falls multivariable
packParamsIntoLetinsProb [v] [_] expr sample = do
  return $ IRLetIn v sample expr    --FIXME sample to auch toIRProbt werden

findLambdaVars :: IRExpr -> [String]
findLambdaVars (IRLambda n expr) = n:findLambdaVars expr
findLambdaVars expr = concatMap findLambdaVars (getIRSubExprs expr)


indicator :: IRExpr -> CompilerMonad  IRExpr
indicator condition = return $ IRIf condition (IRConst $ VFloat 1) (IRConst $ VFloat 0)

-- Must be used in conjunction with irMap, as it does not recurse
uniqueify :: [Varname] -> String -> IRExpr -> IRExpr
uniqueify vars prefix (IRVar name) | name `elem` vars = IRVar (prefix ++ name)
uniqueify vars prefix (IRLetIn name boundExpr bodyExpr) | name `elem` vars = IRLetIn (prefix ++ name) (uniqueify vars prefix boundExpr) (uniqueify vars prefix bodyExpr)
uniqueify vars prefix (IREnumSum name lst bodyExpr) | name `elem` vars = IREnumSum (prefix ++ name) lst (uniqueify vars prefix bodyExpr)
uniqueify _ _ e = e

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: CompilerMetadata -> Expr -> CompilerMonad  IRExpr
toIRGenerate meta (IfThenElse _ cond left right) = do
  c <- toIRGenerate meta cond
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IRIf c l r
toIRGenerate meta (GreaterThan _ left right) = do
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IROp OpGreaterThan l r
toIRGenerate meta (LessThan _ left right) = do
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IROp OpLessThan l r
toIRGenerate meta (ThetaI _ a ix) = do
  a' <- toIRGenerate meta a
  return $ IRTheta a' ix
toIRGenerate meta (Subtree _ a ix) = do
  a' <- toIRGenerate meta a
  return $ IRSubtree a' ix
toIRGenerate _ (Constant _ (VError e)) = return $ IRError e
toIRGenerate _ (Constant _ x) = return (IRConst (fmap failConversion x))
-- Distribution primitives (reserved-name Vars): each occurrence is a fresh draw.
toIRGenerate _ (Var _ "Uniform") = return $ IRSample IRUniform
toIRGenerate _ (Var _ "Normal") = return $ IRSample IRNormal
toIRGenerate meta (InjF ti (Named name) params) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  let resolvedName = resolveInjF (rType ti) name
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let FDecl {inputVars=vars, body=fwdExpr} = fwd
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen meta vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
toIRGenerate meta (Var _ name) = do
  case lookup name (typeEnv meta) of
    -- Var is a function
    Just (TArrow _ _, hasInference) ->
      let fullName = if hasInference then name ++ "_gen" else name in
        return $ IRVar fullName
    -- Var is a top level declaration (an therefor has a _gen function)
    Just (_, True) -> do
      return $ IRVar (name ++ "_gen")
    -- Var is a local variable
    Just (_, False) -> do
      return $ IRVar name
    Nothing -> error ("Could not find name in TypeEnv: " ++ name)
toIRGenerate meta (Lambda t name subExpr) =
  IRLambda name <$> toIRGenerate (extendMetaForLambda meta t name) subExpr
toIRGenerate meta (Apply _ l v) = do
  l' <- toIRGenerate meta l
  v' <- toIRGenerate meta v
  return $ IRApply l' v'
toIRGenerate meta (ReadNN _ name subexpr) = do
  sub <- toIRGenerate meta subexpr
  return $ IRApply (IRVar (name ++ "_auto_gen")) sub
toIRGenerate _ x = error ("found no way to convert to IRGen: " ++ show x)


packParamsIntoLetinsGen :: CompilerMetadata -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen _ [] [] expr = return $ expr
packParamsIntoLetinsGen _ [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen _ _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen meta (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate meta p
  e <- packParamsIntoLetinsGen meta vars params expr
  return $ IRLetIn v pExpr e

-- | Enumerate the application of a conditional/enumerable lambda to a discrete
-- argument. Computes sum over the argument's discrete support of
-- P(arg = value) * P_enum(body | bound = value). Shared by the top-level inference
-- rule and by toIREnumerate, so that nested enumerable `let`s
-- (`let c = .. in let d = .. in ..`) enumerate at every level instead of generating
-- the inner draws forward.
enumerateAppliedLambda :: CompilerMetadata -> Bool -> Expr -> Expr -> IRExpr -> CompilerMonad CompilationResult
enumerateAppliedLambda meta cumulative l v sample = do
  let lCn = chainName (getTypeInfo l)
  let Just (_, LambdaInfo boundVar bodyCn, _) = findEquivalentExpression (fcData meta) lCn
  let fExprs = map snd (functions (compilingProgram meta))
  let lBodyExpr = findExprWithCN fExprs bodyCn
  let newTypeEnv = (boundVar, (rType (getTypeInfo v), False)):typeEnv meta
  irTuple <- lift (runWriterT (do
    (pBranch, _, _) <- toIRInference meta False v (IRVar boundVar)
    (p, d, bc) <- toIREnumerate meta{typeEnv=newTypeEnv} cumulative lBodyExpr sample
    return (IROp OpMult p pBranch, d, bc))) <&> generateLetInBlock meta
  let discreteVVals = head [x | DiscreteValues x <- tags (getTypeInfo v)]
  let (outerBinds, innerTuple) = hoistInvariantBindings boundVar irTuple
  setVariables outerBinds
  let summed = IREnumSum boundVar discreteVVals (IRTFst innerTuple)
  let bc = IREnumSum boundVar discreteVVals (IRTSnd (IRTSnd innerTuple))
  return (summed, const0, bc)

toIREnumerate :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad CompilationResult
-- Nested enumerable application (e.g. an inner `let` binding a fresh discrete draw):
-- recurse with enumeration + weighting rather than generating the draw forward.
toIREnumerate meta cumulative (Apply _ l v) sample
  | isEnumerableApplication l v =
  enumerateAppliedLambda meta cumulative l v sample
toIREnumerate meta cumulative (Var TypeInfo{chainName=cn} _) sample = do
  let Just (equivCN, _, _) = findEquivalentExpression (fcData meta) cn
  let fs = map snd (functions (compilingProgram meta))
  let equivExpr = findExprWithCN fs equivCN
  toIREnumerate meta cumulative equivExpr sample
toIREnumerate meta cumulative (IfThenElse TypeInfo{rType=rt} c t e) sample = do
  cIR <- toIRGenerate meta c
  tIR <- toIRGenerate meta t
  eIR <- toIRGenerate meta e
  --(pBranch, _, _) <- toIRInference meta False distr elem
  -- Due to eager evaluation, we must make sure, that the wrong branch is not executed
  let condSelector e = IRIf cIR e const0
  let notCondSelector e = IRIf (IRUnaryOp OpNot cIR) e const0
  let cmpOp = case rt of { TFloat -> OpApprox; TVarR _ -> OpApprox; _ -> OpEq }
  let thenSelector = if cumulative then compareValueExpr rt tIR sample else IRIf (IROp cmpOp tIR sample) (IRConst (VFloat 1)) const0
  let elseSelector = if cumulative then compareValueExpr rt eIR sample else IRIf (IROp cmpOp eIR sample) (IRConst (VFloat 1)) const0
  let thenRes = condSelector thenSelector
  let elseRes = notCondSelector elseSelector
  let returnExpr = IROp OpPlus thenRes elseRes
  return (returnExpr, const0, IRConst (VFloat 1))
-- Fallback: under enumeration the bound variable carries a concrete enumerated value,
-- so the body is deterministic and can be generated forward and compared to the sample.
-- This covers shapes whose root is not an if, e.g. an InjF sum of conditional terms.
toIREnumerate meta cumulative e sample = do
  eIR <- toIRGenerate meta e
  let rt = rType (getTypeInfo e)
  let cmpOp = case rt of { TFloat -> OpApprox; TVarR _ -> OpApprox; _ -> OpEq }
  let res = if cumulative
              then compareValueExpr rt eIR sample
              else IRIf (IROp cmpOp eIR sample) (IRConst (VFloat 1)) const0
  return (res, const0, IRConst (VFloat 1))

-- | Strip the branch-count field from all probability-mode functions in the environment.
-- Applied after compilation and before optimisation when countBranches = False.
-- Two-step: (1) replace every IRTSnd(IRTSnd x) with IRConst(VFloat 0) to kill bc
-- extractions throughout the body; (2) peel through wrappers to collapse the outermost
-- (prob, (dim, bc)) triple back to (prob, dim).
stripBranchCount :: IREnv -> IREnv
stripBranchCount (IREnv funcs adts consts) = IREnv (map stripGroup funcs) adts consts
  where
    stripGroup fg = fg { probFun  = fmap stripFun (probFun fg)
                       , integFun = fmap stripFun (integFun fg)
                       , normalFun = fmap stripFun (normalFun fg) }
    stripFun (expr, doc) = (irMap killAll expr, doc)

    -- Apply stripOuterTriple to every lambda body, collapsing (prob, (dim, bc)) → (prob, dim)
    -- wherever a probability tuple is returned from a lambda.
    killAll (IRLambda n body) = IRLambda n (stripOuterTriple body)
    -- Fix dim and bc extractions from called-function results.
    -- These are stored in variables generated by mkVariable (format "l_<digits>_<suffix>"),
    -- which distinguishes them from user inputs like "sample" or auto-neural variables.
    -- After stripping, called functions return pairs so dim is at [1], not [1][0].
    killAll (IRTFst (IRTSnd (IRVar x))) | isGenVar x = IRTSnd (IRVar x)
    killAll (IRTSnd (IRTSnd (IRVar x))) | isGenVar x = IRConst (VFloat 0)
    killAll e = e

    -- Variables from mkVariable have the form "l_<digits>_<suffix>".
    isGenVar x = "l_" `isPrefixOf` x
              && not (null rest)
              && all isDigit (takeWhile (/= '_') rest)
              && '_' `elem` rest
      where rest = drop 2 x

    -- Collapse (prob, (dim, _)) → (prob, dim) peeling through IRLambda/IRLetIn wrappers,
    -- and through the query-type guard's IRIf (whose then-branch carries the real triple;
    -- the else-branch is an IRError, left untouched by the catch-all).
    stripOuterTriple (IRLambda n body)         = IRLambda n (stripOuterTriple body)
    stripOuterTriple (IRLetIn n v body)        = IRLetIn n v (stripOuterTriple body)
    stripOuterTriple (IRIf c t e)              = IRIf c (stripOuterTriple t) (stripOuterTriple e)
    stripOuterTriple (IRTCons a (IRTCons b _)) = IRTCons a b
    stripOuterTriple e                         = e

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

-- | Mirrors an inverse-witness expression's structure to build a runtime Bool
-- expression that evaluates to True iff the value that expression produces
-- (under the SAME runtime branching) contains a placeholder VAny introduced by
-- a lossy inverse reconstruction -- e.g. isLeft's inverse (always: @if tag then
-- Left VAny else Right VAny@), the Nothing arm of fromLeft's total inverse
-- (@if isRight m then Left (fromRight m) else Right VAny@, only ANY-tainted on
-- one branch), or a tuple projection's inverse (fst's: @TCons(b, VAny)@, tainted
-- only in the second slot). A single static "is this any-tainted" flag can't
-- capture either of the latter two -- one depends on which branch is taken,
-- the other differs per field of a composite value -- so this produces a
-- same-shaped runtime expression instead of a compile-time Bool, queried fresh
-- per (sub)value by 'mergeWitnessValue' rather than computed once for a whole
-- witness. Recognises the specific shapes this module's inverse FDecls build
-- (IRConst/IRIf/IRLeft/IRRight/IRLetIn); anything else falls back to a
-- shallow runtime OpIsAny check on the whole subexpression (safe: OpIsAny only
-- misses ANY nested below the top level, under-approximating "any-tainted",
-- which only affects which side 'mergeWitnessValue' prefers -- its OpEq guard
-- independently catches a genuine structural mismatch either way).
irRuntimeContainsAny :: IRExpr -> IRExpr
irRuntimeContainsAny (IRConst v) = if valueContainsAny v then constTrueIR else IRConst (VBool False)
irRuntimeContainsAny (IRIf c t e) = IRIf c (irRuntimeContainsAny t) (irRuntimeContainsAny e)
irRuntimeContainsAny (IRLeft a) = irRuntimeContainsAny a
irRuntimeContainsAny (IRRight a) = irRuntimeContainsAny a
irRuntimeContainsAny (IRLetIn n v b) = IRLetIn n v (irRuntimeContainsAny b)
irRuntimeContainsAny e = IRUnaryOp OpIsAny e

-- | Substitutes every occurrence of the IR variable @n@ with @val@. Not
-- capture-avoiding -- fine here, where it is only ever used to eliminate the
-- single free variable of a small inverse-witness template built from a
-- globally-unique "astN" chain name, never shadowed by a nested binder.
substIRVar :: String -> IRExpr -> IRExpr -> IRExpr
substIRVar n val = irMap (\e -> case e of { IRVar n' | n' == n -> val; _ -> e })

-- | Guards are Bool-valued IR over the sample and deterministic scope; a world
-- contributes only when all guards hold.
data WWorld = WWorld { wGuards :: [IRExpr], wSet :: WSet }

constTrueIR :: IRExpr
constTrueIR = IRConst (VBool True)

const1 :: IRExpr
const1 = IRConst (VFloat 1)

addGuard :: IRExpr -> WWorld -> WWorld
addGuard g (WWorld gs s) = WWorld (g:gs) s

intersectW :: WWorld -> WWorld -> WWorld
intersectW (WWorld g1 s1) (WWorld g2 s2) =
  let (g3, s3) = intersectSet s1 s2 in WWorld (g1 ++ g2 ++ g3) s3

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
intersectSet (WPoint p1 c1) (WPoint p2 c2) =
  ([IROp OpEq p1 p2], WPoint (mergeWitnessValue p1 p2) (IROp OpMult c1 c2))
intersectSet (WPoint p c) (WInterval lo hi) = (boundGuards p lo hi, WPoint p c)
intersectSet (WInterval lo hi) (WPoint p c) = (boundGuards p lo hi, WPoint p c)
intersectSet (WInterval lo1 hi1) (WInterval lo2 hi2) =
  ([], WInterval (maxWBound lo1 lo2) (minWBound hi1 hi2))

-- | Picks, field-by-field, whichever side of two witnesses for the same
-- variable is not ANY-tainted (checked fresh via 'irRuntimeContainsAny' at
-- each position, since informativeness can differ per field of a composite
-- witness -- e.g. one side recovers only a tuple's first field via fst's
-- inverse, the other only its second via snd's). Recurses through IRTCons so
-- such complementary partial witnesses combine into a single fully concrete
-- value instead of one silently overriding the other -- mirrors the
-- equivalent merge already used on the ordinary, non-set-witness
-- point-inversion path, ForwardChaining.hs's 'mergeExpr2' IRTCons/VAny cases.
-- Compatibility is 'intersectSet's job (a single guard on the whole value,
-- not per field -- see there for why); this function never rejects, only
-- chooses.
mergeWitnessValue :: IRExpr -> IRExpr -> IRExpr
mergeWitnessValue (IRTCons a1 b1) (IRTCons a2 b2) =
  IRTCons (mergeWitnessValue a1 a2) (mergeWitnessValue b1 b2)
mergeWitnessValue p1 p2 = IRIf (irRuntimeContainsAny p1) p2 p1

-- Membership guards of a point against interval bounds. Strictness is
-- irrelevant for the continuous measures this engine emits (a boundary point
-- has measure zero); the non-strict form gives boundary queries like p(0) for
-- |Normal| the density instead of an arbitrary 0.
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
memberGuard :: RType -> IRExpr -> WSet -> IRExpr
memberGuard rt val (WPoint p _) = case rt of
  TFloat  -> IROp OpApprox val p
  TVarR _ -> IROp OpApprox val p
  _       -> IROp OpEq val p
memberGuard _ val (WInterval lo hi) = case boundGuards val lo hi of
  [] -> constTrueIR
  gs -> foldr1 (IROp OpAnd) gs
memberGuard _ _ WFull  = constTrueIR
memberGuard _ _ WEmpty = IRConst (VBool False)

subtreeCNs :: Expr -> [ChainName]
subtreeCNs e = chainName (getTypeInfo e) : concatMap subtreeCNs (getSubExprs e)

subtreeHasOcc :: [ChainName] -> Expr -> Bool
subtreeHasOcc occs e = let cns = subtreeCNs e in any (`elem` cns) occs

-- | Entry point of the fallback, called from the probabilistic Apply arm after
-- 'toInvExprMaybe' failed. Builds the constraint worlds for the observation and
-- measures them against the bound distribution @v@.
setWitnessApply :: CompilerMetadata -> Bool -> RType -> Expr -> ChainName -> ChainName -> String -> Maybe String -> Expr -> IRExpr -> CompilerMonad CompilationResult
setWitnessApply meta cumulative rt l lResolvedCN lambdaBodyCN tag planDiag v sample = do
  let userVar = case l of Lambda _ n _ -> n; _ -> "<bound variable>"
  let refuse why = error $ unlines $
        [ "set-valued witness construction failed for the binding of '" ++ userVar ++ "' (lambda at " ++ lResolvedCN ++ "):"
        , why
        , "No occurrence of the bound variable is point-invertible either (forward"
        , "chaining found no inversion path). See design set-valued-witnesses." ]
        ++ maybe [] (\d ->
             [ "Plan-guided lazy enumeration was applicable but could not compile the body:"
             , d
             , "(design plan-guided-lazy-enumeration)" ]) planDiag
  if tag /= ""
    then refuse "the lambda is applied through higher-order machinery (tagged invocation), which the set-witness fallback does not support."
    else return ()
  case rt of
    TArrow _ _ -> refuse "the body returns a function."
    _ -> return ()
  let Program{functions=fs} = compilingProgram meta
  let bodyExpr = findExprWithCN (map snd fs) lambdaBodyCN
  let occs = fromMaybe [] (lookup lResolvedCN (lambdaVarOccurrences (fcData meta)))
  let target = if cumulative
        then WInterval WNegInf (WFinite sample)
        else WPoint sample const1
  worldsM <- invertToWorlds meta occs bodyExpr target
  case worldsM of
    -- A cumulative query the engine cannot invert (e.g. the multivariate CDF of
    -- a correlated tuple) is refused at runtime: the probability variant of the
    -- same program may be perfectly fine, and a compile-time error here would
    -- take it down too (all variants are compiled up front).
    Nothing | cumulative -> return
      ( IRError ("cannot compute this cumulative: the observation on binding '" ++ userVar
          ++ "' has no set-valued inverse in cumulative mode (design set-valued-witnesses)")
      , const0, const1)
    Nothing -> refuse ("the observation cannot be propagated onto the bound variable: the body"
      ++ " contains a node that is neither point-invertible, a comparison against a"
      ++ " deterministic bound, an if-then-else case split, a tuple of such parts, nor"
      ++ " deterministic given scope (e.g. it draws fresh randomness).")
    Just worlds -> do
      measured <- mapM (measureWorld meta v) worlds
      (pSum, dimSum, bcSum) <- case measured of
        -- no worlds can only mean an impossible observation
        []     -> return (const0, const0, const1)
        (m:ms) -> foldM (\(ap, ad, ab) (bp, bd, bb) -> do
                           (cp, cd) <- addP (ap, ad) (bp, bd)
                           return (cp, cd, IROp OpPlus ab bb)) m ms
      -- Full-ANY marginal short-circuit: guards and transported bounds are not
      -- ANY-aware, but the marginal of the whole observation is simply 1.
      if cumulative
        then return (pSum, dimSum, bcSum)
        else return ( IRIf (IRUnaryOp OpIsAny sample) const1 pSum
                    , IRIf (IRUnaryOp OpIsAny sample) const0 dimSum
                    , IRIf (IRUnaryOp OpIsAny sample) const1 bcSum )

-- | Measure one world against the bound distribution. The measure is compiled
-- in its own writer scope and kept under the world's guards, so bindings whose
-- evaluation is only valid when the guards hold are not hoisted past them.
measureWorld :: CompilerMetadata -> Expr -> WWorld -> CompilerMonad CompilationResult
measureWorld meta v (WWorld guards set) = do
  ((p, dim, bc), binds) <- lift (runWriterT (measureSet meta v set))
  let wrap = generateLetInExpr binds
  let guarded zero e = foldr (\g acc -> IRIf g acc zero) (wrap e) guards
  return (guarded const0 p, guarded const0 dim, guarded const0 bc)

measureSet :: CompilerMetadata -> Expr -> WSet -> CompilerMonad CompilationResult
measureSet meta v (WPoint p cov) = do
  (pv, dv, bv) <- toIRInference meta False v p
  -- change-of-variables correction only for continuous results, mirroring the
  -- point-witness path
  let scaled = IROp OpMult pv (IRIf (IROp OpEq dv const0) const1 (IRUnaryOp OpAbs cov))
  return (scaled, dv, bv)
measureSet meta v (WInterval lo hi) = do
  (cdfHi, bcHi) <- cdfAtBound meta v hi
  (cdfLo, bcLo) <- cdfAtBound meta v lo
  let diff = IROp OpSub cdfHi cdfLo
  -- an empty runtime intersection shows up as a non-positive difference
  let clamped = IRIf (IROp OpGreaterThan diff const0) diff const0
  let bc = case (hi, lo) of
        (WFinite _, _) -> bcHi
        (_, WFinite _) -> bcLo
        _              -> const1
  return (clamped, const0, bc)
measureSet _ _ WFull  = return (const1, const0, const1)
measureSet _ _ WEmpty = return (const0, const0, const1)

cdfAtBound :: CompilerMetadata -> Expr -> WBound -> CompilerMonad (IRExpr, IRExpr)
cdfAtBound _ _ WNegInf = return (const0, const1)
cdfAtBound _ _ WPosInf = return (const1, const1)
cdfAtBound meta v (WFinite e) = do
  (p, _, bc) <- toIRInference meta True v e
  return (p, bc)

-- | Invert the observation @body ∈ target@ into constraint worlds on the bound
-- variable (occurrences @occs@). Nothing when some node on the way is not
-- supported — the caller refuses with a diagnostic.
invertToWorlds :: CompilerMetadata -> [ChainName] -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
invertToWorlds meta occs body target
  -- x-free subtree: deterministic given scope reduces to a membership test of
  -- its value against the target; anything else draws fresh randomness, and
  -- folding that in alongside set constraints is not supported (the
  -- point-witness path's body-factor folding handles the point case).
  | not (subtreeHasOcc occs body) =
      if pType (getTypeInfo body) == Deterministic
        then do
          bIR <- toIRGenerate meta body
          return (Just [WWorld [memberGuard (rType (getTypeInfo body)) bIR target] WFull])
        else return Nothing
invertToWorlds meta occs body target = do
  direct <- transportDirect meta occs body target
  case direct of
    Just ws -> return (Just ws)
    Nothing -> case body of
      IfThenElse _ c t e
        | not (subtreeHasOcc occs c) && pType (getTypeInfo c) == Deterministic -> do
            g <- toIRGenerate meta c
            wsT <- invertToWorlds meta occs t target
            wsE <- invertToWorlds meta occs e target
            case (wsT, wsE) of
              (Just ts, Just es) -> return (Just (map (addGuard g) ts ++ map (addGuard (IRUnaryOp OpNot g)) es))
              _ -> return Nothing
        | subtreeHasOcc occs c -> do
            -- the condition constrains the same draw: case split and intersect
            cT <- invertToWorlds meta occs c (WPoint constTrueIR const1)
            cF <- invertToWorlds meta occs c (WPoint (IRConst (VBool False)) const1)
            wsT <- invertToWorlds meta occs t target
            wsE <- invertToWorlds meta occs e target
            case (cT, cF, wsT, wsE) of
              (Just cts, Just cfs, Just ts, Just es) ->
                return (Just ([intersectW cw tw | cw <- cts, tw <- ts]
                           ++ [intersectW cw ew | cw <- cfs, ew <- es]))
              _ -> return Nothing
        | otherwise -> return Nothing
      LessThan _ lop rop -> comparisonWorlds meta occs False lop rop target
      GreaterThan _ lop rop -> comparisonWorlds meta occs True lop rop target
      InjF _ (Named "TCons") [pa, pb] -> case target of
        WPoint s _ -> do
          wsA <- invertToWorlds meta occs pa (WPoint (IRTFst s) const1)
          wsB <- invertToWorlds meta occs pb (WPoint (IRTSnd s) const1)
          case (wsA, wsB) of
            (Just as, Just bs) -> return (Just [intersectW a b | a <- as, b <- bs])
            _ -> return Nothing
        -- a multivariate CDF over correlated components is not defined here
        _ -> return Nothing
      _ -> return Nothing

-- | Point/interval transport of a whole subtree onto its single occurrence of
-- the bound variable, via forward chaining seeded at the subtree root. Only
-- fires for exactly one occurrence: with several, a point inversion through
-- one of them would silently drop the others' constraints — the structural
-- cases above split those instead.
transportDirect :: CompilerMetadata -> [ChainName] -> Expr -> WSet -> CompilerMonad (Maybe [WWorld])
transportDirect meta occs body target = case filter (`elem` subtreeCNs body) occs of
  [occ] -> case target of
    WPoint s c0 -> case toSeededInvExpr (fcData meta) (adtDecls meta) bodyCN occ of
      Nothing -> return Nothing
      Just (g0, cov0, guard0) -> do
        g     <- pruneDeadLetIns <$> materializeAnchors meta g0
        cov   <- pruneDeadLetIns <$> materializeAnchors meta cov0
        guard <- pruneDeadLetIns <$> materializeAnchors meta guard0
        let applyTo e arg = IRApply (IRLambda bodyCN e) arg
        -- The inversion may pass through a deconstructing InjF (e.g.
        -- fromLeft/fromRight) only applicable on one arm; fold that as an
        -- extra world guard so measureWorld zeroes this world instead of
        -- evaluating the (crashing on the wrong arm) point value -- see
        -- observe-partials-umbrella N1b.
        -- Substitute eagerly (rather than leaving an IRApply/IRLambda shell
        -- for the interpreter to beta-reduce at runtime) so the witness value
        -- is a genuinely literal expression -- e.g. IRTCons (IRTFst sample)
        -- (IRConst VAny) rather than that same tree hidden behind an
        -- application -- for 'mergeWitnessValue' (see 'intersectSet') to
        -- pattern-match on directly when this witness is later intersected
        -- with another occurrence's.
        let value = substIRVar bodyCN s g
        return (Just [WWorld [applyTo guard s] (WPoint value (IROp OpMult c0 (applyTo cov s)))])
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
        return (Just [WWorld [] (WInterval lo' hi')])
    _ -> return Nothing
  _ -> return Nothing
  where bodyCN = chainName (getTypeInfo body)

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
    splitOn side b flipped = do
      let lower = WInterval WNegInf (WFinite b)
          upper = WInterval (WFinite b) WPosInf
      let (setT, setF) = if isGT /= flipped then (upper, lower) else (lower, upper)
      wsT <- invertToWorlds meta occs side setT
      wsF <- invertToWorlds meta occs side setF
      case (wsT, wsF) of
        (Just ts, Just fs) -> return (Just (
             map (addGuard (memberGuard TBool constTrueIR target)) ts
          ++ map (addGuard (memberGuard TBool (IRConst (VBool False)) target)) fs))
        _ -> return Nothing

-- ===== Plan-guided lazy enumeration (design plan-guided-lazy-enumeration, M1) =====
--
-- When the bound variable of a probabilistic let is the structured output of a
-- neural network (an argument that is a ReadNN whose declaration yields a
-- PartitionPlan), the NN's distribution over that value is fully factorized
-- per plan slot -- softmax regions for enums and constructor flags, (mu,
-- sigma) pairs for continuous leaves -- and the plan is depth-unrolled, hence
-- finite. So instead of materializing the argument's (possibly astronomically
-- large) discrete support into an IREnumSum, the observation is inverted into
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

-- | Constraint on one leaf REGION of the plan, identified by the flat offset
-- of its first logit (regions are always constrained as a whole, so the base
-- offset is a unique key). 'PLeafCon' constrains a discrete region (a
-- Discretes region or an ADT constructor-flag region): allowed slots are
-- (relative index, guard) pairs; a slot contributes its logit's mass only
-- when its Bool-valued guard holds, and an empty slot list is an
-- unsatisfiable constraint (the world measures 0). Milestone 3 adds
-- constraints on Continuous leaves (mu = vec[base], sigma = vec[base+1]):
-- 'PLeafIvl' confines the leaf to an interval, measured as a Gaussian CDF
-- difference (mass, dim 0); 'PLeafPt' pins it to a point, measured as the
-- leaf's density times the |change-of-variables| factor (dim 1), under
-- membership guards accumulated from intersected intervals.
data PLeafCon = PLeafCon Int [(Int, IRExpr)]
              | PLeafIvl Int WBound WBound
              | PLeafPt  Int IRExpr IRExpr [IRExpr]

plcBase :: PLeafCon -> Int
plcBase (PLeafCon b _)    = b
plcBase (PLeafIvl b _ _)  = b
plcBase (PLeafPt b _ _ _) = b

-- | A guarded conjunction of per-leaf constraints; the plan-leaf analogue of
-- 'WWorld'. Contributes (product of constrained leaf masses) when all guards
-- hold, else 0. 'pwPairs' (milestone 3) are pairwise couplings between two
-- continuous leaves: (a, b) constrains leaf@a > leaf@b, measured in closed
-- form via the difference Gaussian. A world may couple each continuous leaf
-- at most once, and a coupled leaf may carry no other constraint -- anything
-- beyond that is an orthant probability, which the language excludes
-- (checked in 'pwOverCoupled'; design plan-guided-lazy-enumeration M3).
-- 'pwFactor' (milestone 4) is a pre-measured multiplicative mass contribution
-- carried by the world -- const1 for every ordinary world, and the summed
-- mass of a collapsed value group for the DP path-counting worlds (see
-- 'planGroupValues'): a group of same-value worlds is merged into one world
-- with empty constraints and this factor, so counting folds stay O(depth)
-- instead of 2^depth.
data PlanWorld = PlanWorld { pwGuards :: [IRExpr], pwCons :: [PLeafCon], pwPairs :: [(Int, Int)], pwFactor :: IRExpr }

-- | An unguarded world from leaf constraints alone.
pw1 :: [PLeafCon] -> PlanWorld
pw1 cs = PlanWorld [] cs [] const1

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
pwUnsat (PlanWorld gs cons pairs _) = any conUnsat cons
                                 || any ((== Just False) . staticBool) gs
                                 || any (\(a, b) -> (b, a) `elem` pairs || a == b) pairs
  where
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
pwOverCoupled (PlanWorld _ cons pairs _)
  | (base:_) <- overCoupled = Just
      ("a world couples the continuous leaf at logit offset " ++ show base
       ++ " to other random leaves more than once (or couples it and also"
       ++ " bounds it); measuring this exactly is an orthant probability,"
       ++ " which is out of scope by design (plan-guided-lazy-enumeration,"
       ++ " milestone 3 refusal rule)")
  | otherwise = Nothing
  where
    coupled = concat [[a, b] | (a, b) <- pairs]
    contCon = [plcBase c | c <- cons, isCont c]
    isCont PLeafCon{} = False
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
    -- | (callee body CN, sum of plan-argument offsets) per active
    -- specialization: re-entering a body already on the stack without
    -- strictly descending the plan cannot terminate and is declined.
  , psStack    :: [(ChainName, Int)]
    -- | The variable the raw logit vector is bound to (milestone 4): the value
    -- grouping measures collapsed worlds against it in-flight, so it must be
    -- bound before the traversal rather than only at measurement time.
  , psNnRaw    :: String
    -- | Whether the milestone-4 value grouping ('planGroupValues') may collapse
    -- same-value worlds into a single measured mass. Sound only when the
    -- counting fold is the SOLE reader of the neural scene: merging bakes the
    -- fold's leaf constraints (including the shared structural SCons/Obj flags)
    -- into one mass, so any sibling predicate re-constraining those same leaves
    -- would double-count them. Enabled iff the plan-bound variable occurs once
    -- in the observation (see 'planWitnessApply').
  , psMerge    :: Bool
  }

emptyPlanState :: String -> Bool -> PlanState
emptyPlanState nnRaw merge = PlanState Map.empty Map.empty [] nnRaw merge

-- (CompilerMonad spelled out: it is an unsaturated synonym application otherwise)
type PlanM a = StateT PlanState (WriterT [(String, IRExpr)] Supply) a

planAddGuard :: IRExpr -> PlanWorld -> PlanWorld
planAddGuard g w = w { pwGuards = g : pwGuards w }

andGuard :: IRExpr -> IRExpr -> IRExpr
andGuard a b | a == constTrueIR = b
             | b == constTrueIR = a
             | otherwise        = IROp OpAnd a b

-- | Multiply two world mass factors, dropping identity const1 factors.
mulFactor :: IRExpr -> IRExpr -> IRExpr
mulFactor a b | a == const1 = b
              | b == const1 = a
              | otherwise   = IROp OpMult a b

-- | Intersect two constraints on the same region. Discrete regions keep the
-- slots allowed by both, conjoining their guards. Continuous leaves follow
-- the scalar 'intersectSet' conventions: interval-interval tightens the
-- bounds, a point absorbs an interval as membership guards, and point-point
-- keeps the first (both compute the same value from the same observation --
-- the mergeExpr convention). A region cannot be discrete in one constraint
-- and continuous in another (the plan fixes each region's kind).
intersectLeafCon :: PLeafCon -> PLeafCon -> PLeafCon
intersectLeafCon (PLeafCon b s1) (PLeafCon _ s2) =
  PLeafCon b [ (i, andGuard g1 g2) | (i, g1) <- s1, Just g2 <- [lookup i s2] ]
intersectLeafCon (PLeafIvl b lo1 hi1) (PLeafIvl _ lo2 hi2) =
  PLeafIvl b (maxWBound lo1 lo2) (minWBound hi1 hi2)
intersectLeafCon (PLeafPt b v cov gs) (PLeafIvl _ lo hi) =
  PLeafPt b v cov (gs ++ boundGuards v lo hi)
intersectLeafCon (PLeafIvl _ lo hi) (PLeafPt b v cov gs) =
  PLeafPt b v cov (gs ++ boundGuards v lo hi)
intersectLeafCon p@(PLeafPt {}) (PLeafPt {}) = p
intersectLeafCon c c' = error ("plan leaf region at offset " ++ show (plcBase c)
  ++ " is constrained as both discrete and continuous (plan invariant violation): "
  ++ show (isDisc c) ++ " vs " ++ show (isDisc c'))
  where isDisc PLeafCon{} = True
        isDisc _          = False

insertLeafCon :: PLeafCon -> [PLeafCon] -> [PLeafCon]
insertLeafCon c [] = [c]
insertLeafCon c (c':cs) | plcBase c == plcBase c' = intersectLeafCon c' c : cs
                        | otherwise               = c' : insertLeafCon c cs

intersectPlanW :: PlanWorld -> PlanWorld -> PlanWorld
intersectPlanW (PlanWorld g1 c1 p1 f1) (PlanWorld g2 c2 p2 f2) =
  PlanWorld (g1 ++ g2) (foldl (flip insertLeafCon) c1 c2) (nub (p1 ++ p2)) (mulFactor f1 f2)

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
planDetGuard :: RType -> IRExpr -> PTarget -> IRExpr
planDetGuard rt val (PTPoint s) = case rt of
  TFloat  -> IROp OpApprox val s
  TVarR _ -> IROp OpApprox val s
  _       -> IROp OpEq val s
planDetGuard rt val (PTUpTo s) = case rt of
  TBool -> IROp OpOr (IRUnaryOp OpNot val) s
  _     -> IRUnaryOp OpNot (IROp OpGreaterThan val s)

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
planNodeName (InjF _ (Named n) _) = "InjF " ++ n
planNodeName (Var _ n)            = "Var " ++ n
planNodeName (Apply _ _ _)        = "Apply"
planNodeName e                    = head (words (show e))

-- | Field bases of an ADTPlan region at offset @off@: for each constructor
-- (in plan order), the flat offset where its field block starts. Mirrors the
-- constrIx arithmetic of AutoNeural.makeProbRec exactly.
adtCtorBases :: Int -> [(String, [PartitionPlan])] -> [Int]
adtCtorBases off ctorPlans = scanl (+) (off + length ctorPlans) (map (sum . map getSize . snd) ctorPlans)

-- | Look up an ADT field accessor name across the declared ADTs: yields the
-- owning constructor's name and the field's index within it.
lookupADTAccessor :: [ADTDecl] -> String -> Maybe (String, Int)
lookupADTAccessor adts name = listToMaybe
  [ (cName, fj)
  | adt <- adts, (cName, fields) <- constructors adt
  , Just fj <- [elemIndex name (map fst fields)] ]

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
    go (InjF _ (Named "fst") [e]) = descend e $ \(PlanRef sub off) cons -> case sub of
      TuplePlan a _ -> Right (PlanRef a off, cons)
      _ -> Left "fst applied to a non-tuple plan slice"
    go (InjF _ (Named "snd") [e]) = descend e $ \(PlanRef sub off) cons -> case sub of
      TuplePlan a b -> Right (PlanRef b (off + getSize a), cons)
      _ -> Left "snd applied to a non-tuple plan slice"
    go (InjF _ (Named nm) [e])
      | Just (cName, fj) <- lookupADTAccessor (adtDecls meta) nm =
          descend e $ \(PlanRef sub off) cons -> case sub of
            ADTPlan _ ctorPlans
              | Just ci <- elemIndex cName (map fst ctorPlans) ->
                  let fieldPlans = snd (ctorPlans !! ci)
                      fBase = (adtCtorBases off ctorPlans !! ci) + sum (map getSize (take fj fieldPlans))
                      flagCon = PLeafCon off [(ci, constTrueIR)]
                  in Right (PlanRef (fieldPlans !! fj) fBase, insertLeafCon flagCon cons)
              | otherwise -> Left ("accessor " ++ nm ++ ": constructor " ++ cName ++ " is not present in the plan (depth-pruned)")
            _ -> Left ("accessor " ++ nm ++ " applied to a non-ADT plan slice")
    go _ = Nothing
    descend e k = fmap (>>= uncurry k) (go e)

-- | Worlds constraining a plan slice to lie in the target. Only shapes whose
-- inversion is supported in milestone 1: Discretes leaves (point and upto),
-- component-wise tuple decomposition against a point, and nullary-constructor
-- ADT regions against a point (guarded per constructor by is<Ctor> on the
-- observed value).
planRefWorlds :: PlanRef -> [PLeafCon] -> PTarget -> Either String [PlanWorld]
planRefWorlds (PlanRef (Discretes rty (MultiDiscretes vals)) off) cons tgt =
  Right [pw1 (insertLeafCon
          (PLeafCon off [ (i, planDetGuard rty (IRConst (valueToIR v)) tgt) | (i, v) <- zip [0..] vals ])
          cons)]
planRefWorlds (PlanRef (TuplePlan a b) off) cons (PTPoint s) = do
  wa <- planRefWorlds (PlanRef a off) cons (PTPoint (IRTFst s))
  wb <- planRefWorlds (PlanRef b (off + getSize a)) [] (PTPoint (IRTSnd s))
  return [ intersectPlanW x y | x <- wa, y <- wb ]
planRefWorlds (PlanRef (ADTPlan _ ctorPlans) off) cons (PTPoint s)
  | all (null . snd) ctorPlans =
      Right [pw1 (insertLeafCon
              (PLeafCon off [ (i, IRApply (IRVar ("is" ++ cn)) s) | (i, (cn, _)) <- zip [0..] ctorPlans ])
              cons)]
planRefWorlds (PlanRef Continuous off) cons (PTPoint s) =
  Right [pw1 (insertLeafCon (PLeafPt off s const1 []) cons)]
planRefWorlds (PlanRef Continuous off) cons (PTUpTo s) =
  Right [pw1 (insertLeafCon (PLeafIvl off WNegInf (WFinite s)) cons)]
planRefWorlds (PlanRef sub _) _ _ =
  Left ("this plan slice cannot be matched against the observation directly (unsupported in milestone 1): " ++ head (words (show sub)))

-- | Peel invertible monotone float transforms off a plan-dependent operand
-- down to a Continuous plan slice (milestone 3). Supports the same static
-- envelope as ForwardChaining.stepMonotonicity: plus/neg/double/exp/log
-- unconditionally, mult only by a literal constant (any other deterministic
-- operand has no statically known direction). Yields the slice, its accessor
-- constraints, a pure transformer from an observed bound to (leaf-space
-- bound, |d leaf-space bound / d observed bound| change-of-variables factor),
-- and the chain's net monotonicity. Nothing: not such a chain over a
-- continuous slice -- the caller tries its other rules (in particular, this
-- deliberately declines chains bottoming out at discrete slices, which the
-- value-enumeration path already covers).
planPeelSlice :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Maybe (Either String (PlanRef, [PLeafCon], IRExpr -> (IRExpr, IRExpr), Monotonicity)))
planPeelSlice meta env = go
  where
    go e | Just refE <- planEvalRef meta env e = return $ case refE of
      Right (ref@(PlanRef Continuous _), cons) ->
        Just (Right (ref, cons, \b -> (b, const1), MonInc))
      _ -> Nothing
    go (InjF _ (Named "neg") [a])    = chain a (IRUnaryOp OpNeg) (const const1) MonDec
    go (InjF _ (Named "double") [a]) = chain a (\b -> IROp OpDiv b (IRConst (VFloat 2))) (const (IRConst (VFloat 0.5))) MonInc
    go (InjF _ (Named "exp") [a])    = chain a (IRUnaryOp OpLog) (\b -> IROp OpDiv const1 b) MonInc
    go (InjF _ (Named "log") [a])    = chain a (IRUnaryOp OpExp) (IRUnaryOp OpExp) MonInc
    go (InjF _ (Named "plus") [a, b])
      | pdep a, pfree b = plusStep a b
      | pdep b, pfree a = plusStep b a
    go (InjF _ (Named "mult") [a, b])
      | pdep a, pfree b = multStep a b
      | pdep b, pfree a = multStep b a
    go _ = return Nothing
    pdep = subtreeHasOcc (planEnvOccs env)
    pfree x = not (pdep x) && pType (getTypeInfo x) == Deterministic
    plusStep pe de = do
      d <- planGenDet meta env de
      chain pe (\b -> IROp OpSub b d) (const const1) MonInc
    multStep pe de = do
      d <- planGenDet meta env de
      case d of
        IRConst (VFloat f) | f /= 0 ->
          chain pe (\b -> IROp OpDiv b d) (const (IRConst (VFloat (1 / abs f))))
                   (if f > 0 then MonInc else MonDec)
        _ -> return (Just (Left "multiplication of a continuous plan leaf by a non-literal deterministic operand has no statically known monotonicity direction"))
    -- Compose one peeled step (observed -> operand space) with the rest of
    -- the chain (operand space -> leaf space).
    chain pe stepF covF stepDir = do
      innerM <- go pe
      return $ fmap (fmap (\(ref, cons, invT, dir) ->
        ( ref, cons
        , \b -> let (bi, covI) = invT (stepF b) in (bi, mulCov (covF b) covI)
        , if stepDir == MonDec then flipDir dir else dir ))) innerM
    flipDir MonInc = MonDec
    flipDir MonDec = MonInc
    mulCov x y | x == const1 = y
               | y == const1 = x
               | otherwise   = IROp OpMult x y

-- | Invert the observation @body ∈ target@ into plan-leaf constraint worlds.
-- The plan-backed analogue of 'invertToWorlds'. Left carries a diagnostic
-- naming the unsupported node; the caller falls through to set-witnesses.
planInvert :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planInvert meta env body target
  -- Plan-free subtree: deterministic given scope reduces to a membership
  -- guard of its value against the target; anything else draws fresh
  -- randomness. (Det-bound parameter occurrences are deterministic here.)
  | not (subtreeHasOcc (planEnvOccs env) body) =
      if pType (getTypeInfo body) == Deterministic
        then do
          bIR <- planGenDet meta env body
          return (Right [PlanWorld [planDetGuard (rType (getTypeInfo body)) bIR target] [] [] const1])
        else return (Left ("a subtree independent of the plan-bound variables draws fresh randomness: " ++ planNodeName body))
planInvert meta env body target
  | Just refE <- planEvalRef meta env body =
      return (refE >>= \(ref, cons) -> planRefWorlds ref cons target)
planInvert meta env body target = case body of
  IfThenElse _ c t e
    | not (subtreeHasOcc occs c) && pType (getTypeInfo c) == Deterministic -> do
        g <- planGenDet meta env c
        wsT <- planInvert meta env t target
        wsE <- planInvert meta env e target
        return ((\ts es -> map (planAddGuard g) ts ++ map (planAddGuard (IRUnaryOp OpNot g)) es) <$> wsT <*> wsE)
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
    | otherwise -> return (Left "an if condition independent of the plan-bound variables draws fresh randomness")
  InjF _ (Named "not") [a] -> do
    ab <- planInvertBool meta env a
    return ((\(t, f) -> planBoolWorlds target f t) <$> ab)
  InjF _ (Named "and") [a, b] -> do
    ab <- planInvertBool meta env a
    bb <- planInvertBool meta env b
    return $ do
      (at, af) <- ab
      (bt, bf) <- bb
      let tw = liveIntersects at bt
      let fw = af ++ liveIntersects at bf
      return (planBoolWorlds target tw fw)
  InjF _ (Named "or") [a, b] -> do
    ab <- planInvertBool meta env a
    bb <- planInvertBool meta env b
    return $ do
      (at, af) <- ab
      (bt, bf) <- bb
      let tw = at ++ liveIntersects af bt
      let fw = liveIntersects af bf
      return (planBoolWorlds target tw fw)
  InjF _ (Named nm) [a]
    | Just ctor <- ctorTestName nm -> case planEvalRef meta env a of
        Just (Right (PlanRef (ADTPlan _ ctorPlans) off, cons)) -> do
          let n = length ctorPlans
          let ci = elemIndex ctor (map fst ctorPlans)
          -- a constructor pruned from the plan (depth limit) simply has mass 0
          let inSet  = maybe [] (\i -> [(i, constTrueIR)]) ci
          let outSet = [ (i, constTrueIR) | i <- [0 .. n-1], Just i /= ci ]
          let tw = [pw1 (insertLeafCon (PLeafCon off inSet)  cons)]
          let fw = [pw1 (insertLeafCon (PLeafCon off outSet) cons)]
          return (Right (planBoolWorlds target tw fw))
        Just (Left why) -> return (Left why)
        _ -> return (Left (nm ++ " applied to something that is not a plan slice"))
  InjF _ (Named "eq") [a, b]
    | planDep a, isDetSide b -> planLeafEq a b
    | planDep b, isDetSide a -> planLeafEq b a
  LessThan    _ a b -> planCmp False a b
  GreaterThan _ a b -> planCmp True  a b
  Apply {} -> planApplyTarget meta env body target
  _ -> return (Left ("unsupported node in plan traversal: " ++ planNodeName body))
  where
    occs = planEnvOccs env
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
          let tw = [pw1 (insertLeafCon (PLeafCon off [ (i, eqG v)                    | (i, v) <- zip [0..] vals ]) cons)]
          let fw = [pw1 (insertLeafCon (PLeafCon off [ (i, IRUnaryOp OpNot (eqG v)) | (i, v) <- zip [0..] vals ]) cons)]
          return (Right (planBoolWorlds target tw fw))
        Just (Right (PlanRef (ADTPlan _ ctorPlans) off, cons)) | all (null . snd) ctorPlans -> do
          dv <- bindDetSide "eq_rhs" de
          let isG cn = IRApply (IRVar ("is" ++ cn)) (IRVar dv)
          let tw = [pw1 (insertLeafCon (PLeafCon off [ (i, isG cn)                    | (i, (cn, _)) <- zip [0..] ctorPlans ]) cons)]
          let fw = [pw1 (insertLeafCon (PLeafCon off [ (i, IRUnaryOp OpNot (isG cn)) | (i, (cn, _)) <- zip [0..] ctorPlans ]) cons)]
          return (Right (planBoolWorlds target tw fw))
        -- Continuous leaf pinned to a deterministic value (milestone 3): the
        -- True outcome is a point constraint (dim-1 density); the False
        -- outcome leaves the leaf free -- the complement of a point is a
        -- full-measure set (the point is a null set).
        Just (Right (PlanRef Continuous off, cons)) -> do
          dv <- bindDetSide "eq_rhs" de
          contEqWorlds off cons (IRVar dv) const1
        Just (Left why) -> return (Left why)
        _ -> do
          peelM <- planPeelSlice meta env pe
          case peelM of
            -- A monotone transform chain over a continuous leaf (milestone
            -- 3): pin the leaf at the inverse-transformed value, with the
            -- change-of-variables factor of the inverse chain.
            Just (Right (PlanRef _ off, cons, invT, _)) -> do
              dv <- bindDetSide "eq_rhs" de
              let (bnd, cov) = invT (IRVar dv)
              bv <- lift (mkVariable "eq_bnd")
              lift (setVariables [(bv, bnd)])
              contEqWorlds off cons (IRVar bv) cov
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
    contEqWorlds off cons v cov = do
      let tw = [pw1 (insertLeafCon (PLeafPt off v cov []) cons)]
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
          Just (Right (PlanRef _ off, cons, invT, dir)) -> do
            dv <- bindDetSide "cmp_rhs" de
            let (bnd, _) = invT (IRVar dv)
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
            let mkW pr = (pw1 cons) { pwPairs = [pr] }
            let tw = [mkW (if isGT then (offA, offB) else (offB, offA))]
            let fw = [mkW (if isGT then (offB, offA) else (offA, offB))]
            return (Right (planBoolWorlds target tw fw))
      (Just (Left why), _) -> return (Left why)
      (_, Just (Left why)) -> return (Left why)
      _ -> return (Left "a comparison with both sides plan-dependent is only supported between two continuous plan leaves (single pairwise coupling)")

-- | Canonical (outcome-True, outcome-False) worlds of a Bool-valued node.
planInvertBool :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String ([PlanWorld], [PlanWorld]))
planInvertBool meta env e = do
  t <- planInvert meta env e (PTPoint constTrueIR)
  f <- planInvert meta env e (PTPoint (IRConst (VBool False)))
  return ((,) <$> t <*> f)

-- | Fold an IR value expression built from numeric literals and plus/mult
-- into a constant Value, when possible. Counting-fold values are always
-- statically foldable (literal increments combined by plus); anything else is
-- left ungrouped by the value DP ('planGroupValues').
foldValueConst :: IRExpr -> Maybe IRValue
foldValueConst (IRConst v) = Just v
foldValueConst (IROp op a b) = do
  va <- foldValueConst a
  vb <- foldValueConst b
  case op of
    OpPlus -> num (+) va vb
    OpMult -> num (*) va vb
    _      -> Nothing
  where
    num f (VFloat x) (VFloat y) = Just (VFloat (f x y))
    num f (VInt  x)  (VInt  y)  = Just (VInt (round (f (fromIntegral x :: Double) (fromIntegral y))))
    num _ _ _                   = Nothing
foldValueConst _ = Nothing

-- | Milestone-4 value-grouped DP: collapse (value, world) pairs that share a
-- statically-known value into one world carrying the summed mass, bound to a
-- fresh IR variable so the mass is shared rather than re-inlined at every
-- recursion level. This is what turns counting folds from 2^depth enumerated
-- worlds into O(depth) value groups per level -- the
-- [[materialized-marginals-semiring]] idea in its first concrete consumer.
-- Soundness rests on three things: the (value, world) pairs are a partition, so
-- summing a same-value subset is exactly P(value = v); constraints shared
-- identically by every world of a group stay LIVE ('commonDiscreteCons') so an
-- outer re-constraint still dedups; and merging fires at all only when the fold
-- is the scene's sole reader ('psMerge'), so no sibling predicate re-constrains
-- a baked leaf. Only all-dim-0, uncoupled worlds with a foldable value are
-- merged; multi-world groups collapse (a singleton keeps its constraints, so no
-- premature commitment), and anything non-foldable or carrying a point/pair
-- constraint passes through untouched.
planGroupValues :: [(IRExpr, PlanWorld)] -> PlanM [(IRExpr, PlanWorld)]
planGroupValues pairs = do
  merge <- gets psMerge
  nnRaw <- gets psNnRaw
  if not merge
    -- unsafe to collapse (the fold shares leaves with a sibling predicate);
    -- keep the milestone-2 world-per-path enumeration unchanged
    then return pairs
    else do
      merged <- mapM (mergeGroup nnRaw) grouped
      return (merged ++ keep)
  where
    (mergeable, keep) = partitionEithers (map classify pairs)
    classify (ve, w)
      | Just v <- foldValueConst ve, canMerge w = Left (show v, (v, [w]))
      | otherwise                               = Right (ve, w)
    canMerge w = null (pwPairs w) && not (any isPt (pwCons w))
    isPt PLeafPt{} = True
    isPt _         = False
    -- group same-value worlds, keeping ascending value-key order for
    -- reproducible IR
    grouped = Map.elems (Map.fromListWith comb mergeable)
    comb (v, ws1) (_, ws2) = (v, ws1 ++ ws2)
    mergeGroup _ (v, [w]) = return (IRConst v, w)
    -- Merge same-value worlds. Constraints shared identically by every world
    -- in the group (a discrete leaf region with the same slots+guards -- in
    -- practice the recursion's accessor/constructor flags) are kept LIVE on the
    -- collapsed world, so an outer context re-constraining that leaf still
    -- dedups via 'intersectLeafCon' instead of double-counting it. Only the
    -- residual (the internal randomness that varies across the group, disjoint
    -- from anything constrained outside) is baked into the summed mass factor.
    mergeGroup nnRaw (v, ws) = do
      let common = commonDiscreteCons ws
          residual w = w { pwCons = filter (\c -> not (any (conEq c) common)) (pwCons w) }
      let mass = foldr1 (IROp OpPlus) (map (planWorldMass nnRaw . residual) ws)
      mv <- lift (mkVariable "cnt_mass")
      lift (setVariables [(mv, mass)])
      return (IRConst v, PlanWorld [] common [] (IRVar mv))
    -- discrete leaf constraints present (identically) in every world's cons
    commonDiscreteCons (w:ws') =
      [ c | c@(PLeafCon _ _) <- pwCons w, all (\w' -> any (conEq c) (pwCons w')) ws' ]
    commonDiscreteCons [] = []
    conEq (PLeafCon b1 s1) (PLeafCon b2 s2) = b1 == b2 && s1 == s2
    conEq _ _ = False

-- | Enumerate the possible values of a plan-dependent expression as
-- (value, world) pairs -- the milestone-2 mechanism behind counting folds.
-- The worlds partition the plan-consistent outcomes (every fork below is a
-- partition), so a consumer may guard each value independently and sum.
-- Values are IR expressions, usually constants; arithmetic combines them
-- unfolded (constant folding is left to the optimizer). The result is passed
-- through the milestone-4 value DP ('planGroupValues') so same-value worlds
-- collapse at every level -- without it counting folds are 2^depth.
planEnumValues :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(IRExpr, PlanWorld)])
planEnumValues meta env body = do
  r <- planEnumValuesRaw meta env body
  case r of
    Left why    -> return (Left why)
    Right pairs -> Right <$> planGroupValues pairs

planEnumValuesRaw :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String [(IRExpr, PlanWorld)])
planEnumValuesRaw meta env body
  | not (subtreeHasOcc occs body) =
      if pType (getTypeInfo body) == Deterministic
        then do
          ir <- planGenDet meta env body
          return (Right [(ir, pw1 [])])
        else return (Left ("a subtree independent of the plan-bound variables draws fresh randomness: " ++ planNodeName body))
  | Just refE <- planEvalRef meta env body = return $ case refE of
      Left why -> Left why
      Right (PlanRef (Discretes _ (MultiDiscretes vals)) off, cons) ->
        Right [ (IRConst (valueToIR v), pw1 (insertLeafCon (PLeafCon off [(i, constTrueIR)]) cons))
              | (i, v) <- zip [0..] vals ]
      Right _ -> Left "value enumeration is only supported for enum plan leaves"
  | otherwise = case body of
      IfThenElse _ c t e
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
                vsT <- if null cts then return (Right []) else planEnumValues meta env t
                vsE <- if null cfs then return (Right []) else planEnumValues meta env e
                return $ do
                  ts <- vsT
                  es <- vsE
                  return (livePairs [ (v, intersectPlanW cw w) | cw <- cts, (v, w) <- ts ]
                       ++ livePairs [ (v, intersectPlanW cw w) | cw <- cfs, (v, w) <- es ])
        | otherwise -> return (Left "an if condition independent of the plan-bound variables draws fresh randomness")
      InjF _ (Named nm) [a, b] | Just op <- arithOp nm -> do
        vsA <- planEnumValues meta env a
        vsB <- planEnumValues meta env b
        return ((\as bs -> livePairs [ (IROp op va vb, intersectPlanW wa wb) | (va, wa) <- as, (vb, wb) <- bs ]) <$> vsA <*> vsB)
      Apply {} -> do
        specE <- planResolveApply meta env body
        case specE of
          Left why -> return (Left why)
          Right spec
            | rType (getTypeInfo body) == TBool -> do
                r <- planSpecializeBool spec
                return ((\(tw, fw) -> [ (constTrueIR, addSpecCons spec w)          | w <- tw ]
                                   ++ [ (IRConst (VBool False), addSpecCons spec w) | w <- fw ]) <$> r)
            | otherwise -> do
                r <- planSpecializeEnum spec
                return ((\pairs -> [ (v, addSpecCons spec w) | (v, w) <- pairs ]) <$> r)
      _ -> return (Left ("unsupported node in plan value enumeration: " ++ planNodeName body))
  where
    occs = planEnvOccs env
    arithOp n = lookup n [("plus", OpPlus), ("mult", OpMult)]
    livePairs = filter (not . pwUnsat . snd)

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
addSpecCons spec w = w { pwCons = foldr insertLeafCon (pwCons w) (spCons spec) }

-- | Resolve a user-function application into a specialization: the callee
-- must be a directly-applied (saturated) top-level function, and each
-- argument either an accessor chain into the plan (bound 'PBPlan') or
-- deterministic given scope (generated at the call site, bound 'PBDet').
planResolveApply :: CompilerMetadata -> PlanEnv -> Expr -> PlanM (Either String PlanSpec)
planResolveApply meta env body = case collectApply body [] of
  Nothing -> return (Left ("unsupported callee in plan traversal (only directly-applied top-level functions can be specialized): " ++ planNodeName body))
  Just (fname, args) -> case lookup fname (functions (compilingProgram meta)) of
    Nothing -> return (Left ("call to '" ++ fname ++ "': not a top-level function (higher-order callees are not specializable)"))
    Just decl -> do
      let (params, calleeBody) = unwrapCalleeLambdas decl
      if length params /= length args
        then return (Left ("call to '" ++ fname ++ "': partial application is not specializable (expected "
                           ++ show (length params) ++ " arguments, got " ++ show (length args) ++ ")"))
        else do
          classesE <- mapM classifyArg args
          case sequence classesE of
            Left why -> return (Left why)
            Right classes -> do
              frame <- lift (mapM bindParam (zip params classes))
              let planOffs = [ off | ArgPlan (PlanRef _ off) _ <- classes ]
              let detKeys  = [ show ir | ArgDet ir <- classes ]
              let key = (chainName (getTypeInfo calleeBody), planOffs, detKeys)
              let callCons = concat [ cons | ArgPlan _ cons <- classes ]
              let meta' = foldl (\m (pname, pti, _) -> extendMetaForLambda m pti pname) meta params
              return (Right (PlanSpec frame calleeBody key (sum planOffs) callCons meta'))
  where
    collectApply (Apply _ f a) acc = collectApply f (a : acc)
    collectApply v@(Var _ n) acc
      -- a callee bound in the traversal env is a higher-order parameter, not
      -- a top-level function of the same name
      | isJust (planEnvLookup env (chainName (getTypeInfo v))) = Nothing
      | otherwise = Just (n, acc)
    collectApply _ _ = Nothing
    unwrapCalleeLambdas (Lambda ti n sub) =
      let (ps, b) = unwrapCalleeLambdas sub in ((n, ti, chainName ti) : ps, b)
    unwrapCalleeLambdas e = ([], e)
    classifyArg argE
      | Just refE <- planEvalRef meta env argE = return (fmap (uncurry ArgPlan) refE)
      | not (subtreeHasOcc (planEnvOccs env) argE) && pType (getTypeInfo argE) == Deterministic =
          Right . ArgDet <$> planGenDet meta env argE
      | otherwise = return (Left ("call argument is neither a plan slice (accessor chain) nor deterministic given scope: " ++ planNodeName argE))
    -- Bind a non-trivial det argument to a fresh variable once; constants and
    -- variables pass through (also keeps memo keys small and collision-free).
    bindParam ((pname, _, pcn), cls) = case cls of
      ArgPlan ref _ -> return (occsOf pcn, PBPlan ref)
      ArgDet ir -> do
        v <- case ir of
          IRConst _ -> return ir
          IRVar _   -> return ir
          _ -> do
            nm <- mkVariable "spec_arg"
            setVariables [(nm, ir)]
            return (IRVar nm)
        return (occsOf pcn, PBDet pname v)
    occsOf cn = fromMaybe [] (lookup cn (lambdaVarOccurrences (fcData meta)))

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
  if any (\(cn, d) -> cn == bodyCN && d >= spDepth spec) (psStack st)
    then return (Left ("recursive specialization of the function at " ++ bodyCN
                       ++ " does not strictly descend the plan (non-terminating recursion shape)"))
    else do
      put st { psStack = (bodyCN, spDepth spec) : psStack st }
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
        Right tf -> do
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
          modify (\s -> s { psEnumMemo = Map.insert (spKey spec) pairs (psEnumMemo s) })
          return (Right pairs)

-- | Observation target applied to a user-function application (milestone 2):
-- specialize the callee at its arguments and match its outcome against the
-- target. Bool results go through the canonical two-polarity specialization
-- (so both polarities share one memo entry); anything else through value
-- enumeration.
planApplyTarget :: CompilerMetadata -> PlanEnv -> Expr -> PTarget -> PlanM (Either String [PlanWorld])
planApplyTarget meta env body target = do
  specE <- planResolveApply meta env body
  case specE of
    Left why -> return (Left why)
    Right spec -> case rType (getTypeInfo body) of
      TBool -> do
        r <- planSpecializeBool spec
        return ((\(tw, fw) -> map (addSpecCons spec) (planBoolWorlds target tw fw)) <$> r)
      rt -> do
        r <- planSpecializeEnum spec
        return ((\pairs -> [ addSpecCons spec (planAddGuard (planDetGuard rt v target) w) | (v, w) <- pairs ]) <$> r)

-- | Measure the worlds against the raw logit vector bound at @nnRaw@:
-- p = sum over worlds of (guards -> product of constrained leaf masses),
-- where a discrete leaf's mass is the sum of its allowed slots' logits (each
-- under its own guard), an interval-constrained continuous leaf's is a
-- Gaussian CDF difference over its (mu, sigma) slice, a pairwise coupling's
-- is the closed-form difference Gaussian, and a point-constrained continuous
-- leaf's is its density times |change-of-variables| -- the only dim-1
-- measure. When every world is dim 0 (in particular for any milestone-1/2
-- world set) the worlds sum directly; with point constraints present the
-- worlds combine via 'addP' (mixture addition, smaller dimension wins). Each
-- world whose guards hold counts as one branch.
measurePlanWorlds :: String -> [PlanWorld] -> CompilerMonad CompilationResult
measurePlanWorlds nnRaw worlds
  | all ((== 0) . planWorldDim) worlds =
      return (sumUp (map mass worlds), const0, sumUp (map branch worlds))
  | otherwise = case map (\w -> ((mass w, dimC (planWorldDim w)), branch w)) worlds of
      []     -> return (const0, const0, const0)
      (m:ms) -> do
        (pS, dS) <- foldM addP (fst m) (map fst ms)
        return (pS, dS, sumUp (map snd (m:ms)))
  where
    dimC d = IRConst (VFloat (fromIntegral d))
    sumUp [] = const0
    sumUp xs = foldr1 (IROp OpPlus) xs
    mass = planWorldMass nnRaw
    branch w = foldr (\g acc -> IRIf g acc const0) const1 (pwGuards w)

-- | Dimensionality of a world's mass: one per point constraint (a univariate
-- density); discrete slots, CDF intervals, pairwise couplings and the carried
-- mass factor are all dim 0.
planWorldDim :: PlanWorld -> Int
planWorldDim w = length [ () | PLeafPt {} <- pwCons w ]

-- | The mass a world contributes: (guards -> the carried factor times the
-- product of constrained leaf masses), read from the raw logit vector bound at
-- @nnRaw@. A discrete leaf's mass is the sum of its allowed slots' logits (each
-- under its own guard), an interval-constrained continuous leaf's is a Gaussian
-- CDF difference over its (mu, sigma) slice, a pairwise coupling's is the
-- closed-form difference Gaussian, and a point-constrained continuous leaf's is
-- its density times |change-of-variables| (the only dim-1 measure). Shared
-- between 'measurePlanWorlds' and the milestone-4 value grouping so a collapsed
-- group's factor measures exactly as the worlds it replaced.
planWorldMass :: String -> PlanWorld -> IRExpr
planWorldMass nnRaw (PlanWorld guards cons pairs factor) =
    foldr (\g acc -> IRIf g acc const0) (mulFactor factor (prodMass cons pairs)) guards
  where
    prodMass []  []  = const1
    prodMass cs prs = foldr1 (IROp OpMult) (map leafMass cs ++ map pairMass prs)
    leafMass (PLeafCon _ [])       = const0
    leafMass (PLeafCon base slots) = foldr1 (IROp OpPlus) (map (slotRead base) slots)
    leafMass (PLeafIvl base lo hi) =
      let diff = IROp OpSub (cdfAt base hi) (cdfAt base lo)
      in case (lo, hi) of
           -- one-sided intervals cannot go negative; only a runtime-empty
           -- two-sided intersection needs the clamp (mirrors measureSet)
           (WFinite _, WFinite _) -> IRIf (IROp OpGreaterThan diff const0) diff const0
           _                      -> diff
    leafMass (PLeafPt base v cov gs) =
      let dens = IROp OpDiv (IRDensity IRNormal (zScore base v)) (vecRead (base + 1))
          scaled = if cov == const1 then dens else IROp OpMult dens (IRUnaryOp OpAbs cov)
      in foldr (\g acc -> IRIf g acc const0) scaled gs
    -- P(leaf@a > leaf@b) for independent Gaussians: Phi((mu_a - mu_b) / sqrt(s_a^2 + s_b^2))
    pairMass (a, b) =
      let num = IROp OpSub (vecRead a) (vecRead b)
          sq x = IROp OpMult x x
          var = IROp OpPlus (sq (vecRead (a + 1))) (sq (vecRead (b + 1)))
          -- sqrt spelled as exp(log/2): the IR has no sqrt primitive
          sd = IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog var))
      in IRCumulative IRNormal (IROp OpDiv num sd)
    cdfAt _ WNegInf = const0
    cdfAt _ WPosInf = const1
    cdfAt base (WFinite e) = IRCumulative IRNormal (zScore base e)
    zScore base e = IROp OpDiv (IROp OpSub e (vecRead base)) (vecRead (base + 1))
    slotRead base (i, g)
      | g == constTrueIR = vecRead (base + i)
      | otherwise        = IRIf g (vecRead (base + i)) const0
    vecRead k = IRIndex (IRVar nnRaw) (IRConst (VInt k))

-- | Entry point of the plan-guided dispatch, tried from the probabilistic
-- Apply arm after point inversion failed and before the set-witness fallback.
-- Right: the compiled result. Left Nothing: not applicable (the argument is
-- not a plan-backed ReadNN, or the application shape is out of scope). Left
-- (Just why): applicable, but the body traversal hit an unsupported node --
-- the diagnostic is appended to the set-witness refusal.
planWitnessApply :: CompilerMetadata -> Bool -> RType -> ChainName -> ChainName -> String -> Expr -> IRExpr -> CompilerMonad (Either (Maybe String) CompilationResult)
planWitnessApply meta cumulative rt lResolvedCN lambdaBodyCN tag v sample
  | tag == ""
  , not (isArrow rt)
  , ReadNN _ nnName symArg <- v
  , Just (_, TArrow TSymbol targetTy, declTag) <- find (\(n, _, _) -> n == nnName) (neurals (compilingProgram meta))
  , let resolved = resolvePartitionAnnotation (encodeDecls (compilingProgram meta)) targetTy declTag
  , isJust resolved || isRight (autoDeriveMultiValue (adtDecls meta) targetTy)
  = do
      let plan = makePartitionPlan (adtDecls meta) targetTy resolved
      let Program{functions=fs} = compilingProgram meta
      let bodyExpr = findExprWithCN (map snd fs) lambdaBodyCN
      let occs = fromMaybe [] (lookup lResolvedCN (lambdaVarOccurrences (fcData meta)))
      let env = [(occs, PBPlan (PlanRef plan 0))]
      let target = if cumulative then PTUpTo sample else PTPoint sample
      -- Bind the raw logit vector up front: the milestone-4 value grouping
      -- measures collapsed worlds during the traversal, so it needs the name.
      nnRaw <- mkVariable "nn_raw"
      sym <- toIRGenerate meta symArg
      setVariables [(nnRaw, IRApply (IRVar nnName) sym)]
      -- The milestone-4 value grouping may collapse same-count worlds only when
      -- the fold is the scene's sole reader: with a single occurrence its leaves
      -- are private, so baking them into a summed mass cannot clash with a
      -- sibling predicate re-constraining the shared structural flags.
      let mayMerge = length occs <= 1
      worldsE <- evalStateT (planInvert meta env bodyExpr target) (emptyPlanState nnRaw mayMerge)
      case worldsE of
        Left why -> return (Left (Just why))
        Right worlds0 -> do
          -- statically unsatisfiable worlds measure 0; drop them
          let worlds = filter (not . pwUnsat) worlds0
          case mapMaybe pwOverCoupled worlds of
           (why:_) -> return (Left (Just why))
           [] -> do
            (p, dim, bc) <- measurePlanWorlds nnRaw worlds
            -- Full-ANY marginal short-circuit, mirroring setWitnessApply.
            if cumulative
              then return (Right (p, dim, bc))
              else return (Right ( IRIf (IRUnaryOp OpIsAny sample) const1 p
                                 , IRIf (IRUnaryOp OpIsAny sample) const0 dim
                                 , IRIf (IRUnaryOp OpIsAny sample) const1 bc ))
  | otherwise = return (Left Nothing)
  where
    isArrow (TArrow _ _) = True
    isArrow _            = False
