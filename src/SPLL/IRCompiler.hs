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
import Data.List (isPrefixOf, (\\))
import Data.Char (isDigit)
import Data.Functor ((<&>))
import Control.Monad.Writer.Lazy
import SPLL.AutoNeural
import SPLL.Typing.ForwardChaining
import SPLL.Typing.AlgebraicDataTypes
import Data.Bifunctor (Bifunctor(bimap))
import Utils
import Control.Monad (foldM, forM, when)
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
        baseFunGroup = IRFunGroup {groupName=name, encodeFun=encodeF,
         integFun =
          if not noInteg && (pt == Deterministic || pt == Integrate || pt == PNormal || pt == PLogNormal) then
            Just (toIntegDecl name (IRLambda "sample" (runCompile (meta typeEnv) (toIRInferenceSave (meta typeEnv) True binding (IRVar "sample")))))
          else Nothing,
          probFun =
            if not noProb && (pt == Deterministic || pt == Integrate || pt == PNormal || pt == PLogNormal) then
              let metaBase = meta typeEnv
                  body m = runCompile m (toIRInferenceSave m False binding (IRVar "sample"))
              in Just (toProbDecl name $ case topKThreshold conf of
                   Just _ -> IRLambda "sample" $ IRLambda "acc_prob" $ body (metaBase { accProb = IRVar "acc_prob" })
                   Nothing -> IRLambda "sample" $ body metaBase)
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
  else case toInvExprMaybe clauses adts lChainName of
   -- No occurrence of the bound variable is point-invertible from the
   -- observation. Fall back to set-valued witnesses: invert the observation
   -- structurally into guarded constraint sets on the bound variable (intervals
   -- from comparisons, case splits from ifs, intersections across occurrences)
   -- and measure them against the bound distribution (design
   -- set-valued-witnesses).
   Nothing -> setWitnessApply meta cumulative rt l lResolvedCN lambdaBodyCN tag v sample
   Just (invExprP0, invExprCoV0) -> do
    invExprP   <- pruneDeadLetIns <$> materializeAnchors meta invExprP0
    invExprCoV <- pruneDeadLetIns <$> materializeAnchors meta invExprCoV0
    let appliedCoV = IRApply (IRLambda (boundVar ++ tag) invExprCoV) sample
    let lInv = IRLambda (boundVar ++ tag) invExprP
    -- Apply the sample to the inverse
    let appliedSample = IRApply lInv sample
    -- Do probabilistic inference using the applied inverse
    (p, dim, bc) <- toIRInference meta cumulative v appliedSample

    let scale x = if not cumulative
                    then IROp OpMult x (IRIf (IROp OpEq dim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs appliedCoV))
                    else IRIf (IROp OpGreaterThan appliedCoV const0) x (IROp OpSub (IRConst (VFloat 1)) x)
    case rt of
      TArrow _ _ -> return (wrapInLambdas (IRTCons (scale p) (IRTCons dim bc)), const0, const0)
      _ | cumulative || not (isLambdaExpr l) || not (null tag) ->
            -- Keep the original single-witness behaviour when: (a) integrate mode, where
            -- tuple/multi-latent CDFs are ill-defined; (b) the callable is not a literal
            -- lambda, i.e. it is a function reached through the higher-order equivalence
            -- machinery (applied top-level fn / returned closure), whose body references
            -- tagged variables this folding would mis-bind; or (c) the lambda is applied
            -- under a tag (HO duplication). Body-factor folding is only sound for a plain
            -- value let-binding `Apply (Lambda x body) v`.
            return (wrapInLambdas $ scale p, wrapInLambdas dim, wrapInLambdas bc)
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
        return ( wrapInLambdas (guardAny combP pBody)
               , wrapInLambdas (guardAny combDim dimBody)
               , wrapInLambdas (guardAny combBC bcBody) )
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
  return (IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
           (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
           (IROp OpPlus (IRVar pVarA) (IRVar pVarB))))),
           -- Dim
           IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
           (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
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
  let (inverseF0, inverseCoV0) = toInvExpr fcData' adts (chainName $ getTypeInfo f)
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

    -- Collapse (prob, (dim, _)) → (prob, dim) peeling through IRLambda/IRLetIn wrappers.
    stripOuterTriple (IRLambda n body)         = IRLambda n (stripOuterTriple body)
    stripOuterTriple (IRLetIn n v body)        = IRLetIn n v (stripOuterTriple body)
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

-- Two constraints on the SAME draw. Point-point takes the first: both compute
-- the same value from the same observation (the mergeExpr convention).
intersectSet :: WSet -> WSet -> ([IRExpr], WSet)
intersectSet WFull s = ([], s)
intersectSet s WFull = ([], s)
intersectSet WEmpty _ = ([], WEmpty)
intersectSet _ WEmpty = ([], WEmpty)
intersectSet (WPoint p c) (WPoint _ _) = ([], WPoint p c)
intersectSet (WPoint p c) (WInterval lo hi) = (boundGuards p lo hi, WPoint p c)
intersectSet (WInterval lo hi) (WPoint p c) = (boundGuards p lo hi, WPoint p c)
intersectSet (WInterval lo1 hi1) (WInterval lo2 hi2) =
  ([], WInterval (maxWBound lo1 lo2) (minWBound hi1 hi2))

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
setWitnessApply :: CompilerMetadata -> Bool -> RType -> Expr -> ChainName -> ChainName -> String -> Expr -> IRExpr -> CompilerMonad CompilationResult
setWitnessApply meta cumulative rt l lResolvedCN lambdaBodyCN tag v sample = do
  let userVar = case l of Lambda _ n _ -> n; _ -> "<bound variable>"
  let refuse why = error $ unlines
        [ "set-valued witness construction failed for the binding of '" ++ userVar ++ "' (lambda at " ++ lResolvedCN ++ "):"
        , why
        , "No occurrence of the bound variable is point-invertible either (forward"
        , "chaining found no inversion path). See design set-valued-witnesses." ]
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
      Just (g0, cov0) -> do
        g   <- pruneDeadLetIns <$> materializeAnchors meta g0
        cov <- pruneDeadLetIns <$> materializeAnchors meta cov0
        let applyTo e arg = IRApply (IRLambda bodyCN e) arg
        return (Just [WWorld [] (WPoint (applyTo g s) (IROp OpMult c0 (applyTo cov s)))])
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
