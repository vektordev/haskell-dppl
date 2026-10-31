-- | The Normal engines: normal parameters ('toIRNormal'), moments, affine
-- forms over marginalised variables, the joint affine Gaussian, log-normal
-- parameters, and the Gaussian-law dispatch on the codegen law.
module SPLL.IRCompiler.Gaussian (
  isNormalExtractable,
  toIRNormal,
  readNNSlotNormal,
  momentsOf,
  affineFormOf,
  isRecursiveFunction,
  affineMarginalisable,
  jointAffineApplicable,
  jointAffineApply,
  normalDiffComparison,
  toIRLogNormalParams,
  gaussianLeaf,
  gaussianParams,
  logNormalExtractable,
  degenerateScaleGuard
) where

import SPLL.IntermediateRepresentation
import SPLL.IRUtil
import SPLL.IRCompiler.Affine
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Typing.PType
import Data.Maybe
import Data.List (nub, intercalate, sort, partition)
import SPLL.Typing.ModalityInfer (reinferLawGiven, Law, AffineCert(..), affineOf)
import qualified SPLL.Typing.ModalityInfer as ModalityInfer
import SPLL.Semiring
import Control.Monad (foldM, forM, (>=>))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph (SCC(..), stronglyConnComp)
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Binding

-- | Whether a declaration (with its parameter lambdas stripped) gets a normal
-- function ('normalE', 'generateComponentNormalFunction'): a body
-- 'toIRNormal' reads a (mu, sigma) off, which a @draw@, a call, a
-- conditional or a constructor is not. A call of such a declaration is a
-- pure callee of the caller's inference ('normalParamsViaCall').
isNormalExtractable :: Expr -> Bool
isNormalExtractable (Expr _ (Lambda _ lambdaBody))            = isNormalExtractable lambdaBody
isNormalExtractable (Expr _ (Apply  _ _))               = False
isNormalExtractable (Expr _ (IfThenElse _ _ _))         = False
isNormalExtractable (Expr _ (InjF (Named "Cons")  _))   = False
isNormalExtractable (Expr _ (InjF (Named "TCons") _))   = False
isNormalExtractable _                            = True

-- | The affine form of a marginalised variable ('bvForm').
affineFormOfVar :: CompilerMetadata -> String -> Maybe AffineForm
affineFormOfVar meta x = Map.lookup x (lawEnv meta) >>= bvForm

-- | The variables marginalised as affine forms ('bvForm').
affineVars :: CompilerMetadata -> Set.Set String
affineVars meta = Map.keysSet (Map.filter (isJust . bvForm) (lawEnv meta))

-- | Dispatch to the appropriate param extractor based on PType.
-- Returns (mu, sigma) for PNormal and (mu_log, sigma) for PLogNormal.
toIRNormal :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
toIRNormal meta e
  | pType (getTypeInfo e) == PNormal    = toIRNormalParams meta e
  | pType (getTypeInfo e) == PLogNormal = toIRLogNormalParams meta e
  -- Invariant, not a refusal (task static-refusals-become-absent-variants): callers check the pType first.
  | otherwise = error $ "toIRNormal: expression is neither PNormal nor PLogNormal: " ++ show (pType (getTypeInfo e))

-- | @sqrt(a*a + b*b)@, the scale of a sum of two independent Gaussians.
--
-- Each operand is read twice, so an operand that is itself a sum's scale is
-- let-bound first rather than copied: written inline, a K-term nested sum's
-- scale is a tree of 2^K nodes (linear only through Haskell's sharing, which
-- every IR pass ignores), and the optimizer spends exponential time folding it
-- back together (task chained-gaussian-trajectory-compile-exponential). Only a
-- nested 'irSqrt' is bound: every other scale (a constant, or a product with a
-- deterministic factor) is a bounded expression whose duplication costs a
-- constant, and binding it would only move emitted code around.
irHypot :: IRExpr -> IRExpr -> CompilerMonad IRExpr
irHypot a b = do
  a' <- shareScale a
  b' <- shareScale b
  return (irSqrt (IROp OpPlus (IROp OpMult a' a') (IROp OpMult b' b')))
  where
    shareScale s
      | containsSqrt s = do
          v <- mkVariable "sigma"
          setVariables [(v, s)]
          return (IRVar v)
      | otherwise = return s
    containsSqrt (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog _))) = True
    containsSqrt x = any containsSqrt (getIRSubExprs x)

-- | Recursively extract (mu, sigma) as IRExprs from a PNormal-typed expression.
-- | (mu, sigma) of the Continuous slot at logit offset @k@ of a network read.
readNNSlotNormal :: CompilerMetadata -> Int -> Expr -> CompilerMonad (IRExpr, IRExpr)
readNNSlotNormal meta k (Expr _ (ReadNN name arg)) = do
  sym <- toIRGenerate meta arg
  var <- mkVariable "nn_out"
  setVariables [(var, IRApply (IRVar name) sym)]
  return (IRBuiltin BListIndex [IRVar var, IRConst (VInt k)], IRBuiltin BListIndex [IRVar var, IRConst (VInt (k + 1))])
readNNSlotNormal _ _ e = error ("readNNSlotNormal: not a network read: " ++ show e)

toIRNormalParams :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
-- 'collapse' is the Gaussian of its operand's moments. First: it is a fresh
-- leaf whatever its operand reads, so it never takes the affine equation.
toIRNormalParams meta (Expr _ (InjF (Named n) [a])) | isCollapse n = momentsOf meta a
-- An expression reading an analytically marginalised binding is collapsed from
-- its affine form. Tried first: the scalar equations below combine their
-- operands as independent, which is exactly wrong for two operands sharing a
-- latent through that binding. Expressions that read no such binding never
-- take this equation, so their emitted code is unchanged.
toIRNormalParams meta e | mentionsAffineVar meta e = collapseAffine <$> affineFormOf meta e
toIRNormalParams _ (Expr _ (Var "Normal")) = return (IRConst (VFloat 0), IRConst (VFloat 1))
toIRNormalParams meta (Expr _ (InjF (Named "plus") [e0, e1]))
  | pType (getTypeInfo e0) == PNormal, pType (getTypeInfo e1) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      (mu1, s1) <- toIRNormalParams meta e1
      sigma <- irHypot s0 s1
      return (IROp OpPlus mu0 mu1, sigma)
toIRNormalParams meta (Expr _ (InjF (Named "plus") [e0, e1]))
  | pType (getTypeInfo e0) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpPlus mu0 det1, s0)
toIRNormalParams meta (Expr _ (InjF (Named "plus") [e0, e1]))
  | pType (getTypeInfo e1) == PNormal = do
      (mu1, s1) <- toIRNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpPlus mu1 det0, s1)
toIRNormalParams meta (Expr _ (InjF (Named "mult") [e0, e1]))
  | pType (getTypeInfo e0) == PNormal = do
      (mu0, s0) <- toIRNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpMult mu0 det1, IROp OpMult s0 (IRUnaryOp OpAbs det1))
toIRNormalParams meta (Expr _ (InjF (Named "mult") [e0, e1]))
  | pType (getTypeInfo e1) == PNormal = do
      (mu1, s1) <- toIRNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpMult mu1 det0, IROp OpMult s1 (IRUnaryOp OpAbs det0))
toIRNormalParams meta (Expr _ (InjF (Named "neg") [e]))
  | pType (getTypeInfo e) == PNormal = do
      (mu, s) <- toIRNormalParams meta e
      return (IRUnaryOp OpNeg mu, s)
toIRNormalParams meta (Expr _ (InjF (Named "log") [e]))
  | pType (getTypeInfo e) == PLogNormal = toIRLogNormalParams meta e
-- Tuple-field projection: the marginal of a literal tuple's field is that
-- field's own law, so extraction descends into the projected component. The
-- modality engine's IProd projection types e.g. @fst (Normal, Uniform * 2)@ as
-- PNormal, a shape PInfer2 never produced.
toIRNormalParams meta (Expr _ (InjF (Named "fst") [Expr _ (InjF (Named "TCons") [a, _])]))
  | pType (getTypeInfo a) == PNormal = toIRNormalParams meta a
toIRNormalParams meta (Expr _ (InjF (Named "snd") [Expr _ (InjF (Named "TCons") [_, b])]))
  | pType (getTypeInfo b) == PNormal = toIRNormalParams meta b
toIRNormalParams meta (Expr ti (InjF f@(Named n) [Expr _ (Var name)]))
  | n `elem` ["fst", "snd"]
  , Just expr <- lookup name (functions (compilingProgram meta)) =
      toIRNormalParams meta (Expr ti (InjF f [expr]))
toIRNormalParams meta (Expr _ (Var name))
  | Just expr <- lookup name (functions (compilingProgram meta)) = toIRNormalParams meta expr
toIRNormalParams meta e@(Expr _ (ReadNN _ _)) = readNNSlotNormal meta 0 e
toIRNormalParams meta e | Just act <- normalParamsViaCall meta PNormal e = act
toIRNormalParams _ e = refuse (chainName (getTypeInfo e)) $ "toIRNormalParams: cannot extract Normal params from " ++ show (pType (getTypeInfo e)) ++ " | expr: " ++ show e

-- | The mean and standard deviation of a 'collapse' operand's law, over its
-- own draws and given the values of the variables it reads (task
-- encode-07-collapse-operator). The dynamic twin of
-- 'ModalityInfer.collapseMomentable', which decides the collapse node's type;
-- a shape that answers no here is refused. A mixture @if c then a else b@ is
-- moment-matched:
--
-- > mu     = p mu_a + (1-p) mu_b
-- > sigma² = p (sigma_a² + (mu_a - mu)²) + (1-p) (sigma_b² + (mu_b - mu)²)
--
-- and sums and products of independent parts combine their moments. Only the
-- sum-product semiring has expectations to take.
momentsOf :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
momentsOf meta e@(Expr ti nd)
  | semiringFamily meta /= SRSumProduct = refuse cn "collapse: moment matching needs the sum-product semiring"
  | mentionsAffineVar meta e =
      refuse cn "collapse: the operand reads a marginalised random binding, so it has no moments given its variables"
  | ModalityInfer.collapsePoint isTop e = do
      v <- toIRGenerate meta e
      return (v, IRConst (VFloat 0))
  | IfThenElse c a b <- nd, ModalityInfer.collapseMomentable isTop e = do
      let sr = semiringOf meta
      -- The condition's False weight is its True weight's complement in the
      -- semiring's sense, compiled unpruned, exactly as the IfThenElse
      -- inference equation takes it; a True outcome that is a density (a null
      -- event, dim > 0) has mass zero.
      condTrue <- toIRInference (unpruned meta) False c (IRConst (VBool True))
      condFalse <- mixWith (\_ p -> srComplement sr p) const0 (mass (srOne sr)) condTrue
      let weight r = IRIf (IROp OpEq (rDim r) (IRConst (VInt 0))) (toLinearSR sr (unP (rProb r))) (IRConst (VFloat 0))
      pT <- bind "collapse_pT" (weight condTrue)
      pF <- bind "collapse_pF" (weight condFalse)
      (muA, sA) <- momentsOf meta a >>= bindPair
      (muB, sB) <- momentsOf meta b >>= bindPair
      mu <- bind "collapse_mu" (IROp OpPlus (IROp OpMult pT muA) (IROp OpMult pF muB))
      let armVar m s = IROp OpPlus (sq s) (sq (IROp OpSub m mu))
      return (mu, irSqrt (IROp OpPlus (IROp OpMult pT (armVar muA sA)) (IROp OpMult pF (armVar muB sB))))
  | InjF (Named "plus") [a, b] <- nd, ModalityInfer.collapseMomentable isTop e = do
      (muA, sA) <- momentsOf meta a
      (muB, sB) <- momentsOf meta b
      sigma <- irHypot sA sB
      return (IROp OpPlus muA muB, sigma)
  | InjF (Named "mult") [a, b] <- nd, ModalityInfer.collapseMomentable isTop e = do
      -- Independent factors: E[ab] = mu_a mu_b and
      -- Var[ab] = (sigma_a² + mu_a²)(sigma_b² + mu_b²) - mu_a² mu_b².
      (muA, sA) <- momentsOf meta a >>= bindPair
      (muB, sB) <- momentsOf meta b >>= bindPair
      let second m s = IROp OpPlus (sq s) (sq m)
          var = IROp OpSub (IROp OpMult (second muA sA) (second muB sB)) (sq (IROp OpMult muA muB))
      -- Rounding can take the difference a hair below zero, where the square
      -- root would be NaN.
      return (IROp OpMult muA muB, irSqrt (IROp OpMax var (IRConst (VFloat 0))))
  | InjF (Named "neg") [a] <- nd, ModalityInfer.collapseMomentable isTop e = do
      (mu, s) <- momentsOf meta a
      return (IRUnaryOp OpNeg mu, s)
  | pType ti == PNormal = toIRNormalParams meta e
  | otherwise = refuse cn ("collapse: cannot read the mean and variance of " ++ show (pType ti) ++ " operand " ++ show e
                           ++ " (a Gaussian, a point, an if-mixture of such with a condition that has a probability, or sums, products and negations of independent such parts)")
  where
    cn = chainName ti
    isTop v = isJust (lookup v (functions (compilingProgram meta)))
    sq x = IROp OpMult x x
    bind tag x = do
      v <- mkVariable tag
      setVariables [(v, x)]
      return (IRVar v)
    bindPair (m, s) = (,) <$> bind "collapse_m" m <*> bind "collapse_s" s

-- | True if the expression reads a variable marginalised as an affine form
-- ('affineVars').
mentionsAffineVar :: CompilerMetadata -> Expr -> Bool
mentionsAffineVar meta e = not (Set.disjoint (freeVarsExpr e) (affineVars meta))

-- | The affine form of a node whose law is an affine form ('gaussianLeaf'),
-- or that 'isAffineOver' accepts: the builder of the affine certificate
-- (design affine-gaussian-forms §3, law-carrying-modality M4). The
-- certificate's rules are the ones here: a constant (Deterministic, reading
-- no marginalised variable, 'isAffineConstant'); a sum, a product with a
-- constant, a negation; a projected tuple field (the field's own form, as
-- 'ModalityInfer.projectedLaw' certifies it); a variable marginalised as a
-- form ('affineFormOfVar'); and a leaf. The certificate sees a Gaussian no
-- rule looks into as one fresh latent ('ModalityInfer.affineOf'), and the
-- builder realises each such leaf: a call and a lambda redex (a @draw@, a
-- @let@) are entered as the bindings they are ('affineCallForm'), so a
-- latent drawn inside a callee is keyed by the call site and a parameter
-- bound to an argument's form reads that form; a @collapse@ is a fresh
-- leaf whatever its operand reads; and a primitive, a neural read or any
-- other Gaussian reading no marginalised variable is answered by the scalar
-- extractor ('toIRNormalParams') and enters as one latent keyed by its own
-- chain name. A shape outside these is refused: the certificate was issued
-- over the program as written and cannot promise what the builder meets
-- inside a callee entered at a call site.
affineFormOf :: CompilerMetadata -> Expr -> CompilerMonad AffineForm
affineFormOf meta e@(Expr ti nd)
  | isAffineConstant meta e = do
      c <- toIRGenerate meta e
      return (AffineForm c Map.empty)
  | Just (pas, calleeBody) <- affineCall meta e = affineCallForm meta (chainName ti) pas calleeBody
  | Apply (Expr _ (Lambda p b)) a <- nd = affineCallForm meta (chainName ti) [(p, a)] b
  | Var n <- nd, Just form <- affineFormOfVar meta n = return form
  | InjF (Named n) [_] <- nd, isCollapse n = leaf
  | InjF (Named "plus") [a, b] <- nd = do
      fa <- affineFormOf meta a
      fb <- affineFormOf meta b
      return (AffineForm (IROp OpPlus (afConst fa) (afConst fb))
                         (Map.unionWith (IROp OpPlus) (afCoeffs fa) (afCoeffs fb)))
  | InjF (Named "mult") [a, b] <- nd, isAffineConstant meta a = scaleBy a b
  | InjF (Named "mult") [a, b] <- nd, isAffineConstant meta b = scaleBy b a
  | InjF (Named "neg") [a] <- nd = do
      fa <- affineFormOf meta a
      return (AffineForm (IRUnaryOp OpNeg (afConst fa)) (Map.map (IRUnaryOp OpNeg) (afCoeffs fa)))
  | InjF (Named "fst") [Expr _ (InjF (Named "TCons") [a, _])] <- nd = affineFormOf meta a
  | InjF (Named "snd") [Expr _ (InjF (Named "TCons") [_, b])] <- nd = affineFormOf meta b
  | not (mentionsAffineVar meta e), pType ti == PNormal = leaf
  | otherwise = refuse (chainName ti) ("affineFormOf: not an affine Gaussian form: " ++ show e)
  where
    leaf = do
      (mu, s) <- toIRNormalParams meta e
      return (AffineForm mu (Map.singleton (chainName ti) s))
    scaleBy c f = do
      cIR <- toIRGenerate meta c
      ff <- affineFormOf meta f
      return (AffineForm (IROp OpMult (afConst ff) cIR) (Map.map (\a -> IROp OpMult a cIR) (afCoeffs ff)))

-- | A subterm the affine algebra treats as a constant: Deterministic, and
-- reading no marginalised binding.
isAffineConstant :: CompilerMetadata -> Expr -> Bool
isAffineConstant meta e = pType (getTypeInfo e) == Deterministic && not (mentionsAffineVar meta e)

-- | @isAffineOver meta names e@: 'affineFormOf' can build a form for @e@ once
-- every name in @names@ is marginalised ('affineVars'): the affine engines'
-- applicability check ('affineMarginalisable', 'jointAffineApplicable'),
-- the static twin of that function. A subterm reading none of the names is
-- a constant or a Gaussian the catch-all would answer by its law
-- ('gaussianLeaf'), or a call entered with every argument constant. The
-- twin is conservative where the builder is not: it does not enter a lambda
-- redex, which the engines leave to the binding resolver.
isAffineOver :: CompilerMetadata -> Set.Set String -> Expr -> Bool
isAffineOver meta names e@(Expr ti nd)
  | Set.null (freeVarsExpr e `Set.intersection` names) =
      pType ti == Deterministic || (pType ti == PNormal && (isJust (gaussianLeaf meta e) || affineCallOver Set.empty))
  | otherwise = case nd of
      Var n -> n `Set.member` names
      Apply _ _ -> affineCallOver names
      -- A fresh Gaussian leaf whatever it reads ('affineFormOf').
      InjF (Named n) [_] | isCollapse n -> pType ti == PNormal
      InjF (Named "plus") [a, b] -> isAffineOver meta names a && isAffineOver meta names b
      InjF (Named "mult") [a, b] -> (constant a && isAffineOver meta names b)
                                 || (constant b && isAffineOver meta names a)
      InjF (Named "neg") [a] -> isAffineOver meta names a
      InjF (Named "fst") [Expr _ (InjF (Named "TCons") [a, _])] -> isAffineOver meta names a
      InjF (Named "snd") [Expr _ (InjF (Named "TCons") [_, b])] -> isAffineOver meta names b
      _ -> False
  where
    constant c = pType (getTypeInfo c) == Deterministic && Set.null (freeVarsExpr c `Set.intersection` names)
    -- A call is entered as a binding of each parameter to its argument (task
    -- binding-resolver-one-application-rule): affine when every argument is a
    -- constant or affine, and the callee's body is affine over the parameters
    -- bound to the non-constant ones.
    affineCallOver ns = case affineCall meta e of
      Just (pas, calleeBody) ->
        all (\(_, a) -> constant a || isAffineOver meta ns a) pas
          && isAffineOver meta (Set.fromList [ p | (p, a) <- pas, not (constant a) ]) calleeBody
      Nothing -> False

-- | Does top-level function @f@ reach itself through the top-level functions
-- its body names? Over-approximates as the modality fixpoint's call graph does
-- (a parameter shadowing a declaration name counts as a call).
isRecursiveFunction :: Program -> String -> Bool
isRecursiveFunction prog f = go Set.empty (callees f)
  where
    fs = functions prog
    go _ [] = False
    go seen (g : gs)
      | g == f = True
      | g `Set.member` seen = go seen gs
      | otherwise = go (Set.insert g seen) (callees g ++ gs)
    callees g = maybe [] (filter (`elem` map fst fs) . Set.toList . freeVarsExpr) (lookup g fs)

-- | A saturated call of a non-recursive top-level function, as the affine
-- algebra enters it: the callee's parameters paired with their arguments, and
-- its body. A declaration without parameters is the call with no arguments
-- (@g = draw x = Normal in x + x@, read as @g@). Recursion is declined: the
-- body would meet the call again. So is a local variable shadowing a
-- declaration's name, which is no call of it.
affineCall :: CompilerMetadata -> Expr -> Maybe ([(String, Expr)], Expr)
affineCall meta e
  | (Expr _ (Var f), args) <- flattenApplySpine e
  , Just decl <- lookup f (functions (compilingProgram meta))
  , not (isLocal f)
  , let ps = lambdaParams decl
  , length ps == length args
  , nub ps == ps
  , not (isRecursiveFunction (compilingProgram meta) f)
  = Just (zip ps args, stripLambdas decl)
  | otherwise = Nothing
  where
    isLocal f = case lookup f (typeEnv meta) of
      Just (_, False) -> True
      _ -> False
    lambdaParams (Expr _ (Lambda p b)) = p : lambdaParams b
    lambdaParams _ = []
    stripLambdas (Expr _ (Lambda _ b)) = stripLambdas b
    stripLambdas b = b

-- | The affine form of a call ('affineCall'): the callee's body under its
-- parameters, a constant argument let-bound under a fresh name, any other
-- marginalised with its own form ('marginaliseAs'). The latents the body itself draws
-- are keyed by the call site as well as by their own chain name, so two calls
-- of one function draw independent latents (forward chaining's per-invocation
-- identity, in the affine algebra's terms); the arguments' latents keep their
-- keys, so a latent shared through an argument stays shared.
affineCallForm :: CompilerMetadata -> ChainName -> [(String, Expr)] -> Expr -> CompilerMonad AffineForm
affineCallForm meta callCN pas calleeBody = do
  bound <- forM pas $ \(p, a) ->
    if isAffineConstant meta a
      then do
        fresh <- mkVariable p
        aIR <- toIRGenerate meta a
        setVariables [(fresh, aIR)]
        return (Left (p, fresh, rType (getTypeInfo a)))
      else do
        fa <- affineFormOf meta a
        return (Right (p, fa))
  let renames = [ r | Left r <- bound ]
      forms = [ f | Right f <- bound ]
      meta' = recoverVars [ fresh | (_, fresh, _) <- renames ]
                (foldr (uncurry marginaliseAs) meta { typeEnv = [ (fresh, (rty, False)) | (_, fresh, rty) <- renames ] ++ typeEnv meta } forms)
      calleeBody' = reinferRecovered meta' [ fresh | (_, fresh, _) <- renames ]
                (foldr (\(p, fresh, _) -> renameFreeVar p fresh) calleeBody renames)
  form <- affineFormOf meta' calleeBody'
  let argKeys = Set.unions [ Map.keysSet (afCoeffs fa) | (_, fa) <- forms ]
      key k = if k `Set.member` argKeys then k else k ++ "@" ++ callCN
  return form { afCoeffs = Map.mapKeys key (afCoeffs form) }

-- | When the probabilistic Apply arm finds no point inversion for a let-bound
-- variable, it marginalises the variable analytically if its certificate says
-- its law is an affine Gaussian form (the argument's 'JAffine' law, read by
-- 'affineOf') and all of its uses flow into a single Gaussian density leaf.
-- Answers the bound variable and the body to compile, with the variable to be
-- marginalised ('marginaliseAs'). 'isAffineOver' stays as the check that this compiler
-- can build the form's IR ('affineFormOf' is its twin), which a certificate
-- issued over the program as written cannot promise inside a callee entered
-- at a call site.
--
-- "A single leaf" is what makes dropping the variable sound: its latents are
-- then integrated exactly once, inside one scalar Normal. It holds when every
-- occurrence sits in one affine, PNormal-typed consumer, which is either the
-- value of a directly nested binding (whose own treatment -- witnessed,
-- marginalised in turn, or refused -- then carries the latents on) or the
-- terminal expression of the let spine. Uses spread over two consumers would
-- need a joint (multivariate) density, which is design affine-gaussian-forms
-- M2; those keep today's path. So does a binding whose body cannot be compiled
-- inline here ('bindInline'), and one returning a function.
affineMarginalisable :: CompilerMetadata -> RType -> Binding -> Maybe (String, Expr)
affineMarginalisable meta rt b
  | bindInline b
  , let x = bindVar b
  , let lamBody = bindBody b
  , not (isTArrowType rt)
  , Just cert <- affineOf (chainName (getTypeInfo v)) (nodeLaw meta v)
  , not (Map.null (acLatents cert))
  , isAffineOver meta envNames v
  , spineOK (Set.insert x envNames) x lamBody
  = Just (x, lamBody)
  | otherwise = Nothing
  where
    envNames = affineVars meta
    -- The form of @v@ is built here, in the binding's scope, and read at the
    -- consumer; a binder in between that shadows one of @v@'s free variables
    -- would change what that IR refers to, so it is refused.
    v = bindArg b
    vFree = freeVarsExpr v
    spineOK names x (Expr _ (Apply lam@(Expr _ (Lambda y inner)) val))
      | x `Set.member` freeVarsExpr val =
          not (x `Set.member` freeVarsExpr lam) && consumer names val
      | y == x || y `Set.member` vFree = False
      | otherwise = spineOK names x inner
    spineOK names x t = x `Set.member` freeVarsExpr t && consumer names t
    consumer names c = pType (getTypeInfo c) == PNormal && isAffineOver meta names c

-- | The joint affine engine's plan for a binding (design affine-gaussian-forms
-- M2; 'jointAffineApplicable').
data JointAffine = JointAffine
  { jaSpine  :: [(TypeInfo, String, Expr)]
    -- ^ The bindings nested below the bound variable, outermost first: the
    -- lambda's annotation, its variable and the value bound. Each is
    -- marginalised as an affine form too, never given an engine of its own.
  , jaFields :: [([Bool], Expr)]
    -- ^ The terminal expression's tuple fields, each with its access path
    -- into the sample (@False@ for @fst@, @True@ for @snd@). A terminal that
    -- is not a tuple is one field at the empty path.
  , jaNames  :: Set.Set String
    -- ^ Every variable read through an affine form at the fields: the
    -- enclosing marginalised ones, the bound variable and the spine's.
  }

-- | When no single affine consumer takes a Gaussian binding
-- ('affineMarginalisable'), it may still be integrated out analytically if
-- its certificate is an affine form and its body is a let spine of affine
-- bindings ending in a tuple: the fields reading the spine are then jointly
-- Gaussian, with covariance the Gram matrix of their coefficient vectors
-- (design affine-gaussian-forms §3), and the fields reading none of it are
-- independent of them. The compiler's twin of
-- 'ModalityInfer.jointAffineBindingCert'; keep the two in step. At most
-- 'ModalityInfer.jointAffineMaxSlots' fields read the spine.
jointAffineApplicable :: CompilerMetadata -> RType -> Binding -> Maybe JointAffine
jointAffineApplicable meta rt b
  | bindInline b
  , not (isTArrowType rt)
  , Just cert <- affineOf (chainName (getTypeInfo v)) (nodeLaw meta v)
  , not (Map.null (acLatents cert))
  , isAffineOver meta envNames v
  = walk (Set.insert (bindVar b) envNames) (freeVarsExpr v) [] (bindBody b)
  | otherwise = Nothing
  where
    v = bindArg b
    envNames = affineVars meta
    -- @bound@ holds the free variables of the values met so far: their forms
    -- are built in their own scope and read at the fields, so a binder in
    -- between must not shadow one.
    walk names bound acc (Expr _ (Apply (Expr lti (Lambda y inner)) val))
      | y `Set.member` names || y `Set.member` bound = Nothing
      | isAffineOver meta names val =
          walk (Set.insert y names) (bound `Set.union` freeVarsExpr val) ((lti, y, val) : acc) inner
      | otherwise = Nothing
    walk names _ acc t
      | not (null affine)
      , length affine <= ModalityInfer.jointAffineMaxSlots
      , all (isAffineOver meta names . snd) affine
      = Just (JointAffine (reverse acc) fields names)
      | otherwise = Nothing
      where
        fields = tupleFieldPaths t
        affine = filter (readsAffine names . snd) fields

-- | The joint affine engine ('jointAffineApplicable'). Every spine variable
-- is marginalised with its form. The fields reading the spine are grouped
-- into classes that covary (a covariance links two fields unless it is a
-- constant zero); a class of one is a scalar Gaussian leaf, and a larger one
-- a multivariate Gaussian density ('jointGaussianDensity') over its observed
-- fields. The other fields are independent factors, compiled as usual. A
-- cumulative query of a class of two or more is refused: the joint CDF of
-- correlated Gaussians has no closed form. A class whose covariance is a
-- constant singular matrix is declined: its law is degenerate, and its
-- measure needs the rank (affine-gaussian-forms M4).
jointAffineApply :: CompilerMetadata -> Bool -> Binding -> JointAffine -> IRExpr -> CompilerMonad (Either (Maybe String) PResult)
jointAffineApply meta cumulative binding ja sample = do
  let sr = semiringOf meta
      x = bindVar binding
      cn = chainName (getTypeInfo (bindHead binding))
  form0 <- affineFormOf meta (bindArg binding)
  let meta0 = marginaliseAs x form0 (withBindingLaw (extendMetaForLambda meta (getTypeInfo (bindHead binding)) x) binding x)
  meta' <- foldM (\m (lti, y, val) -> do
                    f <- affineFormOf m val
                    return (marginaliseAs y f (extendMetaForLambda m lti y)))
                 meta0 (jaSpine ja)
  let (affine, indep) = partition (readsAffine (jaNames ja) . snd) (jaFields ja)
  forms <- mapM (affineFormOf meta' . snd >=> shareForm) affine
  covs <- sequence [ sequence [ covEntry fi fj | fj <- forms ] | fi <- forms ]
  let n = length forms
      linked i j = i /= j && not (staticZero (covs !! i !! j))
      comps = stronglyConnComp [ (i, i, [ j | j <- [0 .. n - 1], linked i j ]) | i <- [0 .. n - 1] ]
      classes = [ sort c | CyclicSCC c <- comps ] ++ [ [i] | AcyclicSCC i <- comps ]
      covOf i j = fromMaybe const0 (covs !! i !! j)
      fieldOf i = fieldSampleAt sample (fst (affine !! i))
      staticCovOf c = mapM (\i -> mapM (\j -> maybe (Just 0) irConstFloat (covs !! i !! j)) c) c
      singular c = maybe False (not . choleskyPositive) (staticCovOf c)
      fieldNames c = intercalate ", " (map (showPath . fst . (affine !!)) c)
  case (filter ((> 1) . length) classes, filter singular classes) of
    (c : _, _) | cumulative ->
      refuse cn ("cannot compute a cumulative distribution of correlated Gaussian tuple fields "
                 ++ "(" ++ fieldNames c ++ ", sharing a latent through the binding of '" ++ x
                 ++ "'): their joint CDF has no closed form (design affine-gaussian-forms)")
    (_, c : _) -> return (Left (Just
      ("the tuple fields " ++ fieldNames c ++ " share Gaussian latents through the binding of '" ++ x
       ++ "' with a singular covariance: their joint law is degenerate, which the joint affine "
       ++ "engine does not measure (design affine-gaussian-forms M4)")))
    _ -> do
      gaussians <- forM classes $ \c -> case c of
        [i] -> do
          let (s, anyS) = fieldOf i
              form = forms !! i
              resid sigma = IROp OpDiv (IROp OpSub s (afConst form)) sigma
          r <- degenerateScaleGuard meta cumulative TFloat (afConst form) (snd (collapseAffine form)) s $ \sigma ->
                 if cumulative
                   then mass (distCumulative sr IRNormal (resid sigma))
                   else mkPResult (sealP (scaledNormalDensity sr (resid sigma) [sigma])) dim1 const1 constFalseIR
          return (zipResult (IRIf anyS) (detP (srOne sr)) r)
        _ -> do
          let guarded = isNothing (staticCovOf c)
              -- One density per subset of observed fields, selected on which
              -- are ANY: a Gaussian's marginal drops the unobserved rows.
              observed chosen [] = case reverse chosen of
                [] -> return (detP (srOne sr))
                obs -> do
                  let resid = [ IROp OpSub (fst (fieldOf i)) (afConst (forms !! i)) | i <- obs ]
                  p <- jointGaussianDensity sr guarded resid (\a b -> covOf (obs !! a) (obs !! b))
                  return (mkPResult (sealP p) (IRConst (VInt (length obs))) const1 constFalseIR)
              observed chosen (i : rest) = do
                whenObs <- observed (i : chosen) rest
                whenAny <- observed chosen rest
                return (zipResult (IRIf (snd (fieldOf i))) whenAny whenObs)
          observed [] c
      others <- forM indep $ \(path, e) -> do
        let (s, _) = fieldSampleAt sample path
            outer = anyOutsideField sample path
        if outer == constFalseIR
          then toIRInferenceSave meta' cumulative e s
          else do
            r <- guardedSubInference meta' [notIR outer] (toIRInferenceSave meta' cumulative e s)
            return (zipResult (IRIf outer) (detP (srOne sr)) r)
      return (Right (foldr1 (prodP sr) (gaussians ++ others)))
  where
    showPath [] = "the value"
    showPath p = intercalate "." (map (\b -> if b then "snd" else "fst") p)
    -- Each coefficient and constant is read by several covariances and
    -- residuals: bound once, unless it is a literal.
    shareForm (AffineForm c cs) = AffineForm <$> share "mean" c <*> traverse (share "coeff") cs
    share name e
      | Just d <- irConstFloat e = return (IRConst (VFloat d))
      | otherwise = do
          v <- mkVariable name
          setVariables [(v, e)]
          return (IRVar v)
    -- The covariance of two fields: the dot product of their coefficient
    -- vectors over the latents they share ('Nothing' when they share none).
    covEntry fa fb = case Map.elems (Map.intersectionWith (IROp OpMult) (afCoeffs fa) (afCoeffs fb)) of
      [] -> return Nothing
      ps -> Just <$> share "cov" (foldr1 (IROp OpPlus) ps)
    staticZero Nothing = True
    staticZero (Just e) = irConstFloat e == Just 0

-- | A *saturated* call to a top-level function whose result is Normal-derived.
-- Reuse the callee's own compiled @<name>_normal@ (which returns its (mu, sigma)
-- pair) instead of re-deriving the params here: the callee's definition is an
-- unapplied Lambda whose Normal draw is parametrized by its own arguments, so
-- there is no single Normal to read params off, and descending into it hit the
-- fallthrough error (task normal-shortcut-crashes-through-function-call).
--
-- The guards mirror exactly the conditions under which 'envToIR' gives the
-- callee a 'normalFun' at all; anything else falls through to the caller's
-- error, which is the status quo.
normalParamsViaCall :: CompilerMetadata -> PType -> Expr -> Maybe (CompilerMonad (IRExpr, IRExpr))
normalParamsViaCall meta wanted expr = do
  (fname, args) <- collectCall expr []
  decl <- lookup fname (functions (compilingProgram meta))
  if pType (getTypeInfo (stripDeclLambdas decl)) == wanted
       && isNormalExtractable decl
       && length (lambdaParams decl) == length args
       -- A probabilistic argument would be *sampled* by toIRGenerate rather
       -- than conditioned on, which is not a Normal shortcut at all.
       && all ((== Deterministic) . pType . getTypeInfo) args
    then Just $ do
      argIRs <- mapM (toIRGenerate meta) args
      var <- mkVariable "normal_params"
      setVariables [(var, foldl IRApply (IRVar (fname ++ "_normal")) argIRs)]
      return (IRDestruct AcFst (IRVar var), IRDestruct AcSnd (IRVar var))
    else Nothing
  where
    collectCall (Expr _ (Apply f a)) acc      = collectCall f (a : acc)
    collectCall (Expr _ (Var n)) acc@(_ : _)  = Just (n, acc)
    collectCall _ _                           = Nothing
    lambdaParams (Expr _ (Lambda n sub)) = n : lambdaParams sub
    lambdaParams _                       = []
    stripDeclLambdas (Expr _ (Lambda _ sub)) = stripDeclLambdas sub
    stripDeclLambdas e                       = e

-- | P(left < right) (@strictLess@) or P(left > right) of two PNormal
-- expressions, queried at the Bool @sample@. left - right ~ Normal(muL - muR,
-- sqrt(sL^2 + sR^2)), so p(left < right) = Phi((0 - mu) / sigma) and the
-- upper tail is its complement ('complementWhen', which keeps a normal upper
-- tail's precision). Gives P-mode a closed form for Gaussian-vs-Gaussian
-- comparisons, where neither side is a deterministic bound.
--
-- The difference's scale vanishes when both sides' scales do (a runtime zero
-- factor, as in @h z = (z * Normal) < (z * Normal)@ at @z = 0@). The
-- difference is then the point mass at @mu@, and the strict comparison holds
-- exactly when @mu < 0@ (resp. @mu > 0@): at @mu = 0@ neither does, which no
-- complement of a CDF can express. As in 'degenerateScaleGuard', the scale is
-- let-bound and the point-mass answer selected at run time; the ordinary leaf
-- reads a safe scale. A scale that is nonzero by construction (either side a
-- literal-scaled Normal) emits no guard.
normalDiffComparison :: CompilerMetadata -> Bool -> Expr -> Expr -> IRExpr -> CompilerMonad PResult
normalDiffComparison meta strictLess left right sample = do
  (muL, sL) <- toIRNormalParams meta left
  (muR, sR) <- toIRNormalParams meta right
  sigma <- irHypot sL sR
  let sr = semiringOf meta
      -- the queried Bool selects the complement: P(diff < 0) is the CDF
      complementOn = if strictLess then notIR sample else sample
      cdfAt0 mu s = complementWhen sr complementOn
        (distCumulative sr IRNormal (IROp OpDiv (IROp OpSub (IRConst (VFloat 0)) mu) s))
  if not (scaleMayVanish sigma)
    then mass <$> cdfAt0 (IROp OpSub muL muR) sigma
    else do
      vMu <- mkVariable "mu"
      vSigma <- mkVariable "sigma"
      setVariables [(vMu, IROp OpSub muL muR), (vSigma, sigma)]
      let isZero = IROp OpEq (IRVar vSigma) (IRConst (VFloat 0))
          safeScale = IRIf isZero (IRConst (VFloat 1)) (IRVar vSigma)
          holds = IROp (if strictLess then OpLessThan else OpGreaterThan) (IRVar vMu) (IRConst (VFloat 0))
          dirac = maskSR sr (equalityGuard TBool holds sample)
      leaf <- cdfAt0 (IRVar vMu) safeScale
      return (mass (IRIf isZero dirac leaf))

-- | Recursively extract (mu_log, sigma) as IRExprs from a PLogNormal-typed expression.
toIRLogNormalParams :: CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr)
toIRLogNormalParams meta (Expr _ (InjF (Named "exp") [e]))
  | pType (getTypeInfo e) == PNormal = toIRNormalParams meta e
toIRLogNormalParams meta (Expr _ (InjF (Named "mult") [e0, e1]))
  | pType (getTypeInfo e0) == PLogNormal, pType (getTypeInfo e1) == PLogNormal = do
      (mu0, s0) <- toIRLogNormalParams meta e0
      (mu1, s1) <- toIRLogNormalParams meta e1
      sigma <- irHypot s0 s1
      return (IROp OpPlus mu0 mu1, sigma)
toIRLogNormalParams meta (Expr _ (InjF (Named "mult") [e0, e1]))
  | pType (getTypeInfo e0) == PLogNormal = do
      (mu0, s0) <- toIRLogNormalParams meta e0
      det1 <- toIRGenerate meta e1
      return (IROp OpPlus mu0 (IRUnaryOp OpLog det1), s0)
toIRLogNormalParams meta (Expr _ (InjF (Named "mult") [e0, e1]))
  | pType (getTypeInfo e1) == PLogNormal = do
      (mu1, s1) <- toIRLogNormalParams meta e1
      det0 <- toIRGenerate meta e0
      return (IROp OpPlus mu1 (IRUnaryOp OpLog det0), s1)
-- sqrt(exp x) = exp(x/2): the log-space variable is halved, so (mu_log, sigma) -> (mu_log/2, sigma/2).
toIRLogNormalParams meta (Expr _ (InjF (Named "sqrt") [e]))
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IROp OpMult (IRConst (VFloat 0.5)) mu, IROp OpMult (IRConst (VFloat 0.5)) s)
-- sq(exp x) = (exp x)^2 = exp(2x): the log-space variable is doubled, so (mu_log, sigma) -> (2 mu_log, 2 sigma).
toIRLogNormalParams meta (Expr _ (InjF (Named "sq") [e]))
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IROp OpMult (IRConst (VFloat 2)) mu, IROp OpMult (IRConst (VFloat 2)) s)
-- recip(exp x) = 1/exp x = exp(-x): the log-space variable is negated, so (mu_log, sigma) -> (-mu_log, sigma).
toIRLogNormalParams meta (Expr _ (InjF (Named "recip") [e]))
  | pType (getTypeInfo e) == PLogNormal = do
      (mu, s) <- toIRLogNormalParams meta e
      return (IRUnaryOp OpNeg mu, s)
-- Tuple-field projection, mirroring toIRNormalParams.
toIRLogNormalParams meta (Expr _ (InjF (Named "fst") [Expr _ (InjF (Named "TCons") [a, _])]))
  | pType (getTypeInfo a) == PLogNormal = toIRLogNormalParams meta a
toIRLogNormalParams meta (Expr _ (InjF (Named "snd") [Expr _ (InjF (Named "TCons") [_, b])]))
  | pType (getTypeInfo b) == PLogNormal = toIRLogNormalParams meta b
toIRLogNormalParams meta (Expr ti (InjF f@(Named n) [Expr _ (Var name)]))
  | n `elem` ["fst", "snd"]
  , Just expr <- lookup name (functions (compilingProgram meta)) =
      toIRLogNormalParams meta (Expr ti (InjF f [expr]))
toIRLogNormalParams meta (Expr _ (Var name))
  | Just expr <- lookup name (functions (compilingProgram meta)) = toIRLogNormalParams meta expr
toIRLogNormalParams meta e | Just act <- normalParamsViaCall meta PLogNormal e = act
toIRLogNormalParams _ e = refuse (chainName (getTypeInfo e)) $ "toIRLogNormalParams: cannot extract LogNormal params from " ++ show (pType (getTypeInfo e))

-- | The Gaussian a @PNormal@ node's codegen law certifies it as, which the
-- catch-all answers from its (mu, sigma): a leaf (a primitive, a neural
-- read, a @collapse@), read by the scalar extractor, or an affine form,
-- built by the affine algebra ('gaussianParams'). The catch-all takes a
-- node iff this is 'Just' (design law-carrying-modality M6/M7; task
-- gaussian-catch-all-dispatch-on-codegen-law). The law is the node's
-- certificate re-inferred under the variables enclosing engines have
-- recovered ('codegenLaw'), so a node compiled after a recovery is gated on
-- what it is then, not on what the program as written said.
--
-- Three node kinds are never the catch-all's, whatever their law. A
-- function value is answered by the callee's own probability function (the
-- @Var@ and @Lambda@ equations). An application is the binding resolver's
-- whatever its head (design law-carrying-modality §C): the engines
-- dispatch it in their measured order ('ModalityInfer.engineOrder'), which
-- a catch-all reading the application's own affine law would run the
-- Gaussian collapse ahead of. And a variable's binder decided its
-- treatment: one marginalised as an affine form ('BoundVar.bvForm') has no
-- runtime value and is read through that form; any other local has its
-- value in scope, the @Var@ equation's leaf; and a declaration's name is a
-- call of its probability function.
data GaussianLaw = GaussianLeaf | GaussianAffine

gaussianLeaf :: CompilerMetadata -> Expr -> Maybe GaussianLaw
gaussianLeaf meta e@(Expr ti nd)
  | isTArrowType (rType ti) = Nothing
  | otherwise = case nd of
      Var n | Just bv <- Map.lookup n (lawEnv meta) -> GaussianAffine <$ bvForm bv
            | Just _ <- lookup n (typeEnv meta) -> Nothing
      Apply _ _ -> Nothing
      _ -> case ModalityInfer.lawJust (codegenLaw meta e) of
        ModalityInfer.JLeaf _ _ -> Just GaussianLeaf
        ModalityInfer.JAffine _ -> Just GaussianAffine
        _ -> Nothing

-- | The (mu, sigma) of a node the catch-all takes ('gaussianLeaf'): a leaf
-- by the scalar extractor, an affine form collapsed from the form the
-- affine algebra builds ('affineFormOf'), which follows calls, redexes and
-- the binder environment the scalar extractor does not see through.
gaussianParams :: CompilerMetadata -> GaussianLaw -> Expr -> CompilerMonad (IRExpr, IRExpr)
gaussianParams meta GaussianLeaf e = toIRNormalParams meta e
gaussianParams meta GaussianAffine e = collapseAffine <$> affineFormOf meta e

-- | A node's certificate as it holds at codegen: its 'nodeLaw', re-inferred
-- under the variables enclosing engines have recovered ('recoveredVars')
-- where there are any. The 'LawTable' certifies the program as written;
-- after a witness fold, an enumeration loop or a residue factor has fixed a
-- variable, a node reading it, or reading a binding computed from it, has
-- a different law (@draw y = x * 2.0 in y + Normal@ with @x@ recovered is
-- affine over the fresh Normal alone). This is the same inference
-- 'reinferRecovered' re-annotates the body with, asked for the node's law;
-- on demand, with no threaded table (task
-- gaussian-catch-all-dispatch-on-codegen-law).
codegenLaw :: CompilerMetadata -> Expr -> Law
codegenLaw meta e = case recoveredVars meta of
  [] -> nodeLaw meta e
  recovered -> reinferLawGiven (reinferContext meta) recovered e

-- | A @PLogNormal@ node the lognormal catch-all answers from its
-- (mu_log, sigma): the shapes 'toIRLogNormalParams' has an equation for,
-- read off the syntax. No law justification describes a lognormal yet
-- (task lognormal-log-affine-justification), so unlike the Gaussian
-- catch-all ('gaussianLeaf') this is a structural predicate, the static
-- twin of that extractor; keep the two in step. The node kinds the
-- Gaussian catch-all never takes are not taken here either: an application
-- is the binding resolver's, a local variable's value is in scope, a
-- declaration's name is a call of its probability function, and a
-- conditional is a mixture its own equation measures.
logNormalExtractable :: CompilerMetadata -> Expr -> Bool
logNormalExtractable meta (Expr ti nd)
  | isTArrowType (rType ti) = False
  | otherwise = case nd of
      InjF (Named "exp") [a] -> pType (getTypeInfo a) == PNormal
      InjF (Named "mult") [a, b] -> any ((== PLogNormal) . pType . getTypeInfo) [a, b]
      InjF (Named n) [a] | n `elem` ["sqrt", "sq", "recip"] -> pType (getTypeInfo a) == PLogNormal
      InjF (Named n) [Expr _ (InjF (Named "TCons") _)] | n `elem` ["fst", "snd"] -> True
      InjF (Named n) [Expr _ (Var f)] | n `elem` ["fst", "snd"] -> isJust (lookup f (functions (compilingProgram meta)))
      _ -> False

-- | A Gaussian (or lognormal) leaf whose scale can be zero at run time is a
-- point mass there, not a density: @z * Normal@ with @z = 0@ is the Dirac at
-- 0, and dividing by the zero scale answered NaN at dim 1 (task
-- helper-parameter-zero-factor-answers-nan; the static-zero twin is the
-- Dirac-law clause, 'lawPoint'). @build sigma@ is the ordinary leaf;
-- when the scale may vanish ('scaleMayVanish') it is let-bound and the leaf
-- selects, at run time, between that and the point mass at @point@ (an
-- equality indicator, or a step for a cdf). A scale that is a nonzero
-- constant by construction keeps its ordinary leaf and emits no guard.
--
-- The ordinary leaf reads the scale through @if sigma == 0 then 1 else
-- sigma@. Where the scale is zero that leaf is not selected, so its value is
-- unchanged, but the batched backend's eager @torch.where@ still
-- differentiates it, and a division by the zero scale there made the sample
-- gradient NaN.
degenerateScaleGuard :: CompilerMetadata -> Bool -> RType -> IRExpr -> IRExpr -> IRExpr
                     -> (IRExpr -> PResult) -> CompilerMonad PResult
degenerateScaleGuard meta cumulative rt point sigma sample build
  | not (scaleMayVanish sigma) = return (build sigma)
  | otherwise = do
      v <- mkVariable "sigma"
      setVariables [(v, sigma)]
      let sr = semiringOf meta
          dirac | cumulative = mass (compareValueExpr sr rt point sample)
                | otherwise  = indicatorP sr (equalityGuard rt point sample)
          isZero = IROp OpEq (IRVar v) (IRConst (VFloat 0))
          safeScale = IRIf isZero (IRConst (VFloat 1)) (IRVar v)
      return (zipResult (IRIf isZero) dirac (build safeScale))

-- | False only for a scale that is nonzero whatever the program's inputs: a
-- nonzero literal, and products, absolute values, negations and Gaussian-sum
-- scales ('irSqrt' of a sum of squares, 'irHypot') built from such. Anything
-- reading a runtime value -- a parameter, a network output, a let-bound
-- scale -- may vanish.
scaleMayVanish :: IRExpr -> Bool
scaleMayVanish = not . nonzero
  where
    nonzero (IRConst (VFloat s)) = s /= 0 && not (isNaN s)
    nonzero (IROp OpMult a b) = nonzero a && nonzero b
    nonzero (IROp OpDiv a b) = nonzero a && nonzero b
    nonzero (IRUnaryOp OpAbs a) = nonzero a
    nonzero (IRUnaryOp OpNeg a) = nonzero a
    nonzero (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog (IROp OpPlus (IROp OpMult a _) (IROp OpMult b _))))) =
      nonzero a || nonzero b
    nonzero _ = False
