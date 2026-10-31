-- The pattern-match coverage checker exceeds its default 30-model budget on
-- 'toIRGenerate's Var case (a 4-way match over @Maybe (RType, Bool)@ with a
-- nested RType pattern), and then reports that exhaustive match as incomplete.
-- Raising the budget lets it finish rather than hiding the result. Two more
-- guarded clauses at the top of 'toIRInference' (task
-- set-witness-eq-o2-optimizer-crash) pushed a second check -- 'toIRGenerate's
-- Var case again, per the checker's own report site -- over 1000 as well;
-- raised again rather than split the check.
{-# OPTIONS_GHC -fmax-pmcheck-models=4000 #-}

-- | The generate variant's translator, 'toIRGenerate'.
module SPLL.IRCompiler.Generate (
  toIRGenerate
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import PredefinedFunctions
import SPLL.Typing.PType
import SPLL.Semiring
import qualified Data.Set as Set
import SPLL.IRCompiler.Monad hiding (toIRGenerate)
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Gaussian

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: CompilerMetadata -> Expr -> CompilerMonad  IRExpr
toIRGenerate meta (Expr _ (IfThenElse cond left right)) = do
  c <- toIRGenerate meta cond
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IRIf c l r
toIRGenerate meta (Expr _ (ThetaI a ix)) = do
  a' <- toIRGenerate meta a
  return $ IRDestruct (AcTheta ix) a'
toIRGenerate meta (Expr _ (Subtree a ix)) = do
  a' <- toIRGenerate meta a
  return $ IRDestruct (AcSubtree ix) a'
toIRGenerate _ (Expr _ (Constant (VError e))) = return $ IRError e
toIRGenerate _ (Expr _ (Constant x)) = return (IRConst (fmap failConversion x))
-- Distribution primitives (reserved-name Vars): each occurrence is a fresh draw.
toIRGenerate _ (Expr _ (Var "Uniform")) = return $ IRSample IRUniform
toIRGenerate _ (Expr _ (Var "Normal")) = return $ IRSample IRNormal
-- A product with a statically-zero factor is zero whatever the other factor
-- draws (its law is a point, 'lawPoint'). Emitting the
-- other factor would put its unread draw into every generate-and-compare
-- probability over the product, which the generate-backed guard then refused
-- (fuzz-admission-oracle-bugs item 6).
toIRGenerate meta e@(Expr _ (InjF (Named name) [_, _]))
  | name `elem` ["mult", "multI"], Just v <- lawPoint meta e =
  return (IRConst (valueToIR v))
-- A random 'collapse' draws from the Gaussian of its operand's moments, not
-- from the operand; a point operand is the point, which the generic equation
-- below gives through the identity forward. The moments' bindings are scoped
-- to the draw: generate code closes no block of its own.
toIRGenerate meta (Expr ti (InjF (Named name) [a]))
  | isCollapse name, pType ti /= Deterministic = do
  moments <- scoped (momentsOf meta a)
  return (closeExpr moments (\(mu, sigma) -> IROp OpPlus mu (IROp OpMult sigma (IRSample IRNormal))))
toIRGenerate meta (Expr ti (InjF (Named name) params)) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  let resolvedName = resolveInjF (rType ti) name
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let FDecl {inputVars=vars, body=fwdExpr} = fwd
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen meta vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
toIRGenerate meta (Expr _ (Var name)) = do
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
    -- Invariant, not a refusal (task static-refusals-become-absent-variants): every bound name is in the type env.
    Nothing -> error ("Could not find name in TypeEnv: " ++ name)
toIRGenerate meta (Expr t (Lambda name subExpr)) =
  IRLambda name <$> toIRGenerate (extendMetaForLambda meta t name) subExpr
-- A dead binding draws nothing anyone reads, so its argument is not emitted:
-- the value is the body's either way. Beyond saving the work, this is what
-- keeps a Deterministic expression's generate-and-compare probability free of
-- a sample -- @(\a -> (\b -> a) (if Uniform < 0.5 then 2 else 1)) 0.0@ is
-- typed Deterministic, and its probability function used to carry the unread
-- draw and be refused as generate-backed (fuzz-admission-oracle-bugs item 7).
toIRGenerate meta (Expr _ (Apply (Expr t (Lambda x deadBody)) _))
  | not (x `Set.member` freeVarsExpr deadBody) =
  toIRGenerate (extendMetaForLambda meta t x) deadBody
toIRGenerate meta (Expr _ (Apply l v)) = do
  l' <- toIRGenerate meta l
  v' <- toIRGenerate meta v
  return $ IRApply l' v'
toIRGenerate meta (Expr _ (ReadNN name subexpr)) = do
  sub <- toIRGenerate meta subexpr
  return $ IRApply (IRVar (name ++ "_auto_gen")) sub


packParamsIntoLetinsGen :: CompilerMetadata -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen _ [] [] expr = return $ expr
-- Invariant, not a refusal (task static-refusals-become-absent-variants): an InjF's declared input variables match its arity.
packParamsIntoLetinsGen _ [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen _ _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen meta (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate meta p
  e <- packParamsIntoLetinsGen meta vars params expr
  return $ IRLetIn v pExpr e
