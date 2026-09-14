-- | Normalisation of the /callee/ position of an application (task
-- @modality-arrow-apply-crashes@).
--
-- Probability mode compiles @Apply l v@ by inverting the observation through
-- @l@'s body, which presupposes that @l@ names a lambda the compiler can see:
-- 'SPLL.Typing.ForwardChaining.findEquivalentExpression' must resolve @l@'s
-- chain name to a @LambdaInfo@. That holds for a literal lambda and for a
-- top-level function, and fails for every other way a program can produce a
-- function /value/ — a lambda projected out of a tuple, taken from a list, or
-- chosen by an @if@ — where the compiler crashed with an internal
-- "should resolve to a lambda" error, or (for a randomly chosen one) compiled a
-- mixture that multiplied a branch weight by a closure and died in the
-- interpreter.
--
-- This pass removes the selection instead of teaching the inference engines to
-- see through it. Two rewrites, both purely syntactic:
--
-- * __An @if@ in callee position is distributed into its arms__:
--   @(if c then f else g) v@ becomes @if c then f v else g v@. The arms are
--   alternatives, so no draw in @v@ is duplicated — only one arm is ever
--   realised — and the result is the ordinary mixture the 'IfThenElse' rules
--   already compile, with each arm now an applied lambda literal. This is what
--   makes a /probabilistic/ function value work end-to-end: the mixture is
--   taken over the two applications' probabilities, never over the closures.
--
-- * __A callee that denotes a lambda literal is replaced by it__:
--   @fst@ \/ @snd@ of a tuple literal, @head@ \/ @tail@ of a list literal, and
--   @let@-bound names standing for either, are reduced until a @Lambda@ falls
--   out ('reduceCallee'). Only a reduction that bottoms out at a lambda literal
--   is taken, so nothing else is ever moved.
--
-- What it deliberately does /not/ do: rewrite a callee that is already a bare
-- name. Forward chaining resolves a variable to the lambda it stands for by
-- itself, so a named callee — a top-level function, or a @let@-bound one — is
-- the one selection the existing engines see through; expanding it anyway
-- would move working programs onto a different path (and would not terminate
-- for a recursive function). Nor does it reach through a binding whose value is
-- itself randomly selected (@let p = if Uniform < 0.5 then f else g@), where
-- copying the selection to two use sites would turn one draw into two.
--
-- The pass runs on the freshly parsed program, before RType inference, so the
-- rewritten nodes need no annotations: every 'TypeInfo' is still @NotSetYet@
-- and the whole pipeline annotates the rewritten tree from scratch.
module SPLL.CalleeNormalize
  ( normalizeCallees
  ) where

import qualified Data.Set as Set

import SPLL.Lang.Lang
import SPLL.Lang.Types

-- | The @let@-bound values in scope, innermost first. Only bindings introduced
-- by a directly-applied lambda go in here: a lambda parameter's value is not
-- known statically.
type Env = [(String, Expr)]

-- | One pass over every declaration body.
--
-- 'Nothing' when nothing was rewritten, which is the case for every program
-- that does not select a function value — the caller then has no new stage to
-- report.
normalizeCallees :: Program -> Maybe Program
normalizeCallees prog
  | rewritten == prog = Nothing
  | otherwise         = Just rewritten
  where
    rewritten = prog { functions = [ (n, rewrite [] body) | (n, body) <- functions prog ] }

-- | Rewrite one expression under the @let@-bindings enclosing it.
rewrite :: Env -> Expr -> Expr
rewrite env e = case node e of
  Apply l v            -> rewriteApply env (ann e) l v
  Lambda x lambdaBody  -> Expr (ann e) (Lambda x (rewrite (dropBinder x env) lambdaBody))
  other                -> Expr (ann e) (fmap (rewrite env) other)

-- | The application cases. @ti@ is the application node's own annotation, which
-- every node this builds inherits: they all stand for the same value, and at
-- this point in the pipeline it is @NotSetYet@ anyway.
rewriteApply :: Env -> TypeInfo -> Expr -> Expr -> Expr
rewriteApply env ti l v = case node l of
  -- `let x = v in body`. The callee is already a lambda literal; what this case
  -- is here for is to record the binding, so a use of `x` further in can be
  -- reduced by 'reduceCallee'.
  Lambda x lambdaBody ->
    let v' = rewrite env v
        bodyEnv = (x, v') : dropBinder x env
    in Expr ti (Apply (Expr (ann l) (Lambda x (rewrite bodyEnv lambdaBody))) v')
  -- An `if` choosing between function values: push the application into both
  -- arms. Re-walked, so a nested selection (`(if a then (if b then f else g)
  -- else h) x`) collapses in the same pass.
  IfThenElse c t f ->
    rewrite env (Expr ti (IfThenElse c (Expr ti (Apply t v)) (Expr ti (Apply f v))))
  -- A *named* callee is left alone: forward chaining resolves a variable to the
  -- lambda it stands for by itself (that is what its equivalence classes are
  -- for), so this is the one selection the existing engines already see
  -- through. Substituting it anyway would rewrite working programs onto a
  -- different path -- `testCases/hoProbValueLambda` and `twiceApplication`
  -- both changed answer when an earlier draft did.
  Var _ -> Expr ti (Apply l (rewrite env v))
  -- A callee that denotes a lambda literal: use the lambda. Only taken when the
  -- reduction really bottoms out at a `Lambda`, so a callee that stays a
  -- projection or a selection is left exactly as it was.
  _ | Just lam <- reduceCallee env l -> Expr ti (Apply (rewrite env lam) (rewrite env v))
  _ -> Expr ti (Apply (rewrite env l) (rewrite env v))

-- | The lambda literal a callee expression denotes, if that is statically
-- decidable: a literal lambda, a field of a tuple literal, an element of a list
-- literal, or a @let@-bound name standing for one of those, in any combination.
--
-- 'Nothing' for everything else — including a name bound to a randomly selected
-- function, whose selection must stay at its binding site.
reduceCallee :: Env -> Expr -> Maybe Expr
reduceCallee env l = case reduce [] l of
  lam@(Expr _ Lambda{}) -> Just lam
  _                     -> Nothing
  where
    -- Structural projection/lookup reduction. Returns the argument unchanged
    -- when there is nothing to reduce. @seen@ bounds the variable expansions by
    -- the size of the environment, so a malformed self-referential binding
    -- cannot loop.
    reduce seen e = case node e of
      Var n | n `notElem` seen, Just bound <- lookup n env -> reduce (n : seen) bound
      InjF (Named "fst") [p]
        | Expr _ (InjF (Named "TCons") [a, _]) <- reduce seen p -> reduce seen a
      InjF (Named "snd") [p]
        | Expr _ (InjF (Named "TCons") [_, b]) <- reduce seen p -> reduce seen b
      InjF (Named "head") [xs]
        | Expr _ (InjF (Named "Cons") [h, _]) <- reduce seen xs -> reduce seen h
      InjF (Named "tail") [xs]
        | Expr _ (InjF (Named "Cons") [_, t]) <- reduce seen xs -> reduce seen t
      _ -> e

-- | Names a binder shadows: drop its own entry, and any entry whose value
-- mentions it. Moving such a value inwards would rebind it to the wrong
-- binder. ('containedVars' over-approximates the free variables, which is the
-- safe direction.)
dropBinder :: String -> Env -> Env
dropBinder x env = [ (n, v) | (n, v) <- env, n /= x, not (Set.member x (containedVars varsOfExpr v)) ]
