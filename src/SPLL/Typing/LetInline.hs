-- | Inlining of unwitnessed single-use bindings whose sole use is a
-- distribution-family closure (task
-- @unwitnessed-gaussian-let-chain-admitted-but-crashes@).
--
-- @ModalityInfer@'s family layer (@tryNormalClosure@) types @x + Normal@ as
-- 'PNormal' whether or not @x@ is a @let@-bound variable, because the sum of two
-- Gaussians really is Gaussian. Admitting the program is therefore right. But
-- the only place that closed form is /realised/ is the Gaussian shortcut on an
-- inline @Normal + Normal@: through a @let@, @IRCompiler@'s probabilistic
-- @Apply@ arm first tries to recover the bound variable from the observation,
-- and for an unwitnessed binding whose sibling operand draws fresh randomness
-- neither point inversion nor the set-valued witness engine has an equation. The
-- refusal is an eager @error@, so it takes @generate@ down with it:
--
-- > main = let x = Normal in let y = x + Normal in y
--
-- This pass closes the gap from the other side: @let x = e in body@ with a
-- /single/ use of @x@ is @body[e\/x]@, so inlining the binding puts the two
-- @Normal@s next to each other and the existing inline shortcut fires. The
-- density is kept rather than thrown away (the alternative considered in the
-- task was to make the let rule refuse the family closure for an unwitnessed
-- binding, typing the program 'Bottom').
--
-- The applicability predicate is deliberately narrow: it fires only on bindings
-- that currently have /no/ engine at all, so no working program changes path.
-- See 'eligibleBinding'.
--
-- What it does /not/ fix is the multi-use shape —
-- @let x = Normal in (x + Normal, x + Normal)@ — where the two outputs are
-- genuinely correlated. Inlining there would decorrelate them, and the honest
-- density is a bivariate Gaussian no engine implements; that program is still
-- admitted and still dies in the set-witness refusal.
module SPLL.Typing.LetInline
  ( inlineFamilyClosureLets
  , letBindingCount
  ) where

import Data.Maybe (isJust)

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.ForwardChaining (FCData, isWitnessedLambda, toInvExprMaybe)
import SPLL.Typing.ModalityInfer (tryNormalClosure)
import SPLL.Typing.PType

-- | One rewriting round over a modality-typed, chain-named program: substitute
-- every eligible binding (see 'eligibleBinding') into its single use.
--
-- 'Nothing' when nothing was eligible, which is the case for every program that
-- does not exhibit the shape — the caller then skips re-running the typing
-- stages entirely. A round strictly reduces the number of @let@ nodes, so the
-- caller's fixpoint loop terminates.
--
-- The result carries the /old/ chain names (and stale pTypes at the nodes above
-- a substitution), so the caller must re-run enum annotation, chain naming and
-- the modality pass on it before using it for anything.
inlineFamilyClosureLets :: FCData -> Program -> Maybe Program
inlineFamilyClosureLets fcData prog
  | rewritten == prog = Nothing
  | otherwise         = Just rewritten
  where
    rewritten = prog { functions = map rewriteDecl (functions prog) }
    rewriteDecl (n, body) = (n, rewriteExpr fcData (adts prog) (cnOf body) body)

-- | Number of @let@ nodes (directly-applied lambdas) in a program. Bounds the
-- caller's fixpoint loop: each round removes at least one.
letBindingCount :: Program -> Int
letBindingCount prog = sum [ go body | (_, body) <- functions prog ]
  where
    go e = here e + sum (map go (getSubExprs e))
    here (Expr _ (Apply (Expr _ Lambda{}) _)) = 1
    here _                                    = 0

cnOf :: Expr -> ChainName
cnOf = chainName . getTypeInfo

-- | Rewrite one declaration body. Top-down: a substituted body is re-walked, so
-- a chain of eligible bindings collapses in a single round. @obsCN@ is the
-- declaration root's chain name, the node the witnessed-binding query is seeded
-- at (exactly as 'SPLL.Typing.ModalityInfer' seeds it).
rewriteExpr :: FCData -> [ADTDecl] -> ChainName -> Expr -> Expr
rewriteExpr fcData adtsDecl obsCN = go
  where
    go e = case node e of
      Apply (Expr lti (Lambda x body)) v
        | eligibleBinding fcData adtsDecl obsCN lti x body v
        -> go (substVar x v body)
      _ -> Expr (ann e) (fmap go (node e))

-- | Is this @let@ one the compiler admits but has no equation for, and can it be
-- removed by substitution?
--
-- Every clause is load-bearing:
--
-- * __The use sits under a chain of certified family closures, one of whose
--   siblings draws fresh randomness.__ "Certified" is 'tryNormalClosure', the
--   family layer's own table, so the pass and the rule that admitted the
--   program agree by construction on what a family closure is. Reading the
--   ancestor's 'PType' instead is /not/ equivalent and was the first attempt's
--   bug: 'injFMod' also labels a unary passthrough @log x@ \/ @sqrt x@ \/
--   @double x@ 'PNormal' (the floor preserves a single operand's family), where
--   no closed form exists and 'SPLL.IRCompiler.toIRNormalParams' dies.
--
--   The fresh draw is what makes the use non-invertible in the first place, and
--   its shape is the one no engine has an equation for. Without it the binding
--   belongs to somebody: @x * 2.0@ is point-invertible, and @if log x > 0@ is
--   the set-valued witness engine's interval transport, which measures or
--   refuses these by design (task @set-witness-interval-partial-inverse@).
--   It is looked for along the whole closure chain rather than at the immediate
--   parent, because the use may be scaled first: in @x * 2.0 + Normal@ the
--   fresh operand is the /grandparent's/ sibling.
--
-- * __Exactly one use, evaluated at most once.__ Two uses of a random binding
--   are correlated draws and inlining would make them independent;
--   'singleUseAncestors' also refuses a use under a lambda that is not directly
--   applied, where the binding would go from one draw to one per call.
--
-- * __Neither witnessed nor point-invertible.__ This is precisely the condition
--   under which @IRCompiler@'s probabilistic @Apply@ arm falls through to
--   'SPLL.IRCompiler.setWitnessApply' — i.e. the set of bindings that currently
--   die. A binding either engine can already handle keeps its existing path, so
--   the corpus's probabilities, dims and branch counts are untouched.
--
-- The surviving intersection is narrow on purpose: @plus@ of two Gaussians and
-- @mult@ of two log-normals are the only entries of the family table that admit
-- a second random operand at all.
eligibleBinding :: FCData -> [ADTDecl] -> ChainName -> TypeInfo -> String -> Expr -> Expr -> Bool
eligibleBinding fcData adtsDecl obsCN lti x body v =
  isFamily (pType (getTypeInfo v))
  && maybe False overFreshDraw (singleUseAncestors x body)
  && not (isWitnessedLambda fcData adtsDecl obsCN lambdaCN)
  && not (isJust (toInvExprMaybe fcData adtsDecl lambdaCN))
  where
    lambdaCN = chainName lti
    isFamily pt = pt == PNormal || pt == PLogNormal
    -- The unbroken run of certified closures directly above the use, and
    -- whether any of them combines it with a fresh draw.
    overFreshDraw = any freshSibling . takeWhile (certifiedClosure . fst)
    certifiedClosure p = case node p of
      InjF (Named fname) operands ->
        isJust (tryNormalClosure fname (map (pType . getTypeInfo) operands))
      _ -> False
    freshSibling (p, onPath) =
      any containsRandomSource
          [ o | o <- getSubExprs p, chainName (getTypeInfo o) /= chainName (getTypeInfo onPath) ]

-- | The ancestors of the one free use of @x@ in @e@ — innermost first, each
-- paired with the child of it the use sits in — when there is exactly one use
-- and it is evaluated at most once.
--
-- "At most once" is the reason the walk tracks binders rather than just
-- counting: a use inside a lambda body is evaluated once per call, so
-- @let x = Normal in map (\\i -> x) xs@ must not be inlined (one draw shared by
-- every element would become one draw each). A /directly applied/ lambda is a
-- @let@, whose body and argument are each evaluated once, so it stays
-- transparent — which is what admits the nested-let repro shape. An @if@ arm is
-- evaluated at most once and needs no special case.
singleUseAncestors :: String -> Expr -> Maybe [(Expr, Expr)]
singleUseAncestors x root = case go False [] root of
  [(False, ancestors)] -> Just ancestors
  _                    -> Nothing
  where
    -- (was a non-applied lambda crossed on the way?, ancestors innermost first)
    go :: Bool -> [(Expr, Expr)] -> Expr -> [(Bool, [(Expr, Expr)])]
    go opaque ancestors e = case node e of
      Var n | n == x -> [(opaque, ancestors)]
      Lambda y b
        | y == x    -> []                          -- shadowed
        | otherwise -> go True ((e, b) : ancestors) b  -- unknown evaluation count
      Apply l@(Expr _ (Lambda y b)) v ->
        (if y == x then [] else go opaque ((l, b) : ancestors) b)
        ++ go opaque ((e, v) : ancestors) v
      _ -> concat [ go opaque ((e, c) : ancestors) c | c <- getSubExprs e ]

-- | Capture-free only by construction: this is used on a binding whose value
-- sits in the enclosing scope, so @v@ has no free variable the body binds.
-- Shadowing of @x@ itself is respected.
substVar :: String -> Expr -> Expr -> Expr
substVar x v = go
  where
    go e = case node e of
      Var n | n == x -> v
      Lambda y _ | y == x -> e
      _ -> Expr (ann e) (fmap go (node e))
