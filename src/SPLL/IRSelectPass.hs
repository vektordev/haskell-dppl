-- | The IR select pass (design pytorch-tensorizer, milestone M1).
--
-- Batched inference (design pytorch-tensorizer) turns data-dependent branching
-- into /select/ semantics: rather than taking one arm of an @if@, evaluate both
-- arms for the whole batch and combine them with a mask (@torch.where@). The
-- conversion — deciding which ifs are elementwise-eligible and retagging them —
-- is backend-agnostic, so it lives here as an IR pass rather than inside a
-- codegen. Any future backend (Julia broadcast, JAX) reuses it, and @-d@
-- intermediates make the rewrite auditable.
--
-- This is M1: the pass alone. It retags eligible 'LazyIf' nodes to 'SelectIf'
-- but changes nothing about how they are emitted — the scalar backends lower
-- both modes to the same lazy ternary — so running it is a behavioural no-op,
-- pinned by a corpus differential test. The eligibility predicate here is the
-- seed of the M2 fragment guard; growing it (poison masking, the batched
-- runtime) is later milestones.
module SPLL.IRSelectPass
  ( selectPassEnv
  , selectPassExpr
  , isTensorFragment
  ) where

import SPLL.IntermediateRepresentation

-- | Run the select pass over an environment's probability and integration
-- functions. Generate functions are left untouched: batched sampling is a
-- separate milestone (M4), and their random draws are not select material.
selectPassEnv :: IREnv -> IREnv
selectPassEnv (IREnv groups adts globals) =
  IREnv (map selectPassGroup groups) adts globals

selectPassGroup :: IRFunGroup -> IRFunGroup
selectPassGroup g = g
  { probFun  = fmap onBody (probFun g)
  , integFun = fmap onBody (integFun g)
  }
  where onBody (body, doc) = (selectPassExpr body, doc)

-- | Retag every elementwise-eligible conditional in an expression to
-- 'SelectIf'. Bottom-up ('irMap'), so a node's arms are already processed when
-- it is examined; retagging an inner if does not change its eligibility (a
-- select-if is elementwise exactly when the lazy-if it came from was), so the
-- traversal order is immaterial to the result.
selectPassExpr :: IRExpr -> IRExpr
selectPassExpr = irMap retag
  where
    retag e@(IRIf cond thn els)
      | isTensorFragment cond && isTensorFragment thn && isTensorFragment els
      = IRSelect cond thn els
      | otherwise = e
    retag e = e

-- | Is this subexpression in the /tensor fragment/ — free of the constructs a
-- per-element @where@ cannot stand in for? Value-dependent control flow ('IRIf'
-- itself, arithmetic, comparisons, densities, tuple projection, enum sums)
-- broadcasts fine and stays in. Excluded are the structural / control
-- constructs (design pytorch-tensorizer, "Central insight"): list operations
-- (which have no fixed tensor shape), 'Either' constructor dispatch (a runtime
-- @isinstance@ branch), function application / lambdas (data-dependent
-- recursion depth), 'IRError' refusal arms (poison-masking is M3), and the
-- root-only query-type guard. A conditional is convertible only when its whole
-- condition and both arms lie in this fragment.
--
-- Because M1 lowers select identically to lazy, this predicate cannot affect
-- results; it decides only which nodes carry the tag (visible under @-d@) and
-- is the honest precursor of the M2 fragment guard.
isTensorFragment :: IRExpr -> Bool
isTensorFragment expr = ok expr && all isTensorFragment (getIRSubExprs expr)
  where
    ok e = case e of
      IRCons _ _        -> False
      IRHead _          -> False
      IRTail _          -> False
      IRMap _ _         -> False
      IRIndex _ _       -> False
      IRElementOf _ _   -> False
      IRLeft _          -> False
      IRRight _         -> False
      IRFromLeft _      -> False
      IRFromRight _     -> False
      IRIsLeft _        -> False
      IRIsRight _       -> False
      IRApply _ _       -> False
      IRLambda _ _      -> False
      IRError _         -> False
      IRConformsTo _ _  -> False
      _                 -> True
