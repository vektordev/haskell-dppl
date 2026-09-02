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
-- This is M1: the pass alone. It rewrites eligible 'IRIf' nodes to 'IRSelect'
-- but changes nothing about how they are emitted — the scalar backends lower
-- 'IRSelect' identically to 'IRIf' (the interpreter delegates, each codegen
-- desugars it at entry) — so running it is a behavioural no-op, pinned by a
-- corpus differential test. The eligibility predicate here is the seed of the
-- M2 fragment guard; growing it (poison masking, the batched runtime) is later
-- milestones.
module SPLL.IRSelectPass
  ( selectPassEnv
  , selectPassExpr
  , isTensorFragment
  , desugarSelectEnv
  , desugarSelectExpr
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

-- | Rewrite every elementwise-eligible 'IRIf' in an expression to 'IRSelect'.
-- Bottom-up ('irMap'), so a node's arms are already processed when it is
-- examined; converting an inner if does not change its eligibility (an
-- 'IRSelect' is elementwise exactly when the 'IRIf' it came from was, and
-- 'isTensorFragment' treats the two alike), so the traversal order is
-- immaterial to the result.
selectPassExpr :: IRExpr -> IRExpr
selectPassExpr = irMap convert
  where
    convert e@(IRIf cond thn els)
      | isTensorFragment cond && isTensorFragment thn && isTensorFragment els
      = IRSelect cond thn els
      | otherwise = e
    convert e = e

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
-- A dense map's lambda is a compile-time unroll over a statically-known
-- extent, not the data-dependent application 'IRLambda' is excluded for, so
-- the fragment is checked *through* it. Without this case the dense lowering
-- would shrink the tensor fragment wherever an enumerable sum appears -- the
-- enum-sum constructors it replaces were in the fragment (design
-- ir-tensor-values).
isTensorFragment (IRBuiltin BMap [IRLambda _ body, d]) =
  isTensorFragment body && isTensorFragment d
isTensorFragment expr = ok expr && all isTensorFragment (getIRSubExprs expr)
  where
    ok e = case e of
      IRCons _ _        -> False
      IRHead _          -> False
      IRTail _          -> False
      IRMap _ _         -> False
      IRIndex _ _       -> False
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

-- | Lower every 'IRSelect' back to an 'IRIf' throughout an environment. This is
-- how scalar codegens consume select-tagged IR (design pytorch-tensorizer, M1,
-- strategy B): they call this once at entry so the rest of the backend never
-- sees an 'IRSelect' and needs no per-site handling. A batched backend, by
-- contrast, would lower 'IRSelect' to @torch.where@ and would /not/ desugar.
desugarSelectEnv :: IREnv -> IREnv
desugarSelectEnv (IREnv groups adts globals) =
  IREnv (map onGroup groups) adts globals
  where
    onGroup g = g
      { genFun   = fmap onBody (genFun g)
      , probFun  = fmap onBody (probFun g)
      , integFun = fmap onBody (integFun g)
      , encodeFun = fmap onBody (encodeFun g)
      , normalFun = fmap onBody (normalFun g)
      }
    onBody (body, doc) = (desugarSelectExpr body, doc)

desugarSelectExpr :: IRExpr -> IRExpr
desugarSelectExpr = irMap lower
  where
    lower (IRSelect cond thn els) = IRIf cond thn els
    lower e                       = e
