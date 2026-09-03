-- | The tensor lowering pass (design ir-tensor-values).
--
-- Rewrites the enum-sum family -- 'IREnumSum', 'IRLogEnumSum' and
-- 'IREnumSumPaired' -- into the tensor builtins: a 'BTensor' domain, a 'BMap' over it, and a
-- 'BReduce' with the operator the constructor had baked in.
--
-- The point is not tidiness. Those three constructors differ only in reduction
-- operator and accumulator arity, and 'IREnumSumPaired' exists solely because
-- "two single-scalar loops cannot share one loop body" -- a branch-counting
-- compile needs both a sum over probability and a sum over branch count from
-- one body, and with no way to /name/ a vector of per-iteration results each
-- re-embedded the whole per-iteration computation. A tensor is that name:
-- the paired form becomes one 'BMap', let-bound, reduced twice. That is the
-- design's central claim, and this pass is where it is cashed.
--
-- Backend-agnostic and run for every backend, so all four consumers (the
-- interpreter, scalar Python, Julia, and the batched tensorizer) see one IR.
-- Refusals are preserved rather than special-cased: the batched backend's
-- admissibility walk checked a domain through @scalarDiscreteMulti@, and after
-- the rewrite the same domain values are ordinary 'IRConst' children that the
-- walk's existing per-constant check rejects for the same reason.
--
-- This pass does /not/ retire the enum-sum constructors -- that is
-- retire-irenumsum, which also depends on ir-reengineering. A domain that
-- cannot be enumerated at compile time is left as it was.
module SPLL.IRTensorPass
  ( tensorPassEnv
  , tensorPassExpr
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang (multiValueToValueList)
import SPLL.Lang.Types (MultiValue)
import Control.Monad.State (State, evalState, get, put)

-- | Run the tensor lowering over every function body in an environment.
tensorPassEnv :: IREnv -> IREnv
tensorPassEnv (IREnv groups adts globals) =
  IREnv (map onGroup groups) adts globals
  where
    onGroup g = g
      { genFun    = fmap onBody (genFun g)
      , probFun   = fmap onBody (probFun g)
      , integFun  = fmap onBody (integFun g)
      , writeLogitsFun = fmap onBody (writeLogitsFun g)
      , normalFun = fmap onBody (normalFun g)
      }
    onBody (body, doc) = (tensorPassExpr body, doc)

-- | Rewrite every enumerable sum in an expression onto a tensor.
--
-- Bottom-up ('irMap'), so an inner sum is already a tensor when its enclosing one
-- is rewritten. The fresh-name counter is threaded across the whole expression
-- rather than per node, so the binding a paired sum introduces is unique even
-- when several appear at different nesting levels -- a reused name would
-- shadow and corrupt a binding of a different type, exactly as it would in the
-- optimizer's CSE.
tensorPassExpr :: IRExpr -> IRExpr
tensorPassExpr e = evalState (go e) 0
  where
    go :: IRExpr -> State Int IRExpr
    go x = do
      x' <- irDescendM go x
      rewrite x'

    rewrite :: IRExpr -> State Int IRExpr
    rewrite (IREnumSum name mv body) =
      pure (reduceOver ROpAdd (mapOver name body mv))
    rewrite (IRLogEnumSum name mv body) =
      pure (reduceOver ROpLogSumExp (mapOver name body mv))
    -- The paired form. The body yields a @(probability, branchCount)@ pair per
    -- enumerated value; let-binding the mapped axis is what lets the two
    -- components reduce independently while the body is still evaluated once.
    -- The probability component reduces with the operator the flag selects,
    -- the branch count always by a plain add -- exactly 'IREnumSumPaired''s
    -- documented semantics.
    rewrite (IREnumSumPaired logSp name mv body) = do
      n <- fresh
      let axis  = "_tensor" ++ show n
          -- Two projections over the one shared axis, each reduced on its own.
          probs = IRBuiltin BMap [IRLambda (axis ++ "_p") (IRDestruct AcFst (IRVar (axis ++ "_p"))), IRVar axis]
          bcs   = IRBuiltin BMap [IRLambda (axis ++ "_b") (IRDestruct AcSnd (IRVar (axis ++ "_b"))), IRVar axis]
          opP   = if logSp then ROpLogSumExp else ROpAdd
      pure $ IRLetIn axis (mapOver name body mv)
               (IRConstruct TgTuple [reduceOver opP probs, reduceOver ROpAdd bcs])
    rewrite x = pure x

    fresh :: State Int Int
    fresh = do { n <- get; put (n + 1); return n }

-- | @map (\\name -> body) over <domain>@.
mapOver :: Varname -> IRExpr -> MultiValue -> IRExpr
mapOver name body mv = IRBuiltin BMap [IRLambda name body, tensorDomain mv]

-- | @reduce op <axis>@.
-- Always axis 0: every tensor this pass builds is rank 1 (an enumeration is
-- one axis), so the reduce collapses that axis to a scalar.
reduceOver :: ReduceOp -> IRExpr -> IRExpr
reduceOver op t = IRBuiltin (BReduce op 0) [t]

-- | The enumerated domain as a rank-1 tensor of constants. The values, and
-- their order, are exactly what the enum-sum node would have looped over, so
-- the reduction sees the same terms in the same order.
tensorDomain :: MultiValue -> IRExpr
tensorDomain mv = IRBuiltin (BTensor [EFixed (length vals)]) (map (IRConst . valueToIR) vals)
  where vals = multiValueToValueList mv
