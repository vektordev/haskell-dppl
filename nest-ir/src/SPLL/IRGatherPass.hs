-- | Batched-only rewrite of a point read written as a one-hot sum into one
-- indexed read (task batched-mask-variant-neural-read-nests-v-deep).
--
-- Reading @P(x = s)@ off a neural network's @[B, n]@ logit tensor over an
-- integer domain is sometimes compiled (e.g. by the per-mask variant of
-- @(a, a == b)@ for the query @(s, ANY)@) as a sum with one term per domain
-- value:
--
-- > (if k0 == s then raw[j0] else 0.0) + (if k1 == s then raw[j1] else 0.0) + ...
--
-- In the batched backend every arm of that sum is an eager @torch.where@ over
-- the whole batch, so the read costs O(V) tensor ops and O(V) source (CPython
-- parses it only because 'SPLL.PythonNesting' spills the V-deep nesting into
-- temporaries). When the keys are distinct and contiguous and every term reads
-- the slot at the same offset from its key (@j_i - k_i = c@), at most one term
-- is non-zero, and the sum is exactly
--
-- > if (k_min - 1 < s) && (s < k_max + 1) then raw[s + c] else 0.0
--
-- -- a single @nn_gather@ guarded by a range test, so a key outside the
-- domain still contributes the zero it did before ('nn_gather' clamps, so
-- the masked-off read is in bounds). Measured on the corpus pin at V = 1000:
-- the variant's forward goes from ~17-26 ms to ~0.06-0.09 ms per call (B = 1
-- and B = 1000), and the module from 107 KB to 37 KB.
--
-- The pattern is matched on the whole @+@-tree only (every leaf must be such
-- a term), and only in the linear semiring's spelling (a 'VFloat' zero and
-- 'OpPlus'); anything else is left untouched, so IR that does not hit the
-- pattern is unchanged byte for byte. The key expression must be a variable
-- or an accessor chain over one: it is now read three times instead of V, and
-- this keeps that trivially pure and cheap.
module SPLL.IRGatherPass
  ( gatherPassEnv
  , gatherPassExpr
  , isGatheredRead
  , usesOneHotGather
  ) where

import Data.List (sort)

import SPLL.IntermediateRepresentation
import SPLL.IR.Value (GenericValue(..))

-- | Run the rewrite over every variant of every function group.
gatherPassEnv :: IREnv -> IREnv
gatherPassEnv (IREnv groups adts globals) =
  IREnv (map onGroup groups) adts globals
  where
    onGroup g = g
      { genFun   = fmap onBody (genFun g)
      , probFun  = fmap onBody (probFun g)
      , integFun = fmap onBody (integFun g)
      , writeLogitsFun = fmap onBody (writeLogitsFun g)
      , normalFun = fmap onBody (normalFun g)
      }
    onBody (body, doc) = (gatherPassExpr body, doc)

-- | Top-down: the outermost @+@ of a chain is tried first, so the whole chain
-- is matched rather than its innermost suffix.
gatherPassExpr :: IRExpr -> IRExpr
gatherPassExpr e@(IROp OpPlus _ _)
  | Just e' <- oneHotRead e = e'
gatherPassExpr e = irDescend gatherPassExpr e

-- | One term: @(key, slot, tensor, index expression)@.
oneHotTerm :: IRExpr -> Maybe (Int, Int, IRExpr, IRExpr)
oneHotTerm t = case t of
  IRIf c r z   -> go c r z
  IRSelect c r z -> go c r z
  _ -> Nothing
  where
    go c (IRBuiltin BListIndex [raw, IRConst (VInt j)]) (IRConst (VFloat 0.0)) =
      case c of
        IROp OpEq (IRConst (VInt k)) x | simpleKey x -> Just (k, j, raw, x)
        IROp OpEq x (IRConst (VInt k)) | simpleKey x -> Just (k, j, raw, x)
        _ -> Nothing
    go _ _ _ = Nothing

simpleKey :: IRExpr -> Bool
simpleKey (IRVar _)        = True
simpleKey (IRDestruct _ x) = simpleKey x
simpleKey _                = False

plusLeaves :: IRExpr -> [IRExpr]
plusLeaves (IROp OpPlus a b) = plusLeaves a ++ plusLeaves b
plusLeaves e                 = [e]

oneHotRead :: IRExpr -> Maybe IRExpr
oneHotRead e = do
  terms@((_, _, raw, x) : _) <- mapM oneHotTerm (plusLeaves e)
  let keys = sort [k | (k, _, _, _) <- terms]
  (lo : _) <- Just keys
  off : offs <- Just [j - k | (k, j, _, _) <- terms]
  let hi = lo + length keys - 1
  if all (\(_, _, r, y) -> r == raw && y == x) terms
       && all (== off) offs
       && keys == [lo .. hi]
    then Just (gatheredRead raw x lo hi off)
    else Nothing

-- | The rewrite's output: @raw[x + off]@ for @lo <= x <= hi@, else 0.0.
gatheredRead :: IRExpr -> IRExpr -> Int -> Int -> Int -> IRExpr
gatheredRead raw x lo hi off =
      let idx | off == 0  = x
              | otherwise = IROp OpPlus x (IRConst (VInt off))
          inRange = IROp OpAnd (IROp OpLessThan (IRConst (VInt (lo - 1))) x)
                               (IROp OpLessThan x (IRConst (VInt (hi + 1))))
      in IRIf inRange (IRBuiltin BListIndex [raw, idx]) (IRConst (VFloat 0.0))

-- | Is this node a read 'gatherPassExpr' produced? Recognised by its exact
-- shape, so the test corpus census can label a module that carries one (the
-- fuzz arms never build a one-hot sum wide enough to be rewritten).
isGatheredRead :: IRExpr -> Bool
isGatheredRead e = case e of
  IRIf (IROp OpAnd (IROp OpLessThan (IRConst (VInt lo1)) x) (IROp OpLessThan x' (IRConst (VInt hi1))))
       (IRBuiltin BListIndex [raw, idx]) (IRConst (VFloat 0.0))
    | x == x', simpleKey x, lo1 < hi1 - 1 ->
        let off = case idx of
              IROp OpPlus _ (IRConst (VInt c)) -> c
              _ -> 0
        in e == gatheredRead raw x (lo1 + 1) (hi1 - 1) off
  _ -> False

-- | Does some probability or integrate body of the environment carry a
-- 'gatherPassExpr' read?
usesOneHotGather :: IREnv -> Bool
usesOneHotGather (IREnv groups _ _) =
  any (any (anyNode . fst)) (concatMap (\g -> [probFun g, integFun g]) groups)
  where anyNode n = isGatheredRead n || any anyNode (getIRSubExprs n)
