-- | Pure helpers over 'IRExpr' (free variables, let-chain surgery, renaming,
-- substitution, node counts) that the frontend's IR compiler uses and that
-- read nothing but the IR. Moved out of @SPLL.IRCompiler@ (task
-- ircompiler-leaf-extractions).
module SPLL.IRUtil
  ( irNodeCount
  , irLogicNodeCount
  , pruneDeadLetIns
  , freeInIR
  , flattenLetIns
  , buildLetIns
  , hoistInvariantBindings
  , splitHoistable
  , renameVar
  , renameVar'
  , substIRVar
  , irSqrt
  ) where

import SPLL.IntermediateRepresentation
import SPLL.IR.Value

-- | Node count of an IR expression, for the unrolling-size budget above.
irNodeCount :: IRExpr -> Int
irNodeCount e = 1 + sum (map irNodeCount (getIRSubExprs e))

-- | 'irNodeCount' with every literal-data subtree counted as one node: the
-- per-copy size 'pointQueryTable' gates a leaf on. A literal (constants,
-- constructors and tensors built only of literals) is the same in every
-- per-value copy of a leaf, so the optimizer's CSE binds it once for the whole
-- table; its node count measures the size of an enumeration DOMAIN, not of the
-- leaf's logic. The case that needed this (task
-- batched-count-chain-enumeration-factorial): a neural ADT read under a
-- predicate, @match (readAttrs s)@, enumerates the 97 values of its @Attrs@
-- domain, and that tensor literal was 98 of the leaf's 138 folded nodes -- over
-- 'maxTabulatedLeafNodes' with a 40-node body, so the table was declined and
-- an n-slot count chain went factorial under @--batched@. Does not bear on the
-- cardinality budget, which still counts every node.
irLogicNodeCount :: IRExpr -> Int
irLogicNodeCount e
  | isLiteralData e = 1
  | otherwise       = 1 + sum (map irLogicNodeCount (getIRSubExprs e))
  where
    isLiteralData (IRConst _)                    = True
    isLiteralData (IRConstruct _ es)             = all isLiteralData es
    isLiteralData (IRBuiltin (BTensor _) es)     = all isLiteralData es
    isLiteralData _                              = False

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

-- | True if the given variable name appears free in an IR expression.
freeInIR :: String -> IRExpr -> Bool
freeInIR v (IRVar v')           = v == v'
freeInIR v (IRLetIn n val irBody) = freeInIR v val || (v /= n && freeInIR v irBody)
freeInIR v (IRLambda n irBody)    = v /= n && freeInIR v irBody
freeInIR v (IRApply f a)        = freeInIR v f  || freeInIR v a
freeInIR v (IROp _ a b)         = freeInIR v a  || freeInIR v b
freeInIR v (IRUnaryOp _ e)      = freeInIR v e
freeInIR v (IRIf c a b)         = freeInIR v c  || freeInIR v a  || freeInIR v b
freeInIR v (IRConstruct _ args) = any (freeInIR v) args
freeInIR v (IRDestruct _ a)     = freeInIR v a
-- Every builtin, over all its arguments. This arm is deliberately generic:
-- 'BMapList'/'BListIndex' once had one each, and the tensor builtins had none
-- at all -- so a variable free inside a 'BMap' body was answered "not free"
-- by the catch-all below. That was latent rather than harmless: 'freeInIR' is
-- what 'pruneDeadLetIns' asks before dropping a binding, so a wrong "no"
-- deletes a binding the loop body still reads. It only ever fired on the
-- max-product semiring, whose enumerated reduction was the one built in
-- tensor form; task retire-irenumsum put EVERY enumerated reduction in that
-- form, which would have made it the common case. A binder inside a builtin
-- is always an 'IRLambda' argument, and that arm above already excludes it.
freeInIR v (IRBuiltin _ args)   = any (freeInIR v) args
freeInIR v (IRDensity _ _ x)    = freeInIR v x
freeInIR v (IRCumulative _ _ x) = freeInIR v x
freeInIR v (IRIsPossible _ x)   = freeInIR v x
freeInIR _ _                    = False

-- | Flatten all leading IRLetIn bindings into a list, returning the core expression.
flattenLetIns :: IRExpr -> ([(String, IRExpr)], IRExpr)
flattenLetIns (IRLetIn n v irBody) = let (rest, core) = flattenLetIns irBody in ((n, v) : rest, core)
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

-- | Split a guarded scope's bindings into those that may be evaluated outside
-- the guard and those that must stay under it. A binding may leave when it is
-- pure ('isPure': no draw, no generator reference) and mentions none of the
-- @blocked@ names -- the loop variables and every name bound per iteration --
-- nor any binding that stays behind. Both sublists keep their relative order,
-- so the leaving prefix is well-scoped on its own.
--
-- This is 'hoistInvariantBindings' for bindings a guard has already wrapped,
-- where the free-variable test alone is not enough: leaving the guard moves
-- evaluation from "only in cells that pass" to "unconditionally", which is
-- sound for a pure expression that cannot observe the guard's variables, and
-- would re-order or fuse draws for an impure one.
splitHoistable :: [String] -> [(String, IRExpr)] -> ([(String, IRExpr)], [(String, IRExpr)])
splitHoistable = go
  where
    go _ [] = ([], [])
    go blocked ((n, v) : rest)
      | isPure v && not (any (`freeInIR` v) blocked) =
          let (out, stay) = go blocked rest in ((n, v) : out, stay)
      | otherwise =
          let (out, stay) = go (n : blocked) rest in (out, (n, v) : stay)

renameVar :: String -> String -> IRExpr -> IRExpr
renameVar old new = irMap (renameVar' old new)

renameVar' :: String -> String -> IRExpr -> IRExpr
renameVar' old new (IRVar n) | n == old = IRVar new
renameVar' _ _ x = x

-- | Substitutes every occurrence of the IR variable @n@ with @val@. Not
-- capture-avoiding -- fine here, where it is only ever used to eliminate the
-- single free variable of a small inverse-witness template built from a
-- globally-unique "astN" chain name, never shadowed by a nested binder.
substIRVar :: String -> IRExpr -> IRExpr -> IRExpr
substIRVar n val = irMap (\e -> case e of { IRVar n' | n' == n -> val; _ -> e })

irSqrt :: IRExpr -> IRExpr
irSqrt x = IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog x))
