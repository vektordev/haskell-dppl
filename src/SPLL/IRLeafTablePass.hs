-- | Batched-only: tabulate a neural leaf decode that an enumeration loop
-- re-evaluates once per world (task
-- batched-enumeration-rereads-neural-leaf-per-world).
--
-- A program that draws several neural reads and branches on them,
--
-- > main a b c d = draw x1 = readMNist(a) in .. draw x4 = readMNist(d) in
-- >   if x1 < x2 then (if x2 < x3 then x3 < x4 else False) else False
--
-- compiles to nested enumeration loops whose bodies read each draw's mass at
-- the loop variable:
--
-- > map (\x1 -> .. map (\x4 -> .. * AcFst (readMNist_auto_prob(raw_d)(x4))) [0..9] ..) [0..9]
--
-- The decode @readMNist_auto_prob(raw_d)(x4)@ depends only on @x4@ and on
-- @raw_d@, which is bound outside every loop, yet it sits in the innermost
-- body and so runs 10^4 times -- 10^4 + 10^3 + 10^2 + 10 decodes over the
-- four reads, for 40 distinct values. Under @--batched@ each decode is a
-- method call, a membership test, a gather and a select over the whole batch,
-- and every arm of a select is eager, so all of them run (the scalar backend's
-- lazy ternary skips the ones a false condition guards). This pass computes
-- the decode once per domain value, ahead of the outermost loop it does not
-- depend on, and reads the table by position inside the loop:
--
-- > let l_leaftbl_0 = map (\l_leafv_0 -> AcFst (readMNist_auto_prob(raw_d)(l_leafv_0))) [0..9] in
-- > map (\x1 -> .. map (\x4 -> .. * index l_leaftbl_0 x4) [0..9] ..) [0..9]
--
-- The rewrite is exact. A read-logits decode is pure and total on its own
-- domain (a gather from the network's output; 'SPLL.AutoNeural'), so
-- evaluating it at every domain value, including worlds a select would have
-- discarded, changes no value: the table holds the same numbers the loop
-- computed, and the index reads the one the loop variable names. The table
-- is bound immediately around the outer loop, so it is evaluated exactly when
-- that loop is: a guard above the loop still guards it.
--
-- Matched narrowly, so anything else is left untouched byte for byte:
--
--   * the decode is @AcFst (f(r)(w))@ with @f@ a network's @_auto_prob@
--     function and @r@ a variable bound outside the outer loop;
--   * @w@ is the variable of a loop nested strictly inside the outer loop,
--     over a literal domain of contiguous ascending integers (the index is
--     then @w - lo@, a plain integer in every row);
--   * the outer loop is a 'BMap' over any domain.
--
-- A decode at the outer loop's own variable gains nothing at that loop and is
-- left for a loop enclosing it, if any; the outermost loop's own decode runs
-- once per value already.
module SPLL.IRLeafTablePass
  ( leafTablePassEnv
  , leafTablePassExpr
  ) where

import Control.Monad.State.Strict
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import SPLL.IntermediateRepresentation
import SPLL.IROptimizer (allNamesIR)
import SPLL.IR.Value (GenericValue(..))
import SPLL.ReservedNames (neuralReadLogitsSuffix)

-- | Run the rewrite over the probability and integrate bodies of every
-- function group. @neurals@ are the program's neural declaration names.
leafTablePassEnv :: Set.Set String -> IREnv -> IREnv
leafTablePassEnv neurals (IREnv groups adts globals) =
  IREnv (map onGroup groups) adts globals
  where
    onGroup g = g
      { probFun  = fmap onBody (probFun g)
      , integFun = fmap onBody (integFun g)
      }
    onBody (body, doc) = (leafTablePassExpr decoders body, doc)
    decoders = Set.map (\n -> n ++ neuralReadLogitsSuffix ++ "_prob") neurals

-- | The rewrite on one body, with @decoders@ the @_auto_prob@ function names.
leafTablePassExpr :: Set.Set String -> IRExpr -> IRExpr
leafTablePassExpr decoders body
  | Set.null decoders = body
  | otherwise = evalState (go body) 0
  where
    taken = allNamesIR body

    fresh :: String -> State Int String
    fresh base = do
      i <- get
      put (i + 1)
      let n = base ++ show i
      if n `Set.member` taken then fresh base else return n

    go :: IRExpr -> State Int IRExpr
    go e@(IRBuiltin BMap [IRLambda v loopBody, _]) =
      case nub (decodes v loopBody) of
        [] -> irDescendM go e
        keys -> do
          named <- mapM (\k -> (,) k <$> fresh "l_leaftbl_") keys
          tables <- mapM (\(k, t) -> (,) t <$> table k) named
          let rewritten = replaceDecodes (Map.fromList named) e
          inner <- irDescendM go rewritten
          return (foldr (\(t, tbl) acc -> IRLetIn t tbl acc) inner tables)
    go e = irDescendM go e

    table :: Key -> State Int IRExpr
    table (f, r, (lo, n)) = do
      x <- fresh "l_leafv_"
      return (IRBuiltin BMap
        [ IRLambda x (decodeAt f r (IRVar x))
        , IRBuiltin (BTensor [EFixed n]) [IRConst (VInt k) | k <- [lo .. lo + n - 1]] ])

    -- The decodes inside an outer loop over @v@ that this pass tabulates: at
    -- the variable of a loop nested inside it, reading a raw output bound
    -- outside it.
    decodes :: String -> IRExpr -> [Key]
    decodes v loopBody =
      [ (f, r, dom)
      | (f, r, w) <- decodeSites loopBody
      , w /= v
      , Just dom <- [Map.lookup w loops]
      , not (r `Set.member` bound) ]
      where
        loops = innerLoops loopBody
        bound = Set.insert v (binders loopBody)

    decodeSites :: IRExpr -> [(String, String, String)]
    decodeSites e = case e of
      IRDestruct AcFst (IRApply (IRApply (IRVar f) (IRVar r)) (IRVar w))
        | f `Set.member` decoders -> [(f, r, w)]
      _ -> concatMap decodeSites (getIRSubExprs e)

    -- Every loop variable in the tree whose loop ranges over a literal
    -- domain of contiguous ascending integers, with that domain. A variable
    -- bound more than once is dropped: its domain would be ambiguous.
    innerLoops :: IRExpr -> Map.Map String (Int, Int)
    innerLoops e = Map.fromList [ (w, d) | (w, Just d) <- all', count w == 1 ]
      where
        all' = loopsOf e
        count w = length (filter ((== w) . fst) all')
        loopsOf x = here x ++ concatMap loopsOf (getIRSubExprs x)
        here (IRBuiltin BMap [IRLambda w _, dom]) = [(w, contiguous dom)]
        here _ = []

    replaceDecodes :: Map.Map Key String -> IRExpr -> IRExpr
    replaceDecodes named (IRBuiltin BMap [IRLambda v loopBody, dom]) =
      IRBuiltin BMap [IRLambda v (irMap rep loopBody), dom]
      where
        loops = innerLoops loopBody
        rep x = case x of
          IRDestruct AcFst (IRApply (IRApply (IRVar f) (IRVar r)) (IRVar w))
            | Just d <- Map.lookup w loops
            , Just t <- Map.lookup (f, r, d) named ->
                IRBuiltin (BIndex 0) [IRVar t, position w d]
          _ -> x
    replaceDecodes _ e = e

type Key = (String, String, (Int, Int))

decodeAt :: String -> String -> IRExpr -> IRExpr
decodeAt f r x = IRDestruct AcFst (IRApply (IRApply (IRVar f) (IRVar r)) x)

-- | The table position of loop value @w@ over the domain @[lo ..]@.
position :: String -> (Int, Int) -> IRExpr
position w (0, _)  = IRVar w
position w (lo, _) = IROp OpSub (IRVar w) (IRConst (VInt lo))

-- | @(lo, n)@ when the domain is the literal @[lo, lo + 1 .. lo + n - 1]@.
contiguous :: IRExpr -> Maybe (Int, Int)
contiguous (IRBuiltin (BTensor [EFixed n]) cs)
  | Just ks@(lo : _) <- mapM intConst cs, ks == [lo .. lo + n - 1] = Just (lo, n)
  where
    intConst (IRConst (VInt k)) = Just k
    intConst _ = Nothing
contiguous _ = Nothing

-- | Every name a lambda or let binds anywhere in the tree.
binders :: IRExpr -> Set.Set String
binders e = here e `Set.union` Set.unions (map binders (getIRSubExprs e))
  where
    here (IRLambda n _)  = Set.singleton n
    here (IRLetIn n _ _) = Set.singleton n
    here _               = Set.empty
