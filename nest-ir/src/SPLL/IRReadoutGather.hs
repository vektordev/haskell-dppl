-- | The scalar Python backend's readout gather (task
-- scalar-backend-tensor-ops-lower-to-torch).
--
-- An enumeration that needs a categorical's probability at every value of its
-- domain -- the agreement fusion's two marginal vectors, @pa@ and @pb@ --
-- compiles to a 'BMap' of the reader's probability function over the domain:
--
-- > map (\v -> AcFst (camNN_auto_prob(raw)(v))) over [0, 1, .., V-1]
--
-- which the scalar backend emits as one Python call per domain value. Inlined,
-- with the two facts the map itself establishes -- @v@ is a concrete Int, so
-- not ANY, and every domain value lies in the reader's declared domain, so its
-- membership guard holds -- the reader's body reduces to a read of one slot of
-- the network's output vector, @raw[v + c]@. Over a contiguous domain that map
-- is a slice of the vector, which the backend emits as one 'vec_slice' call:
-- a list slice, or a tensor view that keeps the autograd graph.
--
-- The rewrite is all or nothing per map. It fires only when the inlined body
-- reduces /exactly/ to such a read; anything else (a log-space reader, a
-- Gaussian, an ADT payload, a domain that is not contiguous or not wholly
-- inside the reader's) leaves the map, call and all, as it was. What it keeps
-- is a read the call would have made, with only constant-folded guards
-- dropped, so the slice's elements are the call's values, bit for bit.
--
-- It runs on the scalar backend's input only. The other backends never see
-- it: the batched backend's own gather pass ('SPLL.IRGatherPass') covers its
-- side, and Julia has its own tensor story.
module SPLL.IRReadoutGather
  ( gatherReadoutsEnv
  , gatherSlice
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

import SPLL.IntermediateRepresentation
import SPLL.IROptimizer (postProcess, OptimizerConfig(..), defaultOptimizerConfig)
import SPLL.IR.Value

-- | Rewrite every eligible readout map in every function of the environment.
gatherReadoutsEnv :: IREnv -> IREnv
gatherReadoutsEnv (IREnv funcs adts consts) = IREnv (map onGroup funcs) adts consts
  where
    probs = Map.fromList [ (groupName g ++ "_prob", e) | g <- funcs, Just (e, _) <- [probFun g] ]
    onGroup g = g { genFun = onDecl <$> genFun g
                  , probFun = onDecl <$> probFun g
                  , integFun = onDecl <$> integFun g
                  , writeLogitsFun = onDecl <$> writeLogitsFun g
                  , normalFun = onDecl <$> normalFun g }
    onDecl (e, doc) = (rewrite probs e, doc)

-- | The rewrite on one body, followed by dropping the domain literals it left
-- unread.
rewrite :: Map.Map Varname IRExpr -> IRExpr -> IRExpr
rewrite probs e0 = let e1 = go Map.empty e0 in if e1 == e0 then e0 else dropDeadDomains e1
  where
    go env e = case e of
      IRLetIn x val body ->
        let val' = go env val
            env' = maybe (Map.delete x env) (\d -> Map.insert x d env) (intDomain env val')
        in IRLetIn x val' (go env' body)
      IRLambda x body -> IRLambda x (go (Map.delete x env) body)
      IRBuiltin BMap [IRLambda v body, dom]
        | Just ints <- intDomain env dom
        , Just _ <- contiguous ints
        , Just body' <- readout probs v ints body ->
            IRBuiltin BMap [IRLambda v body', domainLiteral ints]
      _ -> irDescend (go env) e

-- | The values of a constant Int domain, seen through let-bound names.
intDomain :: Map.Map Varname [Int] -> IRExpr -> Maybe [Int]
intDomain env e = case e of
  IRVar x -> Map.lookup x env
  IRBuiltin (BTensor sh) es | shapeRank sh == 1 -> mapM constInt es
  IRBuiltin (BIota sh) [] | shapeRank sh == 1 -> Just [0 .. shapeNumel sh - 1]
  IRConst (VTensor sh vs) | shapeRank sh == 1 -> mapM valInt vs
  _ -> Nothing
  where
    constInt (IRConst v) = valInt v
    constInt _ = Nothing
    valInt (VInt i) = Just i
    valInt _ = Nothing

domainLiteral :: [Int] -> IRExpr
domainLiteral ints = IRBuiltin (BTensor [EFixed (length ints)]) (map (IRConst . VInt) ints)

-- | @(lo, n)@ when the values are @lo, lo+1, .., lo+n-1@, @n >= 1@.
contiguous :: [Int] -> Maybe (Int, Int)
contiguous ints@(lo : _) | ints == [lo .. lo + length ints - 1] = Just (lo, length ints)
contiguous _ = Nothing

-- | The inlined, reduced body of @AcFst (f(args..)(v))@, when it is a gather.
readout :: Map.Map Varname IRExpr -> Varname -> [Int] -> IRExpr -> Maybe IRExpr
readout probs v ints (IRDestruct AcFst call)
  | (IRVar f, args@(_ : _)) <- collectApplyChain call
  , last args == IRVar v
  , not (any (mentions v) (init args))
  , Just callee <- Map.lookup f probs
  , (params, body) <- lambdas callee
  , length params == length args
  -- No binder inside the callee may capture a name an argument reads.
  , Set.null (binders body `Set.intersection` Set.unions (map freeVars args))
  , let inlined = IRDestruct AcFst (subst (Map.fromList (zip params args)) body)
        reduced = postProcess quiet (project (postProcess quiet (facts inlined)))
  , Just _ <- gatherOf v reduced
  = Just reduced
  where
    quiet = defaultOptimizerConfig { optVerbose = 0, optShowStats = False }
    domain = Set.fromList ints
    facts = irMap fact
    fact (IRUnaryOp OpIsAny (IRVar x)) | x == v = IRConst (VBool False)
    fact (IRIsPossible (MultiDiscretes vals) (IRVar x))
      | x == v, domain `Set.isSubsetOf` Set.fromList [ i | VInt i <- vals ] = IRConst (VBool True)
    fact x = x
    -- The optimizer does not move a projection into a let's body, which is
    -- where the reader's result tuple sits; after this, the let is a
    -- single-use binding the second optimizer run inlines.
    project = irMap proj
    proj (IRDestruct AcFst (IRLetIn x a b)) = IRLetIn x a (proj (IRDestruct AcFst b))
    proj (IRDestruct AcFst (IRConstruct TgTuple [a, _])) = a
    proj x = x
readout _ _ _ _ = Nothing

-- | @(x, c)@ when the map body reads @x[v + c]@ with @x@ a name the loop does
-- not bind.
gatherOf :: Varname -> IRExpr -> Maybe (Varname, Int)
gatherOf v e = case e of
  IRBuiltin BListIndex [IRVar x, idx] | x /= v -> (,) x <$> offset idx
  IRBuiltin (BIndex 0) [IRVar x, idx] | x /= v -> (,) x <$> offset idx
  _ -> Nothing
  where
    offset (IRVar y) | y == v = Just 0
    offset (IROp OpPlus (IRVar y) (IRConst (VInt c))) | y == v = Just c
    offset (IROp OpPlus (IRConst (VInt c)) (IRVar y)) | y == v = Just c
    offset (IROp OpSub (IRVar y) (IRConst (VInt c))) | y == v = Just (negate c)
    offset _ = Nothing

-- | A map the backend emits as a slice: @(x, lo, hi)@ for
-- @map (\v -> x[v + c]) over [a .. a+n-1]@, reading @x[a+c .. a+c+n-1]@.
gatherSlice :: IRExpr -> Maybe (Varname, Int, Int)
gatherSlice (IRBuiltin BMap [IRLambda v body, dom])
  | Just ints <- intDomain Map.empty dom
  , Just (lo, n) <- contiguous ints
  , Just (x, c) <- gatherOf v body
  -- A negative position is Python's read from the end, which a slice does
  -- not reproduce; such a map keeps its (inlined) comprehension.
  , lo + c >= 0
  = Just (x, lo + c, lo + c + n)
gatherSlice _ = Nothing

-- | Drop a let whose value is a constant domain literal no one reads any more.
dropDeadDomains :: IRExpr -> IRExpr
dropDeadDomains = irMap drop1
  where
    drop1 (IRLetIn x val body)
      | Just _ <- intDomain Map.empty val, not (mentions x body) = body
    drop1 e = e

lambdas :: IRExpr -> ([Varname], IRExpr)
lambdas (IRLambda x b) = let (xs, b') = lambdas b in (x : xs, b')
lambdas e = ([], e)

-- | Simultaneous substitution of free variables. The caller has ruled out
-- capture.
subst :: Map.Map Varname IRExpr -> IRExpr -> IRExpr
subst m e
  | Map.null m = e
  | otherwise = case e of
      IRVar x -> fromMaybe e (Map.lookup x m)
      IRLetIn x val body -> IRLetIn x (subst m val) (subst (Map.delete x m) body)
      IRLambda x body -> IRLambda x (subst (Map.delete x m) body)
      _ -> irDescend (subst m) e

freeVars :: IRExpr -> Set.Set Varname
freeVars e = case e of
  IRVar x -> Set.singleton x
  IRLetIn x val body -> freeVars val `Set.union` Set.delete x (freeVars body)
  IRLambda x body -> Set.delete x (freeVars body)
  _ -> Set.unions (map freeVars (getIRSubExprs e))

binders :: IRExpr -> Set.Set Varname
binders e = case e of
  IRLetIn x val body -> Set.insert x (binders val `Set.union` binders body)
  IRLambda x body -> Set.insert x (binders body)
  _ -> Set.unions (map binders (getIRSubExprs e))

mentions :: Varname -> IRExpr -> Bool
mentions x = Set.member x . freeVars
