module SPLL.Typing.ForwardChaining where

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import Control.Monad.Supply

import Data.List (delete, find, maximumBy, intersect, nub, (\\))
import Data.Maybe
import Debug.Trace (trace, traceShowId)
import Data.Bifunctor(second)
import Control.Monad.State.Lazy (StateT, State, runState, runStateT, get, put)
import PredefinedFunctions
import SPLL.IntermediateRepresentation
import Data.PartialOrd (minima)
import Data.Foldable
type Chain a = SupplyT Int (State [(String, ChainName)]) a
type ChainInferState a = ([[HornClause]], [HornClause])

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

addChainName :: ChainName -> Expr -> TypeInfo
addChainName s e = setChainName (getTypeInfo e) s

getChainName :: Expr -> ChainName
getChainName = chainName . getTypeInfo

--Give each node on the AST a chainName first. Then annotate the value clauses of the LetIns correctly, as this cannot be done in the first step
annotateSyntaxTree :: Expr -> Chain Expr
annotateSyntaxTree expr = do
  annotatedExprs <- do
    tMapM (\e -> do
      idx <- demand   -- idx may be unused due to multiple usages of the same variable
      idx2 <- demand  -- Complete waste of integers, but required for LetIn Blocks. TODO Find a better solution
      let name = "astNode" ++ show idx
      let name2 = "astNode" ++ show idx2
      case e of
        (LetIn _ varName val bound) -> lift $ do
          state <- get
          case lookup varName state of
            Just cn -> error $ "Variable name in LetIn is already in declared: " ++varName
            Nothing -> do
              put ((varName, name2):state)
              return (addChainName name e)
        (Var _ varName) -> lift $ do
          state <- get
          case lookup varName state of
            Just cn -> return $ addChainName cn e
            Nothing -> error $ "Variable name in var is unknown: " ++ varName
        _ -> return $ addChainName name e
      ) expr
  setLetInChainNames annotatedExprs

setLetInChainNames :: Expr -> Chain Expr
setLetInChainNames e@(LetIn t n v b) = lift $ do
  state <- get
  let Just correctChainName = lookup n state
  let updatedVal = tMapHead (\ex -> setChainName (getTypeInfo ex) correctChainName) v
  return $ LetIn t n updatedVal b
setLetInChainNames e = return e

annotateChainNamesProg :: Program -> Chain Program
annotateChainNamesProg (Program decls nns) = do
  declsAn <- Prelude.mapM (\(n, ex) -> do
    exAn <- annotateSyntaxTree ex
    return (n, exAn)) decls
  return $ Program declsAn nns

inferProg :: Program -> Program
inferProg p = Program finishedDecls nns
  where
    (annotatedProg, _) = runState (runSupplyT (annotateChainNamesProg p) (+1) 1) []
    Program declsAn nns = annotatedProg
    annotatedExprs = Prelude.map snd declsAn
    startDetVars = concatMap findDeterminism annotatedExprs
    detVarHornClauses = map (\dv -> case dv of
      (n, Nothing) -> HornClause [] [(n, CDeterministic)] (n, Stub StubConstant, 0)
      (n, Just v) -> HornClause [] [(n, CDeterministic)] (n, AnnotValueStub StubConstant v, 0)) startDetVars
    hornClauses = concatMap constructHornClauses annotatedExprs
    startExprName = chainName $ getTypeInfo (head annotatedExprs)
    startClause = HornClause [] [(startExprName, CInferDeterministic)] (startExprName, Stub StubConstant, 0)
    finishedState = fixpointIteration (hornClauses, startClause:detVarHornClauses)
    finishedDecls = Prelude.map (Data.Bifunctor.second (tMap (annotateMaximumCType finishedState))) declsAn


annotateMaximumCType :: ChainInferState a -> Expr -> TypeInfo
annotateMaximumCType (_, used) e = t {cType=ct, derivingHornClause=hc}
  where
    t = getTypeInfo e
    cn = chainName t
    cmpHC (HornClause _ res1 _) (HornClause _ res2 _)  =
      let cn1 = fromMaybe CNotSetYet (lookup cn res1)
          cn2 = fromMaybe CNotSetYet (lookup cn res2) in
            compare cn1 cn2
    maxHC = maximumBy cmpHC used
    maxCT = lookup cn ((\(HornClause _ b _ )-> b) maxHC)
    ct = fromMaybe CBottom maxCT
    hc = if isNothing maxCT then Nothing else Just maxHC


constructHornClause :: Expr -> [HornClause]
constructHornClause e = case e of
  Not _ a -> rotatedHornClauses (HornClause [(getChainName a, CInferDeterministic)]  [(getChainName e, CInferDeterministic)] (getChainName e, Stub StubNot, 0))
  -- The bound expression is det if the
  LetIn _ _ v b -> [HornClause [(getChainName b, CInferDeterministic)]  [(getChainName e, CInferDeterministic)] (getChainName e, Stub StubLetIn, 0), HornClause [(getChainName e, CInferDeterministic)]  [(getChainName b, CInferDeterministic)] (getChainName e, Stub StubLetIn, 1)]
  InjF {} -> getHornClause e
  _ -> []

constructHornClauses ::  Expr -> [[HornClause]]
constructHornClauses e = constructHornClause e:concatMap constructHornClauses (getSubExprs e)

-- TODO Constrained Hornclauses
-- Takes one horn clause on constructs all inverses, including the original
rotatedHornClauses :: HornClause -> [HornClause]
rotatedHornClauses clause@(HornClause cond res (cn, stub, i)) | i == 0 =
  case (cond, res) of
    ([a], [b]) -> [clause, HornClause [b] [a] (cn, stub, 1)]
    ([a, b], [c]) -> [clause, HornClause [c, a] [b] (cn, stub, 1), HornClause [c, b] [a] (cn, stub, 2)]
    ([a, b], [c, d]) ->
      [clause, HornClause [a, c] [b, d] (cn, stub, 1),
        HornClause [a, d] [b, c] (cn, stub, 2),
        HornClause [b, c] [a, d] (cn, stub, 3),
        HornClause [b, d] [a, c] (cn, stub, 4),
        HornClause [c, d] [a, b] (cn, stub, 5)] --TODO is this a good order
    _ -> [clause]
rotatedHornClauses _ = error "Trying to rotate inversion of a Horn clause"

findFulfilledHornClause :: [[HornClause]] -> [(ChainName, CType)] -> Maybe HornClause
--findFulfilledHornClause clauses satisfied | trace (show satisfied) False = undefined
findFulfilledHornClause clauses satisfied = find allSatisfied (concat clauses)
  where
    allSatisfied (HornClause cond _ _) = foldr (\(name, exp) b -> b && cTypeOf name >= exp) True cond
    cTypeOf name = fromMaybe CNotSetYet (lookup name satisfied)


findDeterminism :: Expr -> [(ChainName, Maybe Value)]
findDeterminism (Constant t v) = [(chainName t, Just v)]
findDeterminism (ThetaI t _ _) = [(chainName t, Nothing)]
findDeterminism e = concatMap findDeterminism (getSubExprs e)

-- To the person that wants to implement weaker CTypes:
--  Note that this method uses the implied CType of the used HornClauses to infer the type of each variable
--  Therefor if you want to continue using this method you need to downgrade the CTypes in the used HornClauses
stepIteration :: ChainInferState a -> ChainInferState a
stepIteration (clauses, used) =
  if isJust nextClause then
    (delete (fromJust (find (elem (fromJust nextClause)) clauses)) clauses, fromJust nextClause:used)
  else
    (clauses, used)
  where nextClause = findFulfilledHornClause clauses (determinedCTypes used)

determinedCTypes :: [HornClause] -> [(ChainName, CType)]
determinedCTypes = concatMap (\(HornClause _ b _) -> b)

fixpointIteration :: ChainInferState a -> ChainInferState a
fixpointIteration (clauses, used) = if newDetVars == detVars
    then res
    else fixpointIteration (newClauses, newUsed)
  where
    res@(newClauses, newUsed) = stepIteration (clauses, used)
    detVars = determinedCTypes used
    newDetVars = determinedCTypes newUsed

  -- =========================================================================
  -- WORK IN PROGRESS
  -- =========================================================================

newtype Inversion a = Inversion (ChainName, IRExpr) deriving (Show, Eq)
{-
inferProbProg :: Program -> IRExpr
inferProbProg (Program [("main", main)] nns) = toInvExpr main
inferProbProg _  = error "Programs with function declarations are not yet implemented"
-}
--toInvExpr :: Expr -> IRExpr
-- Chain name of the outermost expression is the sample variable. Instead of naming it sample we just renamed the lambda to the outermost chain name 
--toInvExpr expr = IRLambda (chainName (getTypeInfo expr)) (inversionsToProb (exprToInversions expr))

inversionsToProb :: ([Inversion a], [IRExpr]) -> IRExpr
inversionsToProb (inversions, firstR:randoms) = Prelude.foldr (\(Inversion (cn, val)) body -> IRLetIn cn val body) randomsProduct inversions
  where randomsProduct = Prelude.foldr (\expr body -> IROp OpMult expr body) firstR randoms

exprToInversions :: Expr -> ([Inversion a], [IRExpr])
exprToInversions e = (mapMaybe hornClauseToIRExpr hcs, irs)
  where (hcs, irs) = combinedHornClauses e

combinedHornClauses :: Expr -> ([HornClause], [IRExpr])
combinedHornClauses e@(Uniform _) = (toList (derivingHornClause (getTypeInfo e)), [IRDensity IRUniform (IRVar (getChainName e))])
combinedHornClauses e@(Normal _) = (toList (derivingHornClause (getTypeInfo e)), [IRDensity IRNormal (IRVar (getChainName e))])
combinedHornClauses e = Prelude.foldr (\(a1, b1) (a, b) -> (nub (a1++a), b1++b)) ([], []) ((toList (derivingHornClause (getTypeInfo e)), []):Prelude.map combinedHornClauses (getSubExprs e))

hornClauseToIRExpr :: HornClause -> Maybe (Inversion a)
hornClauseToIRExpr hc@(HornClause pre _ (cn, stub, inversion)) = case stub of
  Stub StubLetIn | inversion == 0 -> return $ Inversion (cn, IRVar (preVars!!0))
  --Stub StubLetIn | inversion == 1 -> [Inversion (cn, IRVar (preVars!!0))] --FIXME This seems wrong?
  -- inversion 0 ist the forward pass. Inversion n is the n-1'th inverse pass
  AnnotStub StubInjF name | inversion == 0 -> do
    let Just (FPair fwdInjF _) = lookup name globalFenv
    let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) fwdInjF (zip (inputVars fwdInjF) preVars)
    return $ Inversion (cn, body renamedF)
  AnnotStub StubInjF name -> do
    let Just (FPair _ invInjF) = lookup name globalFenv
    let correctInv = invInjF !! (inversion - 1)
    let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
    return $ Inversion (cn, body renamedF)
  AnnotValueStub StubConstant v -> return $ Inversion (cn, IRConst (fmap (error "Cannot convert VClosure") v))
  Stub StubConstant -> Nothing
  _ -> error ("Found no way to invert expression: " ++ show hc)
  where
    preVars = map fst pre

chainVarOfSubExpr :: Expr -> Int -> IRExpr
chainVarOfSubExpr e n = IRVar (getChainName (getSubExprs e !! n))

topSortHornClauses :: [HornClause] -> [HornClause]
topSortHornClauses clauses =
  let maxC = minima clauses in
    maxC ++ topSortHornClauses (clauses \\ maxC)