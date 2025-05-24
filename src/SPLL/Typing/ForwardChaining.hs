module SPLL.Typing.ForwardChaining where

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import Control.Monad.Supply

import Data.List (delete, find, maximumBy, intersect, nub)
import Data.Maybe
import Debug.Trace (trace)
import Data.Bifunctor(second)
import Control.Monad.State.Lazy (StateT, State, runState, runStateT, get, put)
import PredefinedFunctions
import SPLL.IntermediateRepresentation
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
annotateChainNamesProg (Program decls nns adts) = do
  declsAn <- Prelude.mapM (\(n, ex) -> do
    exAn <- annotateSyntaxTree ex
    return (n, exAn)) decls
  return $ Program declsAn nns adts

inferProg :: Program -> Program
inferProg p = Program finishedDecls nns adts
  where
    (annotatedProg, _) = runState (runSupplyT (annotateChainNamesProg p) (+1) 1) []
    Program declsAn nns adts = annotatedProg
    annotatedExprs = Prelude.map snd declsAn
    startDetVars = concatMap findDeterminism annotatedExprs
    detVarHornClauses = map (\n -> ([], [(n, CDeterministic)], (StubConstant, 0))) startDetVars
    hornClauses = concatMap constructHornClauses annotatedExprs
    startExprName = chainName $ getTypeInfo (head annotatedExprs)
    startClause = ([],  [(startExprName, CInferDeterministic)], (StubConstant, 0))
    finishedState = fixpointIteration (hornClauses, startClause:detVarHornClauses)
    finishedDecls = Prelude.map (Data.Bifunctor.second (tMap (annotateMaximumCType finishedState))) declsAn
    

annotateMaximumCType :: ChainInferState a -> Expr -> TypeInfo
annotateMaximumCType (_, used) e = t {cType=ct, derivingHornClause=hc}
  where
    t = getTypeInfo e
    cn = chainName t
    cmpHC (_, res1, _) (_, res2, _) =
      let cn1 = fromMaybe CNotSetYet (lookup cn res1)
          cn2 = fromMaybe CNotSetYet (lookup cn res2) in
            compare cn1 cn2
    maxHC = maximumBy cmpHC used
    maxCT = lookup cn (snd3 maxHC)
    ct = fromMaybe CBottom maxCT
    hc = if isNothing maxCT then Nothing else Just maxHC


constructHornClause :: Expr -> [HornClause]
constructHornClause e = case e of
  Not _ a -> rotatedHornClauses ( [(getChainName a, CInferDeterministic)],  [(getChainName e, CInferDeterministic)], (StubNot, 0))
  -- The bound expression is det if the
  LetIn _ _ v b -> [([(getChainName b, CInferDeterministic)],  [(getChainName e, CInferDeterministic)], (StubLetIn, 0)), ([(getChainName e, CInferDeterministic)],  [(getChainName b, CInferDeterministic)], (StubLetIn, 1))]
  InjF {} -> getHornClause e
  _ -> []

constructHornClauses ::  Expr -> [[HornClause]]
constructHornClauses e = constructHornClause e:concatMap constructHornClauses (getSubExprs e)

-- TODO Constrained Hornclauses
-- Takes one horn clause on constructs all inverses, including the original
rotatedHornClauses :: HornClause -> [HornClause]
rotatedHornClauses clause@(cond, res, (stub, i)) | i == 0 = case (cond, res) of
  ([a], [b]) -> [clause, ([b],  [a], (stub, 1))]
  ([a, b], [c]) -> [clause, ( [c, a],  [b], (stub, 1)), ( [c, b],  [a], (stub, 2))]
  ([a, b], [c, d]) ->
    [clause, ( [a, c],  [b, d], (stub, 1)),
      ( [a, d],  [b, c], (stub, 2)),
      ( [b, c],  [a, d], (stub, 3)),
      ( [b, d],  [a, c], (stub, 4)),
      ( [c, d],  [a, b], (stub, 5))] --TODO is this a good order
  _ -> [clause]

findFulfilledHornClause :: [[HornClause]] -> [(ChainName, CType)] -> Maybe HornClause
--findFulfilledHornClause clauses satisfied | trace (show satisfied) False = undefined
findFulfilledHornClause clauses satisfied = find allSatisfied (concat clauses)
  where 
    allSatisfied (cond, _, _) = foldr (\(name, exp) b -> b && cTypeOf name >= exp) True cond
    cTypeOf name = fromMaybe CNotSetYet (lookup name satisfied)
    

findDeterminism :: Expr -> [ChainName]
findDeterminism (Constant t _) = [chainName t]
findDeterminism (ThetaI t _ _) = [chainName t]
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
determinedCTypes = concatMap snd3

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

inferProbProg :: Program -> IRExpr
inferProbProg (Program [("main", main)] _ _) = inferProbExpr main
inferProbProg _  = error "Programs with function declarations are not yet implemented"

inferProbExpr :: Expr -> IRExpr
inferProbExpr = inversionsToProb . exprToInversions

inversionsToProb :: ([Inversion a], [IRExpr]) -> IRExpr
inversionsToProb (inversions, firstR:randoms) = Prelude.foldr (\(Inversion (cn, val)) body -> IRLetIn cn val body) randomsProduct inversions
  where randomsProduct = Prelude.foldr (\expr body -> IROp OpMult expr body) firstR randoms

exprToInversions :: Expr -> ([Inversion a], [IRExpr])
exprToInversions e@(Uniform _) = (hornClauseToIRExpr e, [IRDensity IRUniform (IRVar (getChainName e))])
exprToInversions e@(Normal _) = (hornClauseToIRExpr e, [IRDensity IRNormal (IRVar (getChainName e))])
exprToInversions e = Prelude.foldr (\(a1, b1) (a, b) -> (nub (a1++a), b1++b)) ([], []) ((hornClauseToIRExpr e, []):Prelude.map exprToInversions (getSubExprs e))

hornClauseToIRExpr :: Expr -> [Inversion a]
hornClauseToIRExpr e | isNothing (derivingHornClause (getTypeInfo e)) = error "Cannot convert to IR without a horn clause"
hornClauseToIRExpr e = case stub of
  --TODO InjF hier

  StubLetIn | inversion == 0 -> [Inversion (cn, IRVar (preVars!!0))]
  StubLetIn | inversion == 1 -> [Inversion (cn, IRVar (preVars!!0))] --FIXME This seems wrong?
  
  StubConstant | inversion == 0 -> case e of
    (Constant _ v) -> [Inversion (cn, IRConst (fmap (error "Cannot convert VClosure") v))]
    _ -> [] -- There are places anntotated with constant that are not a constant. For example the returning value is assumed constant for the sake of forward chaining
  where
    (pre, _, (stub, inversion)) = fromJust (derivingHornClause (getTypeInfo e))
    preVars = map fst pre
    cn = getChainName e



chainVarOfSubExpr :: Expr -> Int -> IRExpr
chainVarOfSubExpr e n = IRVar (getChainName (getSubExprs e !! n))
