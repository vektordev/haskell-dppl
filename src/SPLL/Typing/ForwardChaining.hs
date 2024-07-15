module SPLL.Typing.ForwardChaining where

import SPLL.Lang (Expr, Program, Program(..), Expr(..), getTypeInfo, tMapM, getSubExprs, setTypeInfo, tMap)
import SPLL.Typing.Typing
import Control.Monad.Supply

import Data.List (delete, find)
import Data.Set
import Debug.Trace (trace)
import Data.Bifunctor(second)
import Control.Monad.State.Lazy (StateT, State, runState, runStateT, get, put)
import PredefinedFunctions

type Chain a = SupplyT Int (State [(String, ChainName)]) a
type ChainInferState = ([HornClause], [HornClause])

addChainName :: ChainName -> Expr (TypeInfo a) a -> TypeInfo a
addChainName s e = setChainName (getTypeInfo e) s

getChainName :: Expr (TypeInfo a) a -> ChainName
getChainName = chainName . getTypeInfo

annotateSyntaxTree :: Expr (TypeInfo a) a -> Chain (Expr (TypeInfo a) a)
annotateSyntaxTree = tMapM (\e -> do
    idx <- demand   -- idx may be unused due to multiple usages of the same variable
    let name = "astNode" ++ show idx
    case e of
      (Var _ varName) -> lift $ do
        state <- get
        case lookup varName state of
          Just cn -> return $ addChainName cn e
          Nothing -> do 
            put ((varName, name):state)
            return $ addChainName name e
      _ -> return $ addChainName name e
    )

annotateChainNamesProg :: Program (TypeInfo a) a -> Chain (Program (TypeInfo a) a)
annotateChainNamesProg (Program decls e) = do
  eAn <- annotateSyntaxTree e
  declsAn <- Prelude.mapM (\(n, ex) -> do
    exAn <- annotateSyntaxTree ex
    return (n, exAn)) decls
  return $ Program declsAn eAn

inferProg :: Program (TypeInfo a) a -> Program (TypeInfo a) a  --TODO NotSetYet auf Bottom setzen
inferProg p = Program finishedDecls finishedExpr
  where
    (annotatedProg, _) = runState (runSupplyT (annotateChainNamesProg p) (+1) 1) []
    Program declsAn eAn = annotatedProg
    annotatedExprs = eAn:Prelude.map snd declsAn
    startDetVars = startExprName:concatMap findDeterminism annotatedExprs
    hornClauses = concatMap constructHornClauses annotatedExprs
    startExprName = chainName $ getTypeInfo (head annotatedExprs)
    startClause = (empty, fromList [(startExprName, CInferDeterministic)])
    finishedState = fixpointIteration (hornClauses, [startClause])
    finishedDecls = Prelude.map (Data.Bifunctor.second (tMap (annotateMaximumCType finishedState))) declsAn
    finishedExpr = tMap (annotateMaximumCType finishedState) eAn

annotateMaximumCType :: ChainInferState -> Expr (TypeInfo a) a -> TypeInfo a
annotateMaximumCType (_, used) e = setCType t maxCT
  where
    t = getTypeInfo e
    cn = chainName t
    cTypes = Prelude.foldr (\e l -> l ++ cTypesHC e) [] used
    cTypesHC (_, res) = toList (Data.Set.map snd (Data.Set.filter (\(n, _) -> n == cn) res))
    maxCT = maximum cTypes


constructHornClause :: Expr (TypeInfo a) a -> [HornClause]
constructHornClause e = case e of
  PlusF _ a b -> rotatedHornClauses (fromList [getChainName a, getChainName b], fromList [(getChainName e, CInferDeterministic)])
  LetIn _ _ _ b -> [(fromList [getChainName b], fromList [(getChainName e, CInferDeterministic)])] --TODO LetIn Hornklausel
  InjF {} -> getHornClause e
  _ -> []

constructHornClauses :: Expr (TypeInfo a) a -> [HornClause]
constructHornClauses e = constructHornClause e ++ concatMap constructHornClauses (getSubExprs e)

-- Takes one horn clause on constructs all inverses, including the original
rotatedHornClauses :: HornClause -> [HornClause]
rotatedHornClauses clause@(cond, res) = case (toList cond, toList res) of
  ([a], [(b, ct)]) | ct == CDeterministic || ct == CInferDeterministic ->
    [clause, (fromList [b], fromList [(a, CInferDeterministic)])]
  ([a, b], [(c, ct)]) | ct == CDeterministic || ct == CInferDeterministic ->
    [clause, (fromList [a, c], fromList [(b, CInferDeterministic)]), (fromList [b, c], fromList [(a, CInferDeterministic)])]
  ([a, b], [(c, ct0), (d, ct1)]) | (ct0 == CDeterministic || ct0 == CInferDeterministic) && (ct1 == CDeterministic || ct1 == CInferDeterministic) ->
    [clause, (fromList [a, c], fromList [(b, CInferDeterministic), (d, CInferDeterministic)]),
      (fromList [a, d], fromList [(b, CInferDeterministic), (c, CInferDeterministic)]),
      (fromList [b, c], fromList [(a, CInferDeterministic), (d, CInferDeterministic)]),
      (fromList [b, d], fromList [(a, CInferDeterministic), (c, CInferDeterministic)]),
      (fromList [c, d], fromList [(a, CInferDeterministic), (b, CInferDeterministic)])]
  _ -> [clause]

findFulfilledHornClause :: [HornClause] -> [ChainName] -> Maybe HornClause
findFulfilledHornClause clauses satisfied = find allSatisfied clauses
  where allSatisfied (cond, _) = Data.Set.foldr (\x b -> b && elem x satisfied) True cond

findDeterminism :: Expr (TypeInfo a) a -> [ChainName]
findDeterminism (Constant t _) = [chainName t]
findDeterminism (ThetaI t _) = [chainName t]
findDeterminism e = concatMap findDeterminism (getSubExprs e)

-- To the person that wants to implement weaker CTypes:
--  Note that this method uses the implied CType of the used HornClauses to infer the type of each variable
--  Therefor if you want to continue using this method you need to downgrade the CTypes in the used HornClauses
getAllDetVarsInState :: ChainInferState -> [ChainName]
getAllDetVarsInState (_, used) = detVars
  where
    onlyDet = Prelude.foldr (\e l -> l ++ onlyDetHC e) [] used
    onlyDetHC (_, res) = toList (Data.Set.filter (\(_, ct) -> ct == CDeterministic || ct == CInferDeterministic) res)
    detVars = Prelude.map fst onlyDet

inferDeterminism :: ChainInferState -> ChainInferState
inferDeterminism curr@(clauses, used) = case findFulfilledHornClause clauses (getAllDetVarsInState curr) of
  Just nextClause -> (newClauses, nextClause:used)
    where newClauses = Prelude.foldr Data.List.delete clauses (rotatedHornClauses nextClause) -- FIXME: Not the rotated clauses, but the inverses
  Nothing -> (clauses, used)

fixpointIteration :: ChainInferState -> ChainInferState
fixpointIteration curr@(clauses, used) = if newDetVars == detVars
    then res
    else fixpointIteration (newClauses, newUsed)
  where
    res@(newClauses, newUsed) = inferDeterminism (clauses, used)
    detVars = getAllDetVarsInState curr
    newDetVars = getAllDetVarsInState res
