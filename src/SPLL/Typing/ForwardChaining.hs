module SPLL.Typing.ForwardChaining where

import SPLL.Lang (Expr, Program, Program(..), Expr(..), getTypeInfo, tMapM, getSubExprs, setTypeInfo)
import SPLL.Typing.Typing
import Control.Monad.Supply

import Data.List (delete, find)
import Data.Set
import Debug.Trace (trace)
import Control.Monad.State.Lazy (StateT, State, runState, runStateT, get, put)

type Chain a = SupplyT Int (State [(String, ChainName)]) a

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

annotateProg :: Program (TypeInfo a) a -> Chain [Expr (TypeInfo a) a]
annotateProg (Program decls e) = do
  let exprs = e:Prelude.map snd decls
  let annotatedExprs = Prelude.mapM annotateSyntaxTree exprs
  let concExprs = annotatedExprs
  concExprs

inferProg :: Program (TypeInfo a) a -> ([HornClause], [HornClause], [ChainName])
inferProg p = fixpointIteration hornClauses [] startDetVars
  where (annotatedExprs, _) = runState (runSupplyT (annotateProg p) (+1) 1) []
        startDetVars = startExprName:concatMap findDeterminism annotatedExprs
        hornClauses = concatMap constructHornClauses annotatedExprs
        startExprName = chainName $ getTypeInfo (head annotatedExprs)

constructHornClause :: Expr (TypeInfo a) a -> [HornClause]
constructHornClause e = case e of
  PlusF _ a b -> rotatedHornClauses (fromList [getChainName a, getChainName b], fromList [getChainName e])
  LetIn _ _ _ b -> [(fromList [getChainName b], fromList [getChainName e])] --FIXME korrekte Hornklauseln für letins
  _ -> []

constructHornClauses :: Expr (TypeInfo a) a -> [HornClause]
constructHornClauses e = constructHornClause e ++ concatMap constructHornClauses (getSubExprs e)

-- Takes one horn clause on constructs all inverses, including the original
rotatedHornClauses :: HornClause -> [HornClause]
rotatedHornClauses clause@(cond, res) = case (toList cond, toList res) of
  ([a], [b]) -> [clause, (fromList [b], fromList [a])]
  ([a, b], [c]) -> [clause, (fromList [a, c], fromList [b]), (fromList [b, c], fromList [a])]
  ([a, b], [c, d]) -> [clause, (fromList [a, c], fromList [b, d]), (fromList [a, d], fromList [b, c]), (fromList [b, c], fromList [a, d]), (fromList [b, d], fromList [a, c]), (fromList [c, d], fromList [a, b])]
  _ -> error $ "Unimplemented for of a horn clause " ++ show (toList cond, toList res)

findFulfilledHornClause :: [HornClause] -> [ChainName] -> Maybe HornClause
findFulfilledHornClause clauses satisfied = find allSatisfied clauses
  where allSatisfied (cond, _) = Data.Set.foldr (\x b -> b && elem x satisfied) True cond

findDeterminism :: Expr (TypeInfo a) a -> [ChainName]
findDeterminism (Constant t _) = [chainName t]
findDeterminism (ThetaI t _) = [chainName t]
findDeterminism e = concatMap findDeterminism (getSubExprs e)

inferDeterminism :: [HornClause] -> [HornClause] -> [ChainName] -> ([HornClause], [HornClause], [ChainName])
inferDeterminism clauses used detVars = case findFulfilledHornClause clauses detVars of
  Just nextClause -> (newClauses, nextClause:used, toList newVars++detVars)
    where newClauses = Prelude.foldr Data.List.delete clauses (rotatedHornClauses nextClause)
          (_, newVars) = nextClause
  Nothing -> (clauses, used, detVars)

fixpointIteration :: [HornClause] -> [HornClause] -> [ChainName] -> ([HornClause], [HornClause], [ChainName])
fixpointIteration clauses used detVars = if newDetVars == detVars 
    then res
    else fixpointIteration newClauses newUsed newDetVars
  where res@(newClauses, newUsed, newDetVars) = inferDeterminism clauses used detVars
