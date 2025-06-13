module SPLL.Typing.ForwardChaining2 where
import SPLL.Lang.Types hiding (HornClause)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types (Program(Program))
import Control.Monad.Supply
import Data.Bifunctor
import Data.Functor ((<&>))
import SPLL.Lang.Lang
import PredefinedFunctions
import Data.PartialOrd (PartialOrd, minima, (<=))
import Data.List ((\\), delete)
import Data.Maybe
import SPLL.Typing.ForwardChaining (getChainName)
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Debug.Trace

data ExprInfo = StubInfo ExprStub | InjFInfo String | ConstantInfo Value deriving (Eq, Show)
data HornClause = ExprHornClause {premises' :: [ChainName], conclusion :: ChainName, exprInfo :: ExprInfo, inversion :: Int}
                | ParameterHornClause {conclusion :: ChainName} deriving (Eq, Show)

premises :: HornClause -> [ChainName]
premises ParameterHornClause {} = []
premises ExprHornClause {premises'=p}= p

toInvExpr :: [[HornClause]] -> [ChainName] -> ChainName -> IRExpr
toInvExpr clauseSet knownSubCNs toInvertCN = irExpr
  where
    -- Add a clause without preconditions for parameters as a starting point
    paramClauses = map (\cn -> [ParameterHornClause cn]) knownSubCNs
    augmentedClauseSet = clauseSet ++ paramClauses
    requiredClauses = solveHCSet augmentedClauseSet
    sortedClauses = traceShowId $ topologicalSort requiredClauses
    relevantSortedClauses = traceShowId $ cutList sortedClauses (findConcludingHornClause sortedClauses toInvertCN)
    irExpr = toLetInBlock relevantSortedClauses

toLetInBlock :: [HornClause] -> IRExpr
toLetInBlock [c] = hornClauseToIRExpr c
toLetInBlock (c:cs) = IRLetIn (conclusion c) (hornClauseToIRExpr c) (toLetInBlock cs)
toLetInBlock [] = error "Cannot convert empty clause set to LetIn block"

hornClauseToIRExpr :: HornClause -> IRExpr
hornClauseToIRExpr clause =
  case clause of
    ExprHornClause _ _ (ConstantInfo v) _ -> IRConst (valueToIR v)
    ExprHornClause preVars _ (InjFInfo name) inv | inv == 0 ->
        let Just (FPair fwdInjF _) = lookup name globalFenv
            renamedF = foldr (\(old, new) decl -> renameDecl old new decl) fwdInjF (zip (inputVars fwdInjF) preVars) in
              body renamedF
    ExprHornClause preVars _ (InjFInfo name) inv -> do
      let Just (FPair _ invInjF) = lookup name globalFenv
      let correctInv = invInjF !! (inv - 1)
      let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
      body renamedF
    ParameterHornClause conc -> IRVar conc
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

findConcludingHornClause :: [HornClause] -> ChainName -> HornClause
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> error $ "Found no horn clause concluding to " ++ cn
    res -> head res
{-
findChainNameInProg :: ChainName -> Program -> Expr
findChainNameInProg cn Program{functions=fs} = 
  case concatMap (\(n, f) -> findChainNameInExpr cn f) fs of
    [] -> error $ "Did not find chain name in Prpgram: " ++ cn
    [e] -> e
    _ -> error $ "Found chain name multiple times in program" ++ cn

-- Could return Maybe Expr, but code is simpler with lists
findChainNameInExpr :: ChainName -> Expr -> [Expr]
findChainNameInExpr cn expr | chainName (getTypeInfo expr) == cn = [expr]
findChainNameInExpr cn expr = concatMap (findChainNameInExpr cn) (getSubExprs expr)
-}

progToHornClauses :: Program -> [[HornClause]]
progToHornClauses Program{functions=fs}= concatMap (exprToHornClauses . snd) fs

exprToHornClauses :: Expr -> [[HornClause]]
exprToHornClauses e = singleExprToHornClause e:concatMap exprToHornClauses (getSubExprs e)

singleExprToHornClause :: Expr -> [HornClause]
singleExprToHornClause e = case e of
  Constant _ v -> [ExprHornClause [] (getChainName e) (ConstantInfo v) 0]
  Uniform _ -> []
  Normal _ -> []
  InjF {} -> injFtoHornClause e
  _ -> error $ "Forward chaining currently does not support " ++ show (toStub e)

injFtoHornClause :: Expr -> [HornClause]
injFtoHornClause e = case e of
  InjF t name params -> (constructInjFHornClause subst eCN name eFwd 0): zipWith (constructInjFHornClause subst eCN name) eInv [1..]
    where
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl {inputVars = inV, outputVars = [outV]} = eFwd
      Just (FPair eFwd eInv) = lookup name globalFenv
  _ -> error "Cannot get horn clause of non-predefined function"

constructInjFHornClause :: [(String, ChainName)] -> ChainName -> String -> FDecl -> Int -> HornClause
constructInjFHornClause subst cn name decl inv= ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv --FIXME correct inversion parameters 
  where
    FDecl {inputVars = inV, outputVars = [outV]} = decl
    lookupSubst v = fromJust (lookup v subst)
    lookUpSubstAddDet v = ()

getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map (chainName . getTypeInfo) (getSubExprs e)


annotateProg :: Program -> Program
annotateProg p@Program {functions=fs} = p{functions=annotFs}
  -- Map annotateExpr on all functions. The code is ugly because of monad shenanigans
  where annotFs = runSupplyVars (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)  -- FIXME set correct cain names for top level exprs

annotateExpr :: Expr -> Supply Int Expr
annotateExpr e = tMapM (\ex -> do
  case ex of
    Var t n -> return $ setChainName t n
    _ -> demand <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
  ) e



runSupplyVars :: Supply Int a -> a
runSupplyVars f = runSupply f (+1) 0

solveHCSet :: [[HornClause]] -> [HornClause]
solveHCSet hcs = snd (solveHCSet' hcs [])

solveHCSet' :: [[HornClause]] -> [HornClause] -> ([[HornClause]], [HornClause])
solveHCSet' hcs fulfilled = case findFulfilledClause hcs fulfilled of
  Just nextClause ->
    let updatedHCs = delete (fromJust (find (elem nextClause) hcs)) hcs in
      solveHCSet' updatedHCs (nextClause:fulfilled)
  Nothing ->(hcs, fulfilled)

findFulfilledClause :: [[HornClause]] -> [HornClause] -> Maybe HornClause
findFulfilledClause hcs fulfilled = listToMaybe fulfilledClauses
  where
    detVars = map conclusion fulfilled
    fulfilledClauses = filter (all (`elem` detVars) . premises) (concat hcs)

topologicalSort :: (PartialOrd a, Eq a, Show a) => [a] -> [a]
topologicalSort clauses | traceShow clauses False = undefined
topologicalSort [] = []
topologicalSort clauses =
  let maxC = minima clauses in
    maxC ++ topologicalSort (clauses \\ maxC)

cutList :: Eq a => [a] -> a -> [a]
cutList [] _ = []
cutList (x:xs) stop
  | x == stop = [x]
  | otherwise = x : cutList xs stop

instance PartialOrd HornClause where
  -- B depends on A
  ExprHornClause {premises'=pre1, conclusion=conc1} <= ExprHornClause {premises'=pre2, conclusion=conc2} =  conc1 `elem` pre2
  -- All ParameterHornClauses are less than all ExpressionHornClauses. All ParameterHornClauses are equal (Equal for this partial ordering, Not for Eq)
  ExprHornClause {} <= ParameterHornClause {} = False
  _ <= _ = True