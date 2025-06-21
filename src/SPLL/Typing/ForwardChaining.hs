module SPLL.Typing.ForwardChaining where
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
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Debug.Trace


-- Information on what type of expression a HornClause originated from
data ExprInfo = StubInfo ExprStub   -- Generic Expression without additional Info
              | InjFInfo String     -- InjF with the name of the InjF
              | LambdaInfo String   -- Lambda with the name of the bound variable
              | ConstantInfo Value  -- Contant with the value
              deriving (Eq, Show)

-- Horn clauses state: When all premises are known, we can derive the conclusion. Expression info holds information about the original expression.
-- inversion represents which direction the HornClause represents. E.g.
-- Original: a = b + c
-- Inversion 0: b, c -> a
-- Inversion 1: a, c -> b
-- Inversion 2: a, b -> c
-- Parameter HornClauses define a ChainName to be known. This could represent the sample passed to the top-level expression, or the parameter passed to an inverse expression
data HornClause = ExprHornClause {premises' :: [ChainName], conclusion :: ChainName, exprInfo :: ExprInfo, inversion :: Int}
                | ParameterHornClause {conclusion :: ChainName} deriving (Eq, Show)

-- Wraps the premises field, because ParameterHornClauses have an empty set of premises by definition
premises :: HornClause -> [ChainName]
premises ParameterHornClause {} = []
premises ExprHornClause {premises'=p}= p

getChainName :: Expr -> ChainName
getChainName = chainName . getTypeInfo

-- Takes multiple groups of HornClauses and a point in the AST which should be inverted.
-- The function then searches for a Lambda statement and inverses toward the lambda
toInvExpr :: [[HornClause]] -> ChainName -> IRExpr
toInvExpr clauseSet startCN = irExpr
  where
    -- Add a clause without preconditions for parameters as a starting point
    toInvCN = findBoundVariable clauseSet startCN
    paramClause = ParameterHornClause startCN
    augmentedClauseSet = [paramClause]:clauseSet
    requiredClauses = solveHCSet augmentedClauseSet
    sortedClauses = topologicalSort requiredClauses
    relevantSortedClauses = cutList sortedClauses (findConcludingHornClause sortedClauses toInvCN)
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
    ExprHornClause [preVar] _ (LambdaInfo _) 0 ->
      IRVar preVar
    ParameterHornClause conc -> IRVar conc
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

findConcludingHornClause :: [HornClause] -> ChainName -> HornClause
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> error $ "Found no horn clause concluding to " ++ cn
    res -> head res

-- Finds the bound variable of the lambda the parameter ChainName is refferencing
findBoundVariable :: [[HornClause]] -> ChainName -> ChainName
findBoundVariable clauses startName = fromJust $ findBoundVariable' forwardClauses startName
  where
    forwardClauses = concatMap (filter ((== 0) . inversion)) clauses

findBoundVariable' :: [HornClause] -> ChainName -> Maybe ChainName
findBoundVariable' clauses name =
  case currClauses of
    (ExprHornClause _ _ (LambdaInfo n) _):_ -> Just n
    _ -> firstJusts $ map (findBoundVariable' (clauses \\ headIfExists currClauses) . conclusion) nextClauses

  where
    nextClauses = filter (elem name . premises) clauses
    currClauses = filter ((== name) . conclusion) clauses
    firstJusts ((Just x):xs) = Just x
    firstJusts (Nothing:xs) = firstJusts xs
    firstJusts [] = Nothing
    headIfExists (a:_) = [a]
    headIfExists [] = []


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
  Lambda _ n body -> [ExprHornClause [getChainName e] (getChainName body) (LambdaInfo n) 0]
  InjF {} -> injFtoHornClause e
  _ -> []
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
  where
    annotFs = runSupplyVars (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)  -- FIXME set correct cain names for top level exprs
    runSupplyVars f = runSupply f (+1) 0

annotateExpr :: Expr -> Supply Int Expr
annotateExpr e = tMapM (\ex -> do
  case ex of
    Var t n -> return $ setChainName t n
    _ -> demand <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
  ) e

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