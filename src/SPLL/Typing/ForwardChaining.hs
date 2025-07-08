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
import GHC.Stack (HasCallStack)


-- Information on what type of expression a HornClause originated from
data ExprInfo = StubInfo ExprStub   -- Generic Expression without additional Info
              | InjFInfo String     -- InjF with the name of the InjF
              | LambdaInfo String   -- Lambda with the name of the bound variable
              | ConstantInfo Value  -- Contant with the value
              | AppliedInfo         -- Does not directly correlate to an expression. Via application a value is assigned to a bound variable
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

-- Takes all HornClauses of a Program and a point in the AST which should be inverted.
-- The function then searches for a Lambda statement and inverses toward the bound variable
-- Note that it deliberately skips over lambdas that are already applied
toInvExpr :: [[HornClause]] -> ChainName -> IRExpr
--toInvExpr clauses startCN | traceShow startCN False = undefined
toInvExpr clauseSet startCN = irExpr
  where
    -- Find the bound variable of a lambda that is not already applied
    -- This needs to be done if the lambda is a variable, 
    -- in which case the lamba expression would not be a subexpression of the expression to invert
    toInvCN = findBoundVariable clauseSet startCN
    -- Add a clause without preconditions for parameters as a starting point
    -- Define the expression to invert as known. This is true by the definition of an inverse
    paramClause = ParameterHornClause startCN
    augmentedClauseSet =[paramClause]:clauseSet
    -- Solve the set of Horn clauses for clauses which are fulfilled
    solvedClauses = solveHCSet augmentedClauseSet
    -- Throw away superfluous clauses. Do this by sorting them by requirement
    -- and throwing away clauses after the clause that inferes the bound variable
    -- Also guarantees that the later generated letIns are in the correct order
    sortedClauses = topologicalSort solvedClauses
    relevantSortedClauses = cutList sortedClauses (findConcludingHornClause sortedClauses toInvCN)
    -- Generate code
    irExpr = toLetInBlock clauseSet relevantSortedClauses

-- Creates a block of code from a set of sorted horn clauses
-- Generates the last horn clause as a return statement and wraps it in letIn statements created from the leading clauses
toLetInBlock :: [[HornClause]] -> [HornClause] -> IRExpr
toLetInBlock clauses [c] = hornClauseToIRExpr clauses c
toLetInBlock clauses (c:cs) = IRLetIn (conclusion c) (hornClauseToIRExpr clauses c) (toLetInBlock clauses cs)
toLetInBlock clauses [] = error "Cannot convert empty clause set to LetIn block"


-- Generates IRExpr from Horn clauses
hornClauseToIRExpr :: [[HornClause]] -> HornClause -> IRExpr
hornClauseToIRExpr clauses clause =
  case clause of
    -- Constants are always their value
    ExprHornClause _ _ (ConstantInfo v) 0 -> IRConst (valueToIR v)
    -- Get the correct names of the parameters from the horn clause and instantiate the InjF
    ExprHornClause preVars _ (InjFInfo name) inv | inv == 0 ->
        let Just (FPair fwdInjF _) = lookup name globalFenv
            renamedF = foldr (\(old, new) decl -> renameDecl old new decl) fwdInjF (zip (inputVars fwdInjF) preVars) in
              body renamedF
    -- Similar to the forward InjF, but additionally find the correct inversion first
    -- Inversions are always in the correct order in globalFEnv, because the inversion number is created from this order
    ExprHornClause preVars _ (InjFInfo name) inv -> do
      let Just (FPair _ invInjF) = lookup name globalFenv
      let correctInv = invInjF !! (inv - 1)
      let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
      body renamedF
    -- The "value" of a lambda expression is the value of its body
    ExprHornClause [preVar] _ (LambdaInfo _) 1 ->
      IRVar preVar
    -- Forward pass of an application is setting the bound variable of an underlying lambda to the bound value
    ExprHornClause [preLmb, preBound] conc (StubInfo StubApply) 0 -> do
      let bound = findBoundVariable clauses preLmb
      IRLetIn bound (IRVar preBound) (IRVar conc)
    -- The application expression has the value of the bound expression
    ExprHornClause [preExpr] conc (StubInfo StubApply) 1 -> do
      IRVar preExpr
    -- Outside of the normal scope of inversions, therefor a negative inversion number
    -- If a value was applied to a bound variable, that bound variable is the applied value
    ExprHornClause [applied] _ AppliedInfo _ -> do
      IRVar applied
    -- Expect parameters to be known
    ParameterHornClause conc -> IRVar conc
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

-- Finds the first horn clause in a list that has a given conclusion
findConcludingHornClause :: [HornClause] -> ChainName -> HornClause
--findConcludingHornClause hcs cn | trace ("Find " ++ cn ++ " in " ++ show hcs) False = undefined
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> error $ "Found no horn clause concluding to " ++ cn
    res -> head res

-- Finds the bound variable of the lambda the parameter ChainName is referencing
-- Note that this needs to skip over already applied lambdas
findBoundVariable :: HasCallStack => [[HornClause]] -> ChainName -> ChainName
findBoundVariable clauses startName = fromJust $ findBoundVariable' forwardClauses 0 startName
  where
    -- Only forward clauses (inversion == 0) are relevant for this, because we dont want cycles in our graph of horn clauses
    -- Applied clauses are also relevant, because the lambda might be a variable applied elsewhere
    forwardClauses = concatMap (filter (\c -> inversion c == 0 || isAppliedInfo (exprInfo c))) clauses
    isAppliedInfo AppliedInfo = True
    isAppliedInfo _ = False

-- Finds the lambda a parameter ChainName is referencing
-- This also needs to skip over applied lambdas. Because applications must happen before a lambda, 
-- keep track of the number of applications seen on the way and disregard that many lambdas
findBoundVariable' :: HasCallStack => [HornClause] -> Int -> ChainName -> Maybe ChainName
--findBoundVariable' clauses applies name | trace (show name++ "|" ++ show applies ++ "|" ++ show clauses) False = undefined
findBoundVariable' clauses applies name =
  -- The next lambda is what we are looking for
  if applies == 0 then
    case currClauses of
      -- We found what we are looking for
      (ExprHornClause _ _ (LambdaInfo n) _):_ -> Just n
      -- Increase the number of applications to disregard the next lambda
      (ExprHornClause _ conc (StubInfo StubApply) _):cs -> findBoundVariable' cs (applies + 1) conc
      -- Continue looking, but without the current clause. First with the same name, then with all possible next names
      _ -> firstJusts $ if null currClauses then [] else findBoundVariable' (clauses \\ headIfExists currClauses) applies name:
        map (findBoundVariable' (clauses \\ headIfExists currClauses) applies . conclusion) nextClauses

  -- Disregard the next lambda, because it is already applied
  else
    case currClauses of
      -- Disregard it, but decrease the number of applications
      (ExprHornClause _ conc (LambdaInfo n) _):cs -> findBoundVariable' cs (applies - 1) conc
      -- Increase the number of applications to disregard the next lambda
      (ExprHornClause _ conc (StubInfo StubApply) _):cs -> findBoundVariable' cs (applies + 1) conc
      _ -> firstJusts $ if null currClauses then [] else findBoundVariable' (clauses \\ headIfExists currClauses) applies name:
        map (findBoundVariable' (clauses \\ headIfExists currClauses) applies . conclusion) nextClauses
  where
    -- Clauses with the name as premises are potential next clauses
    nextClauses = filter (elem name . premises) clauses
    -- Clauses with the current name as conclusion are the current clauses
    currClauses = filter ((== name) . conclusion) clauses
    -- First Just in a list, else nothing
    firstJusts ((Just x):xs) = Just x
    firstJusts (Nothing:xs) = firstJusts xs
    firstJusts [] = Nothing
    headIfExists (a:_) = [a]
    headIfExists [] = []

-- Convert a Program to a set of groups of Horn clauses
progToHornClauses :: Program -> [[HornClause]]
progToHornClauses Program{functions=fs} = foldl (\ augClauses currGroup-> augmentApplyClauseSet augClauses currGroup:augClauses) initialRun initialRun
  where
    -- We need two runs for this: first run is every expression converted into a group of Horn clauses
    initialRun = concatMap (exprToHornClauses . snd) fs
    -- Second run is a special Horn clause for applications

-- Converts an expression with all its subexpressions into Horn clauses
exprToHornClauses :: Expr -> [[HornClause]]
exprToHornClauses e = singleExprToHornClause e:concatMap exprToHornClauses (getSubExprs e)

-- Converts a single expression into Horn clauses
singleExprToHornClause :: Expr -> [HornClause]
singleExprToHornClause e = case e of
  Constant _ v -> [ExprHornClause [] (getChainName e) (ConstantInfo v) 0]
  Lambda _ n body -> [ExprHornClause [getChainName body] (getChainName e) (LambdaInfo n) 0,
                      ExprHornClause [getChainName e] (getChainName body) (LambdaInfo n) 1]
  Apply _ l v -> [ExprHornClause [getChainName l, getChainName v] (getChainName e) (StubInfo StubApply) 0,
                  ExprHornClause [getChainName e] (getChainName l) (StubInfo StubApply) 1]
  InjF {} -> injFtoHornClause e
  -- No Horn clauses instead of error. Some expressions are not invertable and therefor do not produce Horn clauses. But we might not need them 
  _ -> []

-- Converts an instance of a InjF into a Horn clause with corresponding variables in the premises and conclusion
injFtoHornClause :: Expr -> [HornClause]
injFtoHornClause e = case e of
  -- Forward Horn clause: Inverse Horn clauses with corresponding inversion number 
  InjF t name params -> (constructInjFHornClause subst eCN name eFwd 0): zipWith (constructInjFHornClause subst eCN name) eInv [1..]
    where
      -- Create a substitution, that maps the variables in the declaration of the InjF
      -- to the ChainNames in the instantiation
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl {inputVars = inV, outputVars = [outV]} = eFwd
      Just (FPair eFwd eInv) = lookup name globalFenv
  _ -> error "Cannot get horn clause of non-predefined function"

-- Creates a Horn clause of an FDecl and substitutes the variables with a substition
constructInjFHornClause :: [(String, ChainName)] -> ChainName -> String -> FDecl -> Int -> HornClause
constructInjFHornClause subst cn name decl inv = ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv
  where
    FDecl {inputVars = inV, outputVars = [outV]} = decl
    lookupSubst v = fromJust (lookup v subst)

-- Application implies that the bound variable of the lambda expression is equal to the applied expression.
-- This step requires knowledge of the program structure and can therefor only be done after the clause set is constructed
augmentApplyClauseSet :: [[HornClause]] -> [HornClause] -> [HornClause]
augmentApplyClauseSet clauses (c@(ExprHornClause [l, v] cn (StubInfo StubApply) 0):_) =
  [ExprHornClause [v] bound AppliedInfo 0,
   ExprHornClause [bound] v AppliedInfo 1]
  where bound = findBoundVariable clauses l
augmentApplyClauseSet _ x = []

-- Chain name of subexpressions
getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map getChainName (getSubExprs e)

-- Annotates a Program with chain names for every expression
annotateProg :: Program -> Program
annotateProg p@Program {functions=fs} = p{functions=annotFs}
  -- Map annotateExpr on all functions. The code is ugly because of monad shenanigans
  where
    annotFs = runSupplyVars (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)
    -- Sets the ChainName of the top level expression to the name of the top level expression
    -- TODO: What if the top level is just a variable access?
    correctTopLevel = map (\(n, f) -> (n, setTypeInfo f (setChainName (getTypeInfo f) n))) annotFs
    runSupplyVars f = runSupply f (+1) 0

-- Annotate an expression and all of its subexpressions
annotateExpr :: Expr -> Supply Int Expr
annotateExpr = tMapM (\ex -> do
  case ex of
    -- Variables have itself as its ChainName
    Var t n -> return $ setChainName t n
    _ -> demand <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
  )

-- Returns all recursively fulfilled clauses
solveHCSet :: [[HornClause]] -> [HornClause]
solveHCSet hcs = solveHCSet' hcs []

-- Takes a set of all clauses and already fulfilled clauses and returns a set of fulfilled Horn clauses
solveHCSet' :: [[HornClause]] -> [HornClause] -> [HornClause]
solveHCSet' hcs fulfilled = case findFulfilledClause hcs fulfilled of
  Just nextClause ->
    -- Remove used clause group from set of available clauses
    let updatedHCs = delete (fromJust (find (elem nextClause) hcs)) hcs in
      solveHCSet' updatedHCs (nextClause:fulfilled)
  Nothing -> fulfilled

-- Finds a fulfilled clause given a set of already fulfilled clauses
findFulfilledClause :: [[HornClause]] -> [HornClause] -> Maybe HornClause
findFulfilledClause hcs fulfilled = listToMaybe fulfilledClauses
  where
    detVars = map conclusion fulfilled
    fulfilledClauses = filter (all (`elem` detVars) . premises) (concat hcs)

-- Sorts a list according to a partial order such that if a comes before b a <= b
topologicalSort :: (PartialOrd a, Eq a, Show a) => [a] -> [a]
topologicalSort [] = []
topologicalSort clauses =
  let maxC = minima clauses in
    maxC ++ topologicalSort (clauses \\ maxC)

-- Returns all elements that come before a given parameter in a list
cutList :: Eq a => [a] -> a -> [a]
cutList [] _ = []
cutList (x:xs) stop
  | x == stop = [x]
  | otherwise = x : cutList xs stop

-- Define a partial order that corresponds to dependancy. A is less than B if B depends on A 
instance PartialOrd HornClause where
  -- A <= B iff B depends on A
  ExprHornClause {conclusion=conc1} <= ExprHornClause {premises'=pre2} =  conc1 `elem` pre2
  -- All ParameterHornClauses are less than all ExpressionHornClauses. All ParameterHornClauses are equal (Equal for this partial ordering, Not for Eq)
  ExprHornClause {} <= ParameterHornClause {} = False
  _ <= _ = True