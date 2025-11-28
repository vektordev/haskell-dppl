{-# LANGUAGE FlexibleInstances #-}
module SPLL.Typing.ForwardChaining where
import SPLL.Lang.Types hiding (HornClause)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types (Program(Program))
import Data.Bifunctor
import Data.Functor ((<&>))
import SPLL.Lang.Lang
import PredefinedFunctions
import Data.List ((\\), delete, nub, isPrefixOf, tails)
import Data.Maybe
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Debug.Trace
import GHC.Stack (HasCallStack)
import System.Posix.Types (CNfds(CNfds))
import Utils
import SPLL.Typing.RType
import qualified Text.Megaparsec.Char as ANY
import Data.IntMap.Merge.Strict (merge)
import Utils (DAGEdge)
import Data.Char (isDigit)
import GHC.Base (augment)


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

isAppliedInfo :: ExprInfo -> Bool
isAppliedInfo AppliedInfo = True
isAppliedInfo _ = False

tagChainsTo :: Program -> Program
tagChainsTo prog = prog {functions=map (second (tMap (tagChainsToExpr hornClauses))) (functions prog)}
  where
    hornClauses = progToHornClauses prog

tagChainsToExpr :: [[HornClause]] -> Expr -> TypeInfo
tagChainsToExpr clauses (Apply ti l v) = ti{tags=ChainsTo foundLambdaCN:tags ti}
  where
    lambdaCN = chainName (getTypeInfo l)
    Just (_, foundLambdaCN) = findBoundVariable clauses lambdaCN
tagChainsToExpr _ x = getTypeInfo x

-- Inversion table maps a chain name of the lamda declaration to: (Name of the bound variable, (Inversion of the lambda, CoV factor))
buildInversionTable :: [ADTDecl] -> Program -> [(ChainName, (String, (IRExpr, IRExpr)))]
buildInversionTable adts prog = concatMap (buildInversionTableExpr hornClauses adts [] . snd) (functions prog)
  where
    hornClauses = progToHornClauses prog

buildInversionTableExpr :: [[HornClause]] -> [ADTDecl] -> [String] -> Expr -> [(ChainName, (String, (IRExpr, IRExpr)))]
buildInversionTableExpr clauses adts boundVars (Lambda TypeInfo{chainName=cn} bound body) = (cn, (bound, toInvExpr clauses adts boundVars cn bound)):buildInversionTableExpr clauses adts (bound:boundVars) body
--buildInversionTableExpr clauses adts (Var TypeInfo{rType = TArrow _ _, chainName=cn} v) = 
buildInversionTableExpr clauses adts boundVars x = concatMap (buildInversionTableExpr clauses adts boundVars) (getSubExprs x)

-- Takes all HornClauses of a Program and a point in the AST which should be inverted.
-- The function then searches for a Lambda statement and inverses toward the bound variable
-- Note that it deliberately skips over lambdas that are already applied
toInvExpr :: [[HornClause]] -> [ADTDecl] -> [String] -> ChainName -> ChainName -> (IRExpr, IRExpr)
--toInvExpr clauses adts boundVars startCN boundCN | traceShow boundCN False = undefined
toInvExpr clauseSet adts boundVars startCN boundCN = wrappedInUnappliedLambdas
  where
    -- Find the bound variable of a lambda that is not already applied
    -- This needs to be done if the lambda is a variable, 
    -- in which case the lamba expression would not be a subexpression of the expression to invert
    -- We expect lambda variables of subexpression to later be bound by a lambda. We add them as parameters, because we expect them to be bound later
    innerBoundVars = getUnappliedLambdas clauseSet startCN \\ [boundCN]
    -- Add a clause without preconditions for parameters as a starting point
    -- Define the expression to invert as known. This is true by the definition of an inverse
    paramClauses = map ParameterHornClause (startCN:innerBoundVars) -- ++ boundVars)
    -- If there are multiple paths towards the final parameter, we want to consider all paths for maximum information
    -- To do this we calculate the expression multiple times, but throw out all but one horn clause concluding to toInvCN
    terminalGroups = getTerminalGroups clauseSet boundCN

    isLambdaGroup ((ExprHornClause _ _ (LambdaInfo _) _):_) = True
    isLambdaGroup _ = False
    -- We do not want to use Lambda expressions when constructing the expression, because we assume all other lambdas to be deterministic
    intermediateSet = clauseSet \\ terminalGroups
    -- Create the expression that calculates toInvCN
    valueExprs = mapMaybe (\term -> toValueExpr (term:intermediateSet) paramClauses adts boundCN) terminalGroups
    (mergedExprs, mergedCoV) = mergeExpr valueExprs
    wrappedInUnappliedLambdas = (foldr IRLambda mergedExprs innerBoundVars, foldr IRLambda mergedCoV innerBoundVars)

getTerminalGroups :: [[HornClause]] -> ChainName -> [[HornClause]]
getTerminalGroups clauses cn = filter (any ((== cn) . conclusion)) clauses

-- This takes a list of value expressions and merges then such that in tuple constructions a existing value overwrites an ANY.
-- If two paths provide information for the same part of the tuple, we discard the second, because the should be semantically equal and therefor redundant
-- We also assume that the different paths do not have cnflicting LetIns
-- FIXME: Implement Gramian Matrix correctly, instead of multiplying all together
mergeExpr :: [(IRExpr, IRExpr)] -> (IRExpr, IRExpr)
mergeExpr [] = error "Cannot merge empty list of expressions"
mergeExpr [x] = x
mergeExpr ((x, xCoV):xs) = (removeReduntantLets [] $ mergeExpr2 id x mergedX, IROp OpMult xCoV mergedCoV)
  where (mergedX, mergedCoV) = mergeExpr xs

mergeExpr2 :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr -> IRExpr
mergeExpr2 bindings (IRLetIn n v body) expr2 = mergeExpr2 (bindings . IRLetIn n v) body expr2
mergeExpr2 bindings expr1 (IRLetIn n v body) = mergeExpr2 (bindings . IRLetIn n v) expr1 body
mergeExpr2 bindings (IRTCons (IRConst VAny) b) (IRTCons a (IRConst VAny)) = bindings $ IRTCons a b
mergeExpr2 bindings (IRTCons a (IRConst VAny)) (IRTCons (IRConst VAny) b)  = bindings $ IRTCons a b
-- Assume they are semantically equal. Then just take the first
mergeExpr2 bindings x _ = bindings x
--mergeExpr2 bindings x y = trace ("Cannot merge expressions: " ++ show x ++ show y) (bindings x)

removeReduntantLets :: [String] -> IRExpr -> IRExpr
removeReduntantLets used (IRLetIn n v body) | n `elem` used = removeReduntantLets used body
removeReduntantLets used (IRLetIn n v body) | n `notElem` used = IRLetIn n v (removeReduntantLets (n:used) body)
removeReduntantLets _ e = e

-- Creates an expression, which returns the value of a point in the AST. Takes a list of AST points, which are considered to be of known value
-- First element is the expression, second is the CoV factor
toValueExpr :: [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe (IRExpr, IRExpr)
--toValueExpr clauses paramClauses adts "x" | traceShow (paramClauses:clauses) False = undefined
toValueExpr clauses paramClauses adts startCN =
  case findConcludingHornClause solvedClauses startCN of
    Just concludingClause -> do
      -- Throw away superfluous clauses. Do this by sorting them by requirement
      -- and throwing away clauses after the clause that inferes the bound variable
      -- Also guarantees that the later generated letIns are in the correct order
      let sortedClauses = topSortDAG solvedClauses
      let relevantSortedClauses = cutList sortedClauses concludingClause
      let deriv = derivativeOfPath adts relevantSortedClauses
      -- Generate code
      Just $ (toLetInBlock clauses adts relevantSortedClauses, wrapInLetInBlock clauses adts relevantSortedClauses deriv)
    Nothing -> Nothing
  where
    augmentedClauseSet = map (:[]) paramClauses ++ clauses
    -- Solve the set of Horn clauses for clauses which are fulfilled
    solvedClauses = solveHCSet augmentedClauseSet

-- Creates a block of code from a set of sorted horn clauses
-- Generates the last horn clause as a return statement and wraps it in letIn statements created from the leading clauses
toLetInBlock :: [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
toLetInBlock clauses adts [] = error "Cannot convert empty clause set to LetIn block"
toLetInBlock clauses adts cs = wrapInLetInBlock clauses adts (init cs) (hornClauseToIRExpr clauses adts (last cs))

wrapInLetInBlock :: [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr -> IRExpr
wrapInLetInBlock clauses adts (ParameterHornClause _:cs) inner = wrapInLetInBlock clauses adts cs inner
wrapInLetInBlock clauses adts (c:cs) inner = IRLetIn (conclusion c) (hornClauseToIRExpr clauses adts c) (wrapInLetInBlock clauses adts cs inner)
wrapInLetInBlock clauses adts [] inner = inner


-- Generates IRExpr from Horn clauses
hornClauseToIRExpr :: [[HornClause]] -> [ADTDecl] -> HornClause -> IRExpr
hornClauseToIRExpr clauses adts clause =
  case clause of
    -- Constants are always their value
    ExprHornClause _ _ (ConstantInfo v) 0 -> IRConst (valueToIR v)
    -- Get the correct names of the parameters from the horn clause and instantiate the InjF
    ExprHornClause preVars _ (InjFInfo name) inv | inv == 0 ->
        let Just (FPair fwdInjF _) = lookup name (globalFEnv adts)
            renamedF = foldr (\(old, new) decl -> renameDecl old new decl) fwdInjF (zip (inputVars fwdInjF) preVars) in
              body renamedF
    -- Similar to the forward InjF, but additionally find the correct inversion first
    -- Inversions are always in the correct order in globalFEnv, because the inversion number is created from this order
    ExprHornClause preVars _ (InjFInfo name) inv -> do
      let Just (FPair _ invInjF) = lookup name (globalFEnv adts)
      let correctInv = invInjF !! (inv - 1)
      let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
      body renamedF
    -- The "value" of a lambda expression is the value of its body
    e@(ExprHornClause [preVar] _ (LambdaInfo _) _) ->
      IRVar preVar
    -- Forward pass of an application is setting the bound variable of an underlying lambda to the bound value
    ExprHornClause [preLmb, preBound] conc (StubInfo StubApply) 0 -> do
      let Just (bound, _) = findBoundVariable clauses preLmb
      IRLetIn bound (IRVar preBound) (IRVar conc)
    -- The application expression has the value of the bound expression
    ExprHornClause [preExpr] conc (StubInfo StubApply) 1 -> do
      IRVar preExpr
    -- The inverse Tuple expressions are fst and snd
    ExprHornClause [preExpr] conc (StubInfo StubTCons) 1 -> do
      IRTFst (IRVar preExpr)
    ExprHornClause [preExpr] conc (StubInfo StubTCons) 2 -> do
      IRTSnd (IRVar preExpr)
    -- Outside of the normal scope of inversions, therefor a negative inversion number
    -- If a value was applied to a bound variable, that bound variable is the applied value
    ExprHornClause [applied] _ AppliedInfo _ -> do
      IRVar applied
    -- Expect parameters to be known
    ParameterHornClause conc -> IRVar conc
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

-- Finds the first horn clause in a list that has a given conclusion
findConcludingHornClause :: [HornClause] -> ChainName -> Maybe HornClause
--findConcludingHornClause hcs cn | trace ("Find " ++ cn ++ " in " ++ show hcs) False = undefined
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> Nothing
    res -> Just $ head res

-- Finds the bound variable of the lambda the parameter ChainName is referencing
-- Note that this needs to skip over already applied lambdas
findBoundVariable :: HasCallStack => [[HornClause]] -> ChainName -> Maybe (String, ChainName)
--findBoundVariable clauses cn | trace ("SEARCH "++ show cn) False = undefined
findBoundVariable clauses = findBoundVariable' forwardClauses 0
  where
    -- Only forward clauses (inversion == 0) are relevant for this, because we dont want cycles in our graph of horn clauses
    -- Applied clauses are also relevant, because the lambda might be a variable applied elsewhere
    forwardClauses = getForwardClauses clauses ++ getAppliedClauses clauses

    -- Look at all suffixes, then take the ones that start with the split. Take the last one in the list, because it is the shortest suffix
    splitAfterLast split s = case filter (split `isPrefixOf`) (tails s) of
      [] -> ""
      xs -> last xs

-- Finds the lambda a parameter ChainName is referencing
-- This also needs to skip over applied lambdas. Because applications must happen before a lambda, 
-- keep track of the number of applications seen on the way and disregard that many lambdas
-- First return is the name of the bound variable, second is the ChainName of the lambda
findBoundVariable' :: HasCallStack => [HornClause] -> Int -> ChainName -> Maybe (String, ChainName)
--findBoundVariable' clauses applies name | trace (show name++ "|" ++ show applies) False = undefined
findBoundVariable' clauses applies name =
  -- The next lambda is what we are looking for
  if applies == 0 then
    case currClauses of
      -- We found what we are looking for
      (ExprHornClause _ cn (LambdaInfo n) _):_ -> Just (n, cn)
      -- Increase the number of applications to disregard the next lambda
      (ExprHornClause pre _ (StubInfo StubApply) _):_ -> firstJusts $ map (findBoundVariable' (clauses \\ headIfExists currClauses) (applies + 1)) pre
      -- Continue looking, but without the current clause. First with the same name, then with all possible next names
      _ -> firstJusts $ if null currClauses then [] else findBoundVariable' (clauses \\ headIfExists currClauses) applies name:
        map (findBoundVariable' (clauses \\ headIfExists currClauses) applies . conclusion) nextClauses

  -- Disregard the next lambda, because it is already applied
  else
    case currClauses of
      -- Disregard it, but decrease the number of applications
      (ExprHornClause pre _ (LambdaInfo n) _):_ -> firstJusts $ map (findBoundVariable' (clauses \\ headIfExists currClauses) (applies - 1)) pre
      -- Increase the number of applications to disregard the next lambda
      (ExprHornClause pre _ (StubInfo StubApply) _):_ -> firstJusts $ map (findBoundVariable' (clauses \\ headIfExists currClauses) (applies + 1)) pre
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

-- Returns all clauses, which are considered to be forward. This includes all clauses, which are inversion=0
-- except for clauses created by applying values, because they refference AST points backwards.
-- These clauses can be used for syntactic traversal of a program
-- This set of clauses is guaranteed cycle free and is analog to the AST
getForwardClauses :: [[HornClause]] -> [HornClause]
getForwardClauses = concatMap (filter (\c -> inversion c == 0 && not (isAppliedInfo (exprInfo c))))

-- Returns all clauses created by applying values
-- In conjunction with the forward clauses, they can be used for evaluating traversal of a prorgam.
-- For the syntactic traversal (Var x) is an atom. For evaluating traversal, there is a clause linking x to its value.
-- Because the value is applied higher up in the program, the forwardClauses with appliedClauses are NOT cycle free
getAppliedClauses :: [[HornClause]] -> [HornClause]
getAppliedClauses = concatMap (filter (\c -> isAppliedInfo (exprInfo c)))

-- Get all names of all lambda variables in a subexpression of a specific point in the AST.
-- Exclude all lambdas, which are already applied
getUnappliedLambdas :: HasCallStack => [[HornClause]] -> ChainName -> [String]
--getUnappliedLambdas clauses cn | traceShow (getForwardClauses clauses) False = undefined
getUnappliedLambdas clauses cn = inc \\ exc
  where
    -- We do not start with the firt expression directly, because it is the lambda, we want to seach the subexpressions of.
    nextClauses = filter ((== cn) . conclusion) forwardClauses
    forwardClauses = getForwardClauses clauses
    (inc, exc) = concatMap2 (getUnappliedLambdas' clauses forwardClauses) (concatMap premises nextClauses)

-- For any lambda l we want to get names of bound variables for that lambda
-- Returns a list of candidates and a list of applied lambda names. The unapplied lambda names is the difference of those lists
getUnappliedLambdas' :: HasCallStack => [[HornClause]] -> [HornClause] -> ChainName -> ([String], [String])
getUnappliedLambdas' allClauses clauses cn = case currClauses of
  -- This is an application clause of a lambda
  c@(ExprHornClause [n, _] _ (StubInfo StubApply) 0):_ ->
    let (inc, exc) = getUnappliedLambdas' allClauses (clauses \\ [c]) cn in
        -- Find the bound variable and add it to the applied return list
      case findBoundVariable allClauses n of
        Just (lambdaVar, _) -> (inc, lambdaVar:exc)
        Nothing -> (inc, exc)
  -- This is the clause for a lambda. Add its variable name to the candiate return list
  c@(ExprHornClause pre _ (LambdaInfo n) _):_ ->
    let (inc, exc) = getUnappliedLambdas' allClauses (clauses \\ [c]) cn in
      (n:inc, exc)
  -- There are more possible clauses to handle
  c:_ -> getUnappliedLambdas' allClauses (clauses \\ [c]) cn
  -- No more clauses at this level. Search all clauses, which represent subexpressions of the current level
  [] -> concatMap2 (getUnappliedLambdas' allClauses clauses) (concatMap premises nextClauses)
  where
    -- Subexpressions of the current chain name
    nextClauses = filter (\c -> (conclusion c == cn)) clauses
    -- All clauses, on the current level of the recursive descend
    currClauses = filter (elem cn . premises) clauses

-- Convert a Program to a set of groups of Horn clauses
progToHornClauses :: Program -> [[HornClause]]
progToHornClauses Program{functions=fs, adts=adts} = augmentApplyClauseSet initialRun
  where
    -- We need two runs for this: first run is every expression converted into a group of Horn clauses
    initialRun = concatMap (exprToHornClauses adts . snd) fs
    -- Second run is augmenting the clause set with fresh copies of clauses for every application
    --freshFs = evalSupply (augmentFreshApplicationsClauseSet initialRun)

-- Converts an expression with all its subexpressions into Horn clauses
exprToHornClauses :: [ADTDecl] -> Expr -> [[HornClause]]
exprToHornClauses adts e = case e of
  Constant _ v -> [[ExprHornClause [] (getChainName e) (ConstantInfo v) 0]]
  Lambda _ n body -> [ExprHornClause [getChainName body] (getChainName e) (LambdaInfo n) 0,
                      ExprHornClause [getChainName e] (getChainName body) (LambdaInfo n) 1]:
                      exprToHornClauses adts body
  Apply _ l v -> [ExprHornClause [getChainName l, getChainName v] (getChainName e) (StubInfo StubApply) 0,
                  ExprHornClause [getChainName e] (getChainName l) (StubInfo StubApply) 1]:
                  exprToHornClauses adts l ++ exprToHornClauses adts v
  -- Importantly the clauses drom the tuple are in separate groups, because they can be solved independently
  TCons _ a b -> [ExprHornClause [getChainName e] (getChainName a) (StubInfo StubTCons) 1]:
                 [ExprHornClause [getChainName e] (getChainName b) (StubInfo StubTCons) 2]:
                  exprToHornClauses adts a ++ exprToHornClauses adts b
  InjF _ _ params -> injFtoHornClause adts e: concatMap (exprToHornClauses adts) params
  -- No Horn clauses instead of error. Some expressions are not invertable and therefor do not produce Horn clauses. But we might not need them 
  _ -> []

-- Converts an instance of a InjF into a Horn clause with corresponding variables in the premises and conclusion
injFtoHornClause :: [ADTDecl] -> Expr -> [HornClause]
injFtoHornClause adts e = case e of
  -- Forward Horn clause: Inverse Horn clauses with corresponding inversion number 
  InjF t name params -> (constructInjFHornClause subst eCN name eFwd 0): zipWith (constructInjFHornClause subst eCN name) eInv [1..]
    where
      -- Create a substitution, that maps the variables in the declaration of the InjF
      -- to the ChainNames in the instantiation
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl {inputVars = inV, outputVars = [outV]} = eFwd
      Just (FPair eFwd eInv) = lookup name (globalFEnv adts)
  _ -> error "Cannot get horn clause of non-predefined function"

lambdasToHornClauses :: [Expr] -> [[HornClause]]
lambdasToHornClauses = undefined

type AssociationTable = [(ChainName, ChainName)]

searchForNewlambdaHornClauses :: AssociationTable -> Expr -> AssociationTable
-- If Apply has a lambda as its left side, then directly associate the it with the body of the lambda
searchForNewlambdaHornClauses table (Apply aTi (Lambda lTi lVar lBody) val) =
  case lookup (chainName aTi) table of
    Nothing -> (chainName aTi, getChainName lBody):table
    _ -> table
-- If Apply has anything else on its left side, look whether that is associated with anything

findExprWithCN :: [Expr] -> ChainName -> Expr
findExprWithCN exprs cn = case mapMaybe (findExprWithCN' cn) exprs of
  [e] -> e
  [] -> error "Expression with given chain name not found"
  _ -> error "Multiple expressions with the same chain name"

findExprWithCN' :: ChainName -> Expr -> Maybe Expr
findExprWithCN' cn expr | getChainName expr == cn = Just expr
findExprWithCN' cn expr = msum $ map (findExprWithCN' cn) (getSubExprs expr)

associateVariable :: AssociationTable -> [Expr] -> String -> ChainName -> Expr -> AssociationTable
associateVariable table top var associateTo (Var TypeInfo{chainName=cn} name) | var == name = (cn, associateTo):table
associateVariable table top var associateTo expr = do
  let traverseSubs = foldr (\e table -> associateVariable table top var associateTo e) table (getSubExprs expr)
  case lookup (getChainName expr) table of
    Just chainsTo -> associateVariable traverseSubs top var associateTo (findExprWithCN top chainsTo)
    Nothing -> traverseSubs

-- Creates a Horn clause of an FDecl and substitutes the variables with a substition
constructInjFHornClause :: [(String, ChainName)] -> ChainName -> String -> FDecl -> Int -> HornClause
constructInjFHornClause subst cn name decl inv = ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv
  where
    FDecl {inputVars = inV, outputVars = [outV]} = decl
    lookupSubst v = fromJust (lookup v subst)

-- Application implies that the bound variable of the lambda expression is equal to the applied expression.
-- This step requires knowledge of the program structure and can therefor only be done after the clause set is constructed
augmentApplyClauseSet :: [[HornClause]] -> [[HornClause]]
augmentApplyClauseSet clauses = fixpoint aug clauses
  where
    aug curr = nub $ filter (not . null) (map (augmentApplyClauseSet' curr) curr ++ curr)
    fixpoint f x
      | x == f x = x
      | otherwise = fixpoint f (f x)

augmentApplyClauseSet' :: [[HornClause]] -> [HornClause] -> [HornClause]
augmentApplyClauseSet' clauses (c@(ExprHornClause [l, v] cn (StubInfo StubApply) 0):_) =
  case findBoundVariable clauses l of
    Just (bound, _) -> [ExprHornClause [v] bound AppliedInfo 0,
      ExprHornClause [bound] v AppliedInfo 1]
    Nothing -> []
augmentApplyClauseSet' _ x = []

-- TODO: This assumes that derivativs are composable, which (I think) is not true in general
derivativeOfPath :: [ADTDecl] -> [HornClause] -> IRExpr
derivativeOfPath adts clauses = foldr1 (IROp OpMult) derivs
  where derivs = map (derivativeOfHornClause adts) clauses

derivativeOfHornClause :: [ADTDecl] -> HornClause -> IRExpr
derivativeOfHornClause adts (ExprHornClause pre conc (InjFInfo name) inv) | inv > 0 = do
  let FPair injFFwdDecl injFInvDecls = fromJust $ lookup name (globalFEnv adts)
  let correctDecl = injFInvDecls !! (inv - 1)
  -- The premises of the of the HornClause are the input of the inverse InjF
  let FDecl {derivatives=invDerivs} = foldr (\(old, new) decl -> renameDecl old new decl) correctDecl (zip (inputVars correctDecl) pre)
  -- We need to find out which variable is the output of the forward InjF. For this take the fwd InjF and do the same renaming as for the inverse
  let FDecl {outputVars=[invVar]} = foldr (\(old, new) decl -> renameDecl old new decl) injFFwdDecl (zip (inputVars correctDecl) pre)
  fromJust $ lookup invVar invDerivs
derivativeOfHornClause _ _ = IRConst (VFloat 1.0)

-- Chain name of subexpressions
getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map getChainName (getSubExprs e)

-- Annotates a Program with chain names for every expression
annotateProg :: Program -> Program
annotateProg p@Program {functions=fs} = chainsToTagged
  -- Map annotateExpr on all functions. The code is ugly because of monad shenanigans
  where
    annotFs = evalSupply (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)
    -- Sets the ChainName of the top level expression to the name of the top level expression
    correctTopLevel = map (\(n, f) -> (n, setTypeInfo f (setChainName (getTypeInfo f) n))) annotFs
    chainsToTagged = tagChainsTo p{functions=correctTopLevel}

-- Annotate an expression and all of its subexpressions
annotateExpr :: Expr -> Supply Expr
annotateExpr = tMapM (\ex -> do
  case ex of
    Var TypeInfo{rType=(TArrow _ _)} n -> demandUniqueNumber <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
    -- Variables have itself as its ChainName
    Var t n -> return $ setChainName t n
    _ -> demandUniqueNumber <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
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

-- Returns all elements that come before a given parameter in a list
cutList :: Eq a => [a] -> a -> [a]
cutList [] _ = []
cutList (x:xs) stop
  | x == stop = [x]
  | otherwise = x : cutList xs stop


-- Define a DAG Edge that corresponds to dependancy. A is less than B if B depends on A 
instance DAGEdge HornClause where
  -- A <= B iff B depends on A
  ExprHornClause {conclusion=conc1} `edge` ExprHornClause {premises'=pre2} = conc1 `elem` pre2
  _ `edge` _ = False

-- Define DAG edges of HornClause groups based on the forward clause
instance DAGEdge [HornClause] where
  xs `edge` ys = not eitherEmpty && head possibleX `edge` head possibleY
    where
      possibleX = filter (\x -> inversion x == 0 && not (isAppliedInfo (exprInfo x))) xs
      possibleY = filter (\y -> inversion y == 0 && not (isAppliedInfo (exprInfo y))) ys
      eitherEmpty = null possibleX || null possibleY