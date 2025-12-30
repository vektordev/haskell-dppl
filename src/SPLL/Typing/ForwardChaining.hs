{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module SPLL.Typing.ForwardChaining where
import SPLL.Lang.Types hiding (HornClause)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types (Program(Program))
import Data.Bifunctor
import Data.Functor ((<&>))
import SPLL.Lang.Lang
import PredefinedFunctions
import Data.List ((\\), delete, nub, isPrefixOf, tails, intercalate, group)
import Data.Maybe
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Debug.Trace
import GHC.Stack (HasCallStack)
import Utils
import SPLL.Typing.RType
import qualified Text.Megaparsec.Char as ANY
import Data.Char (isDigit)
import Data.List.NonEmpty (nonEmpty)
import GHC.Base (empty)



data FCData = FCData {hornClauses :: [[HornClause]], chainNameInfo :: [(ChainName, ExprInfo)]}

-- Information on what type of expression a HornClause originated from
data ExprInfo = StubInfo ExprStub   -- Generic Expression without additional Info
              | InjFInfo String     -- InjF with the name of the InjF
              | LambdaInfo String ChainName  -- Lambda with the name of the bound variable and the ChainName of the body
              | ConstantInfo Value  -- Contant with the value
              | VarInfo String
              | ApplyInfo ChainName ChainName -- Chain name of the left parameter of the Apply
              | AppliedInfo         -- Does not directly correlate to an expression. Via application a value is assigned to a bound variable
              deriving (Eq, Show)

data EquivalenceType = VariableEquivalence String
                     | AppliedEquivalence
                     deriving (Eq, Show)

-- Horn clauses state: When all premises are known, we can derive the conclusion. Expression info holds information about the original expression.
-- inversion represents which direction the HornClause represents. E.g.
-- Original: a = b + c
-- Inversion 0: b, c -> a
-- Inversion 1: a, c -> b
-- Inversion 2: a, b -> c
-- Parameter HornClauses define a ChainName to be known. This could represent the sample passed to the top-level expression, or the parameter passed to an inverse expression
data HornClause = ExprHornClause {premises' :: [ChainName], conclusion :: ChainName, exprInfo :: ExprInfo, inversion :: Int}
                | EquivalenceHornClause {premises' :: [ChainName], conclusion :: ChainName, equivalenceType :: EquivalenceType, inversion :: Int}
                | ParameterHornClause {conclusion :: ChainName} deriving (Eq, Show)

-- Wraps the premises field, because ParameterHornClauses have an empty set of premises by definition
premises :: HornClause -> [ChainName]
premises ParameterHornClause {} = []
premises ExprHornClause {premises'=p} = p
premises EquivalenceHornClause {premises'=p} = p

getChainName :: Expr -> ChainName
getChainName = chainName . getTypeInfo

isAppliedInfo :: ExprInfo -> Bool
isAppliedInfo AppliedInfo = True
isAppliedInfo _ = False

isEquivalenceHornClause :: HornClause -> Bool
isEquivalenceHornClause (EquivalenceHornClause {}) = True
isEquivalenceHornClause _ = False

isExprHornClause :: HornClause -> Bool
isExprHornClause (ExprHornClause {}) = True
isExprHornClause _ = False

isAppliedEquivalence :: EquivalenceType -> Bool
isAppliedEquivalence AppliedEquivalence = True
isAppliedEquivalence _ = False

-- Takes all HornClauses of a Program and a point in the AST which should be inverted.
-- The function then searches for a Lambda statement and inverses toward the bound variable
-- Note that it deliberately skips over lambdas that are already applied
toInvExpr :: FCData -> [ADTDecl] -> ChainName -> (IRExpr, IRExpr)
--toInvExpr clauses adts startCN | traceShow startCN False = undefined
toInvExpr fcData adts lambdaCN = (mergedM, mergedCoV)
  where
    clauseSet = hornClauses fcData
    -- Find the bound variable of a lambda that is not already applied
    -- This needs to be done if the lambda is a variable, 
    -- in which case the lamba expression would not be a subexpression of the expression to invert
    {-toInvCN = case findBoundVariable clauseSet startCN of
      Just cn -> cn
      Nothing -> error $ "Cannot find bound variable of expression: " ++ startCN
    -- We expect lambda variables of subexpression to later be bound by a lambda. We add them as parameters, because we expect them to be bound later
    boundVars = getUnappliedLambdas clauseSet startCN \\ [toInvCN]
    -- Add a clause without preconditions for parameters as a starting point
    -- Define the expression to invert as known. This is true by the definition of an inverse
    
    -- If there are multiple paths towards the final parameter, we want to consider all paths for maximum information
    -- To do this we calculate the expression multiple times, but throw out all but one horn clause concluding to toInvCN-}
    (LambdaInfo toInvVarName lambdaBodyCN, tag) = findEquivalentLambda fcData lambdaCN
    toInvCN = findChainNameForVar fcData toInvVarName ++ tag
    (unwrappedChainName, lambdaVars) = unwrapLambdas fcData lambdaBodyCN
    paramClause = ParameterHornClause (unwrappedChainName ++ tag)
    terminalGroups = getTerminalGroups clauseSet toInvCN
    intermediateSet = clauseSet \\ terminalGroups
    -- Create the expression that calculates toInvCN
    valueExprs = mapMaybe (\term -> toValueExpr (term:intermediateSet) [paramClause] adts toInvCN) terminalGroups
    (mergedM, mergedCoV) = mergeExpr valueExprs

findChainNameForVar :: FCData -> String -> ChainName
findChainNameForVar fcData varName = case correctVarInfos of
  [(cn, _)] -> cn
  [] -> error "Could not find variable " ++ varName ++ " in FC data"
  _ -> error "Multiple occurances of  " ++ varName ++ " in FC data"
  where
    correctVarInfos = filter (isCorrectVarInfo varName . snd) (chainNameInfo fcData)
    isCorrectVarInfo name (VarInfo n) | name == n = True
    isCorrectVarInfo _ _ = False

unwrapLambdas :: FCData -> ChainName -> (ChainName, [String])
unwrapLambdas fcData cn = case lookup cn (chainNameInfo fcData) of
  Just (LambdaInfo name bodyName) ->
    let (lCN, names) = unwrapLambdas fcData bodyName in (lCN, name:names)
  Just _ -> (cn, [])

getTerminalGroups :: [[HornClause]] -> ChainName -> [[HornClause]]
getTerminalGroups clauses cn = filter (any ((== cn) . conclusion)) clauses

-- This takes a list of value expressions and merges then such that in tuple constructions a existing value overwrites an ANY.
-- If two paths provide information for the same part of the tuple, we discard the second, because the should be semantically equal and therefor redundant
-- We also assume that the different paths do not have conflicting LetIns
-- FIXME: Implement Gramian Matrix correctly, instead of multiplying all together
mergeExpr :: [(IRExpr, IRExpr)] -> (IRExpr, IRExpr)
mergeExpr [] = error "Cannot merge empty list of expressions"
mergeExpr [x] = x
mergeExpr (x:xs) = mergeExpr2 id x (mergeExpr xs)

mergeExpr2 :: (IRExpr -> IRExpr) -> (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> (IRExpr, IRExpr)
mergeExpr2 bindings (IRLetIn n v body, cov1) expr2 = mergeExpr2 (bindings . IRLetIn n v) (body, cov1) expr2
mergeExpr2 bindings expr1 (IRLetIn n v body, cov2) = mergeExpr2 (bindings . IRLetIn n v) expr1 (body, cov2)
mergeExpr2 bindings (IRTCons (IRConst VAny) b, cov1) (IRTCons a (IRConst VAny), cov2) = (bindings $ IRTCons a b, IROp OpMult cov1 cov2)
mergeExpr2 bindings (IRTCons a (IRConst VAny), cov1) (IRTCons (IRConst VAny) b, cov2)  = (bindings $ IRTCons a b, IROp OpMult cov1 cov2)
-- Assume they are semantically equal. Then just take the first
mergeExpr2 bindings (expr1, cov1) _ = (bindings expr1, cov1)
--mergeExpr2 bindings x y = trace ("Cannot merge expressions: " ++ show x ++ show y) (bindings x)


removeReduntantLets :: [String] -> IRExpr -> IRExpr
removeReduntantLets used (IRLetIn n v body) | n `elem` used = removeReduntantLets used body
removeReduntantLets used (IRLetIn n v body) | n `notElem` used = IRLetIn n v (removeReduntantLets (n:used) body)
removeReduntantLets _ e = e

-- Creates an expression, which returns the value of a point in the AST. Takes a list of AST points, which are considered to be of known value
toValueExpr :: [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe (IRExpr, IRExpr)
--toValueExpr clauses paramClauses adts startCN | trace (startCN ++ " || " ++ show clauses) False = undefined
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

findEquivalentLambda :: FCData -> ChainName -> (ExprInfo, String)
--findEquivalentLambda fcData startCN | trace startCN False = undefined
findEquivalentLambda fcData startCN = case lookup startCN (chainNameInfo fcData) of
  Nothing -> error $ "Could not find chainName in FCData " ++ startCN
  Just li@(LambdaInfo _ _) -> (li, "")
  Just _ -> do
    let origClauses = getAllOriginatingEquivalenceHornClauses (hornClauses fcData) startCN
    let [EquivalenceHornClause [pre] _ _ _] = filter (\(EquivalenceHornClause _ conc ty inv) -> inv == 1) origClauses
    (fst $ findEquivalentLambda fcData (untag pre), getTag pre)

getAllOriginatingEquivalenceHornClauses :: [[HornClause]] -> ChainName -> [HornClause]
getAllOriginatingEquivalenceHornClauses clauses cn = concatMap (filter (\hc -> isEquivalenceHornClause hc && conclusion hc == cn)) clauses

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
    {-e@(ExprHornClause [preVar] _ (LambdaInfo _) 1) ->
      IRVar preVar
    -- Forward pass of an application is setting the bound variable of an underlying lambda to the bound value
    ExprHornClause [preLmb, preBound] conc (StubInfo StubApply) 0 -> do
      let Just bound = findBoundVariable clauses preLmb
      IRLetIn bound (IRVar preBound) (IRVar conc)
    -- The application expression has the value of the bound expression
    ExprHornClause [preExpr] conc (StubInfo StubApply) 1 -> do
      IRVar preExpr
    -- Outside of the normal scope of inversions, therefor a negative inversion number
    -- If a value was applied to a bound variable, that bound variable is the applied value
    ExprHornClause [applied] _ AppliedInfo _ -> do
      IRVar applied
    -- Expect parameters to be known
    -}
    ExprHornClause [preExpr] conc (StubInfo StubTCons) 1 -> do
      IRTFst (IRVar preExpr)
    ExprHornClause [preExpr] conc (StubInfo StubTCons) 2 -> do
      IRTSnd (IRVar preExpr)
    ParameterHornClause conc -> IRVar conc
    EquivalenceHornClause [p] _ _ _ -> IRVar p
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

-- Finds the first horn clause in a list that has a given conclusion
findConcludingHornClause :: [HornClause] -> ChainName -> Maybe HornClause
--findConcludingHornClause hcs cn | trace ("Find " ++ cn ++ " in " ++ show hcs) False = undefined
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> Nothing
    res -> Just $ head res

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

-- Finds the bound variable of the lambda the parameter ChainName is referencing
-- Note that this needs to skip over already applied lambdas
{-findBoundVariable :: HasCallStack => [[HornClause]] -> ChainName -> Maybe ChainName
--findBoundVariable clauses cn | trace ("SEARCH "++ show cn) False = undefined
findBoundVariable clauses cn = findBoundVariable' forwardClauses 0 cn <&> (++ suffix)
  where
    -- Only forward clauses (inversion == 0) are relevant for this, because we dont want cycles in our graph of horn clauses
    -- Applied clauses are also relevant, because the lambda might be a variable applied elsewhere
    forwardClauses = getForwardClauses clauses ++ getAppliedClauses clauses
    -- If chain name is tagged with a suffix, we need to tag the return with the same suffix
    -- FIXME: If the varibale has a _ in it this does not work correctly
    suffix = splitAfterLast "_c" cn
    -- Look at all suffixes, then take the ones that start with the split. Take the last one in the list, because it is the shortest suffix
    splitAfterLast split s = case filter (split `isPrefixOf`) (tails s) of
      [] -> ""
      xs -> last xs

-- Finds the lambda a parameter ChainName is referencing
-- This also needs to skip over applied lambdas. Because applications must happen before a lambda, 
-- keep track of the number of applications seen on the way and disregard that many lambdas
findBoundVariable' :: HasCallStack => [HornClause] -> Int -> ChainName -> Maybe ChainName
--findBoundVariable' clauses applies name | trace (show name++ "|" ++ show applies) False = undefined
findBoundVariable' clauses applies name =
  -- The next lambda is what we are looking for
  if applies == 0 then
    case currClauses of
      -- We found what we are looking for
      (ExprHornClause _ _ (LambdaInfo n) _):_ -> Just n
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
-}
-- Returns all clauses, which are considered to be forward. This includes all clauses, which are inversion=0
-- except for clauses created by applying values, because they refference AST points backwards.
-- These clauses can be used for syntactic traversal of a program
-- This set of clauses is guaranteed cycle free and is analog to the AST
{-getForwardClauses :: [[HornClause]] -> [HornClause]
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
        Just lambdaVar -> (inc, lambdaVar:exc)
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
    currClauses = filter (elem cn . premises) clauses -}

progToFCData :: Program -> FCData
progToFCData prog = FCData {hornClauses = progToHornClauses prog cnInfo, chainNameInfo = progToChainNameInfo prog}
  where cnInfo = progToChainNameInfo prog


progToChainNameInfo :: Program -> [(ChainName, ExprInfo)]
progToChainNameInfo Program{functions=fs} = concatMap (exprToChainNameInfo . snd) fs

exprToChainNameInfo :: Expr -> [(ChainName, ExprInfo)]
exprToChainNameInfo (Lambda TypeInfo{chainName=cn} n b) = (cn, LambdaInfo n (getChainName b)):exprToChainNameInfo b
exprToChainNameInfo (Constant TypeInfo{chainName=cn} v) = [(cn, ConstantInfo v)]
exprToChainNameInfo (Var TypeInfo{chainName=cn} n) = [(cn, VarInfo n)]
exprToChainNameInfo (Apply TypeInfo{chainName=cn} l v) = (cn, ApplyInfo (getChainName l) (getChainName v)):exprToChainNameInfo l ++ exprToChainNameInfo v
exprToChainNameInfo e = (getChainName e, StubInfo (toStub e)):concatMap exprToChainNameInfo (getSubExprs e)

-- Convert a Program to a set of groups of Horn clauses
progToHornClauses :: Program -> [(ChainName, ExprInfo)] -> [[HornClause]]
progToHornClauses Program{functions=fs, adts=adts} cnInfo = initialRun ++ equivClauses
  where
    -- We need two runs for this: first run is every expression converted into a group of Horn clauses
    initialRun = concatMap (exprToHornClauses adts . snd) fs
    equivClauses = lambdasToHornClauses initialRun fs
    --taggedGroups = tagAppliedGroups (FCData (equivClauses ++ initialRun) cnInfo)
    -- Second run is augmenting the clause set with fresh copies of clauses for every application
    --freshFs = evalSupply (augmentFreshApplicationsClauseSet initialRun)

-- Converts an expression with all its subexpressions into Horn clauses
exprToHornClauses :: [ADTDecl] -> Expr -> [[HornClause]]
exprToHornClauses adts e = case e of
  Constant _ v -> [[ExprHornClause [] (getChainName e) (ConstantInfo v) 0]]
  {-Lambda _ n body -> [ExprHornClause [getChainName body] (getChainName e) (LambdaInfo n) 0,
                      ExprHornClause [getChainName e] (getChainName body) (LambdaInfo n) 1]:
                      exprToHornClauses adts body
  Apply _ l v -> [ExprHornClause [getChainName l, getChainName v] (getChainName e) (StubInfo StubApply) 0,
                  ExprHornClause [getChainName e] (getChainName l) (StubInfo StubApply) 1]:
                  exprToHornClauses adts l ++ exprToHornClauses adts v-}
  -- Importantly the clauses drom the tuple are in separate groups, because they can be solved independently
  TCons _ a b -> [ExprHornClause [getChainName e] (getChainName a) (StubInfo StubTCons) 1]:
                 [ExprHornClause [getChainName e] (getChainName b) (StubInfo StubTCons) 2]:
                  exprToHornClauses adts a ++ exprToHornClauses adts b
  InjF _ _ params -> injFtoHornClause adts e: concatMap (exprToHornClauses adts) params
  -- No Horn clauses instead of error. Some expressions are not invertable and therefor do not produce Horn clauses. But we might not need them 
  _ -> concatMap (exprToHornClauses adts) (getSubExprs e)

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

-- Creates a Horn clause of an FDecl and substitutes the variables with a substition
constructInjFHornClause :: [(String, ChainName)] -> ChainName -> String -> FDecl -> Int -> HornClause
constructInjFHornClause subst cn name decl inv = ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv
  where
    FDecl {inputVars = inV, outputVars = [outV]} = decl
    lookupSubst v = fromJust (lookup v subst)

getEquivCN :: [[HornClause]] -> ChainName -> ChainName
getEquivCN clauses cn = case (filter (\(EquivalenceHornClause [pre] _ _ _) -> pre == cn)) equiv of
  [EquivalenceHornClause _ back _ _] -> back
  [] -> error $ "Found no equivalent chain name to: " ++ cn
  _ ->  error $ "Found multiple equivalent chain name to: " ++ cn
  where
    equiv = filter isEquivalenceHornClause (map head clauses)

lambdasToHornClauses :: [[HornClause]] -> [FnDecl] -> [[HornClause]]
lambdasToHornClauses clauses fns = fixpoint fExprs clauses
  where
    fExprs = map snd fns
    fixpoint exprs cs = let extension = concatMap (constructEquivalenceClauses cs fExprs) exprs in if null extension then cs else fixpoint exprs (extension ++ cs)

constructEquivalenceClauses :: [[HornClause]] -> [Expr] -> Expr -> [[HornClause]]
constructEquivalenceClauses clauses exprs ex@(Apply TypeInfo{chainName=exCn} l v) | not (isInClauseSet clauses exCn) && (isLambda l || isInClauseSet clauses (getChainName l)) = do
    -- Find the declaration of the lambda on the left side of the Apply. Trivial if the lambda is directly there, else follow equivalences
    let (lCn, lTag, lVar, lBody) = case l of
          Lambda TypeInfo{chainName=lCn'} n body -> (lCn', "", n, body)
          _ -> 
            let appliedLambdaCn = getEquivCN clauses (getChainName l)
                appliedLambdaTag = getTag appliedLambdaCn
                Lambda _ name body = findExprWithCN exprs (untag appliedLambdaCn) in
                  (appliedLambdaCn, appliedLambdaTag, name, body)
    let lBodyCn = getChainName lBody ++ lTag
    let appliedGroup = createEquivHornClauseGroup AppliedEquivalence exCn lBodyCn
    case rType (getTypeInfo v) of
      TArrow _ _ -> do
        let vLambdaCn = case v of
              (Lambda TypeInfo{chainName = vlCn} _ _) -> vlCn
              _ -> getEquivCN clauses (getChainName v)
        let Lambda _ _ vBody = findExprWithCN exprs vLambdaCn
        let dependent = getDependentGroups clauses (getChainName vBody)
        let (varClauses, applyCnt) = evalSupply $ associateFunctionVariable lVar vLambdaCn lTag lBody
        let taggedDependents = concatMap (\tag -> map (tagGroup tag) dependent) [0..applyCnt - 1]
        appliedGroup:varClauses ++ taggedDependents
      _ -> 
        let taggedGroups = if null lTag then [] else map (map (tagHornClause lTag)) (getDependentGroups clauses (getChainName lBody)) in
        appliedGroup:taggedGroups ++ associateVariable lVar (getChainName v) lTag lBody
          
          
        
  where
    isLambda (Lambda {}) = True
    isLambda _ = False
constructEquivalenceClauses clauses exprs ex = concatMap (constructEquivalenceClauses clauses exprs) (getSubExprs ex)


isInClauseSet :: [[HornClause]] -> ChainName -> Bool
isInClauseSet clauses cn = any (\cs -> premises (getForwardClauseOfGroup cs) == [cn] && isEquivalenceHornClause (getForwardClauseOfGroup cs)) clauses

associateVariable :: String -> ChainName -> String -> Expr -> [[HornClause]]
associateVariable varName chainTo tag (Var TypeInfo{chainName=cn} n) | n == varName = [createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) chainTo]
associateVariable varName chainTo tag ex = concatMap (associateVariable varName chainTo tag) (getSubExprs ex)

associateFunctionVariable :: String -> ChainName -> String -> Expr -> Supply ([[HornClause]], Int)
associateFunctionVariable varName chainTo tag (Var TypeInfo{chainName=cn} n) | n == varName = demandUniqueNumber <&> \num -> ([createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) (chainTo ++ tagPrefix ++ show num)], 1)
associateFunctionVariable varName chainTo tag ex = do
  a <- mapM (associateFunctionVariable varName chainTo tag) (getSubExprs ex)
  return (concatMap fst a, sum (map snd a))

createEquivHornClauseGroup :: EquivalenceType -> ChainName -> ChainName -> [HornClause]
createEquivHornClauseGroup ty cn1 cn2 = [EquivalenceHornClause [cn1] cn2 ty 0, EquivalenceHornClause [cn2] cn1 ty 1]

findExprWithCN :: [Expr] -> ChainName -> Expr
findExprWithCN exprs cn = case mapMaybe (findExprWithCN' cn) exprs of
  [e] -> e
  [] -> error $ "Expression with given chain name not found " ++ cn
  _ -> error $ "Multiple expressions with the same chain name" ++ cn

findExprWithCN' :: ChainName -> Expr -> Maybe Expr
findExprWithCN' cn expr | getChainName expr == cn = Just expr
findExprWithCN' cn expr = msum $ map (findExprWithCN' cn) (getSubExprs expr)


tagAppliedGroups :: FCData -> [[HornClause]]
tagAppliedGroups fcData = withoutRemoved ++ independentGroups
  where
    clauses = hornClauses fcData
    applyClauses = filter (\c -> isEquivalenceHornClause (getForwardClauseOfGroup c) && isAppliedEquivalence (equivalenceType (getForwardClauseOfGroup c))) clauses
    --nonApplyClauses = clauses \\ applyClauses
    -- Applies that do not apply a variable on its left side. Ignore them and add them back later
    --nonVariableApplies = map fst $ filter (isNothing . snd) (map (\c -> (c, getApplyVar fcData (getForwardClauseOfGroup c))) applyClauses)
    appliedVarClauses = map (second fromJust) $ filter (isJust . snd) (map (\c -> (c, getApplyVar fcData (getForwardClauseOfGroup c))) applyClauses)
    dependentGroups = map (\(apGroup, n@(var, (lCn, vCn))) -> let (EquivalenceHornClause [src] dst AppliedEquivalence 0) = getForwardClauseOfGroup apGroup in (apGroup:getLamdbaEquivalenceClauses fcData lCn:getDependentGroups clauses src, n)) appliedVarClauses
    independentGroups = foldr ((\dependent remaining -> remaining \\ dependent)) clauses (map fst dependentGroups)
    taggedGroups = evalSupply $ mapM (\(cs, n) -> demandUniqueNumber <&> \num -> (map (tagGroup num) cs, n)) dependentGroups
    -- The applied equiv clauses are by construction above always the first group
    reconstructAppliedEquivClauseGroups = map (\(c:cs, n) -> (reconstructAppliedEquivClauseGroup c:cs, n)) taggedGroups
    reconstructedLambdaVarEquivClauses = map (\(group, (varName, (lCn, vCn))) -> (map (map (reconstructLambdaVarEquivClause lCn)) group, (varName, (lCn, vCn)))) reconstructAppliedEquivClauseGroups
    reconstructedBoundVarEquivClauses = concatMap (\(group, (varName, (lCn, vCn))) -> map (map (reconstructBoundVarEquivClause varName vCn)) group) reconstructedLambdaVarEquivClauses
    withoutRemoved = filter (not . null) (map catMaybes reconstructedBoundVarEquivClauses)

reconstructBoundVarEquivClause :: String -> ChainName -> HornClause -> Maybe HornClause
--reconstructBoundVarEquivClause var vCn clause | trace ("Reconstructing: " ++ var ++ " in " ++ show clause) False = undefined
reconstructBoundVarEquivClause var vCn clause@(EquivalenceHornClause [pre] conc (VariableEquivalence varName) 0) =
        if var == varName then
          if untag pre == vCn then
            Just $ EquivalenceHornClause [untag pre] conc (VariableEquivalence varName) 0
          else Nothing
        else
          Just clause
reconstructBoundVarEquivClause var vCn clause@(EquivalenceHornClause [pre] conc (VariableEquivalence varName) 1) =
        if var == varName then
          if untag conc == vCn then
            Just $ EquivalenceHornClause [pre] (untag conc) (VariableEquivalence varName) 1
          else Nothing
        else
          Just clause
reconstructBoundVarEquivClause var vCn x = Just x
  where
    isCorrectVarInfo name (VarInfo n) | name == n = True
    isCorrectVarInfo _ _ = False

reconstructLambdaVarEquivClause :: ChainName -> HornClause -> HornClause
--reconstructBoundVarEquivClause var vCn clause | trace ("Reconstructing: " ++ var ++ " in " ++ show clause) False = undefined
reconstructLambdaVarEquivClause lCn clause@(EquivalenceHornClause [pre] conc (VariableEquivalence varName) 0) | untag conc == lCn =
  EquivalenceHornClause [pre] (untag conc) (VariableEquivalence varName) 0
reconstructLambdaVarEquivClause lCn clause@(EquivalenceHornClause [pre] conc (VariableEquivalence varName) 1) | untag pre == lCn =
  EquivalenceHornClause [untag pre] conc (VariableEquivalence varName) 1
reconstructLambdaVarEquivClause lCn x = x
  where
    isCorrectVarInfo name (VarInfo n) | name == n = True
    isCorrectVarInfo _ _ = False

reconstructAppliedEquivClauseGroup :: [HornClause] -> [HornClause]
reconstructAppliedEquivClauseGroup group = [EquivalenceHornClause [pre0] (untag conc0) AppliedEquivalence 0, EquivalenceHornClause [untag pre1] conc1 AppliedEquivalence 1]
  where
    [EquivalenceHornClause [pre0] conc0 AppliedEquivalence 0] = filter ((== 0). inversion) group
    [EquivalenceHornClause [pre1] conc1 AppliedEquivalence 1] = filter ((== 1). inversion) group

tagPrefix = "_t"

untag :: String -> String
untag = fst . splitByString tagPrefix

getTag :: String -> String
getTag = snd . splitByString tagPrefix

tagGroup :: Int -> [HornClause] -> [HornClause]
tagGroup tagNum group = do
  let tag = tagPrefix ++ show tagNum
  map (tagHornClause tag) group

tagHornClause :: String -> HornClause -> HornClause
tagHornClause tag (ExprHornClause pre conc info inv) = ExprHornClause (map (++ tag) pre) (conc ++ tag) info inv
tagHornClause tag (EquivalenceHornClause pre conc info inv) = EquivalenceHornClause (map (++ tag) pre) (conc ++ tag) info inv

getLamdbaEquivalenceClauses :: FCData -> ChainName -> [HornClause]
getLamdbaEquivalenceClauses fcData lCn = correctGroup
  where
    [correctGroup] = filter (\group -> (conclusion (getForwardClauseOfGroup group) == lCn) && isEquivalenceHornClause (getForwardClauseOfGroup group)) (hornClauses fcData)

-- Is the given Apply Equivalence horn clause applying a Var expression
-- This is relevant, because we only need to tag applications of Var expressions
getApplyVar :: FCData -> HornClause -> Maybe (String, (ChainName, ChainName))
--getApplyVar fcData c | traceShow c False = undefined
getApplyVar fcData (EquivalenceHornClause [src] dst AppliedEquivalence 0) = do
  case lookup dst (chainNameInfo fcData) of
    Just (ApplyInfo lCn vCn) -> case lookup lCn (chainNameInfo fcData) of
      -- Check whether the left side of the Apply is a variable. If not we don't need to do anything
      Just (VarInfo _) -> Just $ case lookup (getEquivCN (hornClauses fcData) lCn) (chainNameInfo fcData) of
        Just (LambdaInfo name _) -> (name, (lCn, vCn))
        _ -> error $ "Could not find lambda parameter of " ++ dst
      _ -> Nothing

getDependentGroups :: [[HornClause]] -> ChainName -> [[HornClause]]
getDependentGroups clauses cn = directDependence cn ++ concatMap (getDependentGroups clauses) (concatMap forwardPremises (directDependence cn))
  where
    -- Variable equivalences work the other way around as other clauses
    --forwardConclusion cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc && isVariableEquivalence (equivalenceType fc) then head $ premises fc else conclusion fc
    forwardConclusion = conclusion . getForwardClauseOfGroup
    -- We want to include the equivalence clauses in the dependent clauses, but don't want to follow their jumps
    forwardPremises cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc then [] else premises fc
    --forwardPremises = premises . getForwardClauseOfGroup
    directDependence c = filter (\cs -> forwardConclusion cs == c) clauses
    isVariableEquivalence (VariableEquivalence _) = True
    isVariableEquivalence _ = False


getForwardClauseOfGroup :: [HornClause] -> HornClause
getForwardClauseOfGroup clauses = case filter (\c -> (isExprHornClause c || isEquivalenceHornClause c) && inversion c == 0) clauses of
  [x] -> x
  [] -> error $ "Found no forward clause in clause group: " ++ show clauses
  _ -> error $ "Found multiple forward clauses in clause group: " ++ show clauses

-- Chain name of subexpressions
getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map getChainName (getSubExprs e)

-- Annotates a Program with chain names for every expression
annotateProg :: Program -> Program
annotateProg p@Program {functions=fs} = p{functions=annotFs}
  -- Map annotateExpr on all functions. The code is ugly because of monad shenanigans
  where
    annotFs = evalSupply (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)
    -- Sets the ChainName of the top level expression to the name of the top level expression
    -- correctTopLevel = map (\(n, f) -> (n, setTypeInfo f (setChainName (getTypeInfo f) n))) annotFs

-- Annotate an expression and all of its subexpressions
annotateExpr :: Expr -> Supply Expr
annotateExpr = tMapM (\ex -> do
  case ex of
    --Var TypeInfo{rType=(TArrow _ _)} n -> demandUniqueNumber <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex)
    -- Variables have itself as its ChainName
    --Var t n -> return $ setChainName t n
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
  edge :: HornClause -> HornClause -> Bool
  c1 `edge` c2 = conclusion c1 `elem` premises c2

{-}
-- Define DAG edges of HornClause groups based on the forward clause
instance DAGEdge [HornClause] where
  xs `edge` ys = not eitherEmpty && head possibleX `edge` head possibleY
    where
      possibleX = filter (\x -> inversion x == 0 && not (isAppliedInfo (exprInfo x))) xs
      possibleY = filter (\y -> inversion y == 0 && not (isAppliedInfo (exprInfo y))) ys
      eitherEmpty = null possibleX || null possibleY

-}

showClause :: HornClause -> [Char]
showClause (ExprHornClause pre conc info inv) = show pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Expression) " ++ show info
showClause (EquivalenceHornClause [pre] conc info inv) = pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Equivalence) " ++ show info
showClause (ParameterHornClause param) = "Parameter " ++ param

showClauseGroup :: [HornClause] -> String
showClauseGroup cs = intercalate "\n" (map showClause cs)

showClauseGroups :: [[HornClause]] -> String
showClauseGroups groups = intercalate "\n\n" (map showClauseGroup groups)

traceShowClauseGroupId :: [HornClause] -> [HornClause]
traceShowClauseGroupId clauses = trace (showClauseGroup clauses) clauses

traceShowClauseGroupsId :: [[HornClause]] -> [[HornClause]]
traceShowClauseGroupsId clauses = trace (showClauseGroups clauses) clauses

