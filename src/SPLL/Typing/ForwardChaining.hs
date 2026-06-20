{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module SPLL.Typing.ForwardChaining
  ( FCData(..)
  , ExprInfo(..)
  , annotateProg
  , progToFCData
  , toInvExpr
  , isInvertibleLambda
  , findEquivalentExpression
  , findExprWithCN
  , unwrapLambdas
  , untag
  ) where
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import Data.Functor ((<&>))
import SPLL.Lang.Lang
import PredefinedFunctions
import Data.List (nub, intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Utils
import SPLL.Typing.RType



data FCData = FCData
  { hornClauses :: [[HornClause]]
  , chainNameInfo :: [(ChainName, ExprInfo)]
  -- | The determinism field's known-anchor set seeded into 'hornClauses'. Kept
  -- around so codegen (IRCompiler) can materialise the value of any non-constant
  -- anchor a forward-chaining inverse path lands on.
  , fcAnchors :: Set ChainName
  }

-- Information on what type of expression a HornClause originated from
data ExprInfo = StubInfo ExprStub   -- Generic Expression without additional Info
              | InjFInfo String     -- InjF with the name of the InjF
              | LambdaInfo String ChainName  -- Lambda with the name of the bound variable and the ChainName of the body
              | IfInfo ChainName ChainName ChainName
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

-- The forward-chaining setup shared by the invertibility certificate
-- ('isInvertibleLambda') and the inverse codegen ('toInvExpr'), so the two can
-- never disagree about which lambdas invert. For the lambda resolved from a
-- chain name it returns: the bound variable's name, the chain names of every
-- occurrence of that variable inside the body (the points we try to solve for),
-- and the ParameterHornClause declaring the observed body known. 'Nothing' when
-- the chain name does not resolve to a lambda.
inversionSetup :: FCData -> ChainName -> Maybe (String, [ChainName], HornClause)
inversionSetup fcData lambdaCN = do
  (_, info, tag) <- findEquivalentExpression fcData lambdaCN
  case info of
    -- If the lambda is applied multiple times, @tag@ uniquely identifies our
    -- application; it suffixes both the occurrences and the observed body.
    LambdaInfo toInvVarName lambdaBodyCN ->
      let toInvCNs = map (++ tag) (findChainNamesForVar fcData toInvVarName)
          -- If the function being inverted is itself a function, strip the
          -- additional lambdas; those are re-added by the caller around the
          -- whole inference function (the inverse is only a part of it).
          (unwrappedChainName, _) = unwrapLambdas fcData lambdaBodyCN
          paramClause = ParameterHornClause (unwrappedChainName ++ tag)
      in Just (toInvVarName, toInvCNs, paramClause)
    _ -> Nothing

-- | Invertibility certificate (modality stage 2): is the variable bound by the
-- lambda at this chain name algebraically recoverable from the known anchors and
-- the observed body? This is the pure verdict the modality engine consults in
-- place of weaker ad-hoc heuristics; the IR realisation that shares the very
-- same 'FCData' is 'toInvExpr'. (Finiteness/preimage of the recovered value is
-- the orthogonal DiscreteValues axis — Fin in the design — not a FC concern.)
isInvertibleLambda :: FCData -> [ADTDecl] -> ChainName -> Bool
isInvertibleLambda fcData adts lambdaCN = case inversionSetup fcData lambdaCN of
  Just (_, toInvCNs, paramClause) ->
    any (isJust . toValueExpr (hornClauses fcData) [paramClause] adts) toInvCNs
  Nothing -> False

-- Takes the chainName of a function (May be a lambda, a variable, an Apply ...) and returns the inverse function of that lambda together with the derivative of the inverse
toInvExpr :: FCData -> [ADTDecl] -> ChainName -> (IRExpr, IRExpr)
toInvExpr fcData adts lambdaCN = (mergedM, mergedCoV)
  where
    clauseSet = hornClauses fcData
    (toInvVarName, toInvCNs, paramClause) = case inversionSetup fcData lambdaCN of
      Just x  -> x
      Nothing -> error $ "toInvExpr: chain name does not resolve to an invertible lambda: " ++ lambdaCN
    -- Create the expression that calculates each occurrence; merge those that
    -- carry complementary information.
    valueExprs = mapMaybe (toValueExpr clauseSet [paramClause] adts) toInvCNs
    (mergedM, mergedCoV) = mergeExpr toInvVarName lambdaCN toInvCNs valueExprs

-- Performs forward chaining to create an expression, which calculates the value of a specific point in the AST given a set of parameter points in the AST.
-- Also returns the derivative of that expression
toValueExpr :: [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe (IRExpr, IRExpr)
toValueExpr clauses paramClauses adts startCN =
  case findConcludingHornClause solvedClauses startCN of
    Just concludingClause -> do
      -- Throw away superfluous clauses. Do this by sorting them by requirement
      -- and throwing away clauses after the clause that inferes the bound variable
      -- Also guarantees that the later generated letIns are in the correct order
      -- This may still contain some superflous clauses, but they can easily be detected by an optimizer
      let sortedClauses = topSortDAG solvedClauses
      let relevantSortedClauses = cutList sortedClauses concludingClause
      -- Calculate the symbolic derivative
      let deriv = derivativeOfPath adts relevantSortedClauses
      -- Generate code
      Just (toLetInBlock clauses adts relevantSortedClauses, wrapInLetInBlock clauses adts relevantSortedClauses deriv)
    Nothing -> Nothing
  where
    augmentedClauseSet = map (:[]) paramClauses ++ clauses
    -- Solve the set of Horn clauses for clauses which are fulfilled
    solvedClauses = solveHCSet augmentedClauseSet

-- Takes a chain name of a point in the AST and finds the lambda, this point is equivalent to.
-- Also return the uniquely identifying tag if the lambda is tagged
findEquivalentExpression :: FCData -> ChainName -> Maybe (ChainName, ExprInfo, String)
findEquivalentExpression fcData startCN = go [startCN] startCN
  where
    go visited cn = case lookup cn (chainNameInfo fcData) of
      Nothing -> error $ "Could not find chainName in FCData " ++ cn
      Just x | isFinalExpr x -> Just (cn, x, "")
      Just _ -> do
        let origClauses = getAllOriginatingEquivalenceHornClauses (hornClauses fcData) cn
        case filter (\(EquivalenceHornClause _ _ _ inv) -> inv == 1) origClauses of
          [EquivalenceHornClause [pre] _ _ _] ->
            let next = untag pre in
            if next `elem` visited
              then Nothing  -- cycle detected; no valid lambda found along this chain
              else do
                (resCN, resInfo, _) <- go (next : visited) next
                return (resCN, resInfo, getTag pre)
          _ -> Nothing
    isFinalExpr (ApplyInfo _ _) = False
    isFinalExpr (VarInfo _) = False
    isFinalExpr _ = True

findChainNamesForVar :: FCData -> String -> [ChainName]
findChainNamesForVar fcData varName = case correctVarInfos of
  [] -> error $ "Could not find variable " ++ varName ++ " in FC data"
  x -> map fst x
  where
    correctVarInfos = filter (isCorrectVarInfo varName . snd) (chainNameInfo fcData)
    isCorrectVarInfo name (VarInfo n) | name == n = True
    isCorrectVarInfo _ _ = False

-- Strip the expression of all wrapping lambdas. Return the chain name of the resulting expression and all names of the bound variables stripped away
unwrapLambdas :: FCData -> ChainName -> (ChainName, [String])
unwrapLambdas fcData cn = case lookup cn (chainNameInfo fcData) of
  Just (LambdaInfo name bodyName) ->
    let (lCN, names) = unwrapLambdas fcData bodyName in (lCN, name:names)
  Just _ -> (cn, [])

-- This takes a list of value expressions and merges then such that in tuple constructions a existing value overwrites an ANY.
-- If two paths provide information for the same part of the tuple, we discard the second, because the should be semantically equal and therefor redundant
-- We also assume that the different paths do not have conflicting LetIns
-- The covariance factors are multiplied only in the two disjoint-tuple-slot
-- merges below (each path fills one component, the other ANY). Disjoint
-- components are independent coordinates, so the Jacobian is block-diagonal and
-- its determinant IS that product — the correct Gramian for this shape. Any other
-- merge takes the first path's covariance (semantically-equal values, one
-- Jacobian), never a product. Proven sound by investigation
-- forward-chaining-math-correctness.
-- The first three arguments are purely diagnostic context for the failure case below:
-- the name of the variable being witnessed, the chain name of the lambda being inverted,
-- and the candidate occurrences (chain names) that were attempted and yielded no path.
mergeExpr :: String -> ChainName -> [ChainName] -> [(IRExpr, IRExpr)] -> (IRExpr, IRExpr)
mergeExpr varName lambdaCN candidateCNs [] = error $ unlines
  [ "Forward chaining failed to find a solution: no inversion path could be constructed for variable \"" ++ varName ++ "\""
  , "while inverting the function bound at chain name " ++ lambdaCN ++ "."
  , "Candidate occurrences that were tried and could not be witnessed: " ++ show candidateCNs
  , "This usually means the function is not algebraically invertible in this variable (e.g. it is"
  , "many-to-one, like a count/sum of conditional contributions) and the program shape did not"
  , "qualify for enumeration-based inference instead (the IsConditional + toIREnumerate path in the"
  , "IRCompiler). See docs/forward-chaining-recursion-constraint.md for the failure analysis."
  ]
mergeExpr _ _ _ [x] = x
mergeExpr varName lambdaCN candidateCNs (x:xs) = mergeExpr2 id x (mergeExpr varName lambdaCN candidateCNs xs)

mergeExpr2 :: (IRExpr -> IRExpr) -> (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> (IRExpr, IRExpr)
mergeExpr2 bindings (IRLetIn n v body, cov1) expr2 = mergeExpr2 (bindings . IRLetIn n v) (body, cov1) expr2
mergeExpr2 bindings expr1 (IRLetIn n v body, cov2) = mergeExpr2 (bindings . IRLetIn n v) expr1 (body, cov2)
mergeExpr2 bindings (IRTCons (IRConst VAny) b, cov1) (IRTCons a (IRConst VAny), cov2) = (bindings $ IRTCons a b, IROp OpMult cov1 cov2)
mergeExpr2 bindings (IRTCons a (IRConst VAny), cov1) (IRTCons (IRConst VAny) b, cov2)  = (bindings $ IRTCons a b, IROp OpMult cov1 cov2)
-- Expressions are not compatible. Assume they are semantically equal. Then just take the first
-- TODO: Maybe one of the two is compatible with a third expression, then we would want to take this one
mergeExpr2 bindings (expr1, cov1) _ = (bindings expr1, cov1)

getAllOriginatingEquivalenceHornClauses :: [[HornClause]] -> ChainName -> [HornClause]
getAllOriginatingEquivalenceHornClauses clauses cn = concatMap (filter (\hc -> isEquivalenceHornClause hc && conclusion hc == cn)) clauses

-- Takes a list of Horn clauses and converts them to nested letIn expressions.
-- We do this by declaring a new variable named after the conclusion of the clause
-- The value of this letIn depends on the type of Horn clause, but is in general either the forward path or an inversion of the expression used to create the clause
toLetInBlock :: [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
toLetInBlock _ _ [] = error "Cannot convert empty clause set to LetIn block"
toLetInBlock clauses adts cs = wrapInLetInBlock clauses adts (init cs) (hornClauseToIRExpr clauses adts (last cs))

wrapInLetInBlock :: [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr -> IRExpr
wrapInLetInBlock clauses adts (ParameterHornClause _:cs) inner = wrapInLetInBlock clauses adts cs inner
wrapInLetInBlock clauses adts (c:cs) inner = IRLetIn (conclusion c) (hornClauseToIRExpr clauses adts c) (wrapInLetInBlock clauses adts cs inner)
wrapInLetInBlock _ _ [] inner = inner

-- Generates IRExpr from Horn clauses
hornClauseToIRExpr :: [[HornClause]] -> [ADTDecl] -> HornClause -> IRExpr
hornClauseToIRExpr _ adts clause =
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
    ParameterHornClause conc -> IRVar conc
    EquivalenceHornClause [p] _ _ _ -> IRVar p
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

-- Finds the first horn clause in a list that has a given conclusion
findConcludingHornClause :: [HornClause] -> ChainName -> Maybe HornClause
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> Nothing
    res -> Just $ head res

-- An FC inversion path is a linear chain of single-input invertible steps, and
-- the witnessed variable flows through it exactly once (a step with two
-- un-witnessed random inputs has no inversion clause and never enters a path).
-- So this product of per-step inverse derivatives IS the chain rule
-- d/dx g(h(x)) = g'(h(x))·h'(x), i.e. the full path Jacobian — proven sound under
-- that structural constraint by investigation forward-chaining-math-correctness.
derivativeOfPath :: [ADTDecl] -> [HornClause] -> IRExpr
derivativeOfPath adts clauses = foldr1 (IROp OpMult) derivs
  where derivs = map (derivativeOfHornClause adts) clauses

derivativeOfHornClause :: [ADTDecl] -> HornClause -> IRExpr
derivativeOfHornClause adts (ExprHornClause pre _ (InjFInfo name) inv) | inv > 0 = do
  let FPair injFFwdDecl injFInvDecls = fromJust $ lookup name (globalFEnv adts)
  let correctDecl = injFInvDecls !! (inv - 1)
  -- The premises of the of the HornClause are the input of the inverse InjF
  let FDecl {derivatives=invDerivs} = foldr (\(old, new) decl -> renameDecl old new decl) correctDecl (zip (inputVars correctDecl) pre)
  -- We need to find out which variable is the output of the forward InjF. For this take the fwd InjF and do the same renaming as for the inverse
  let FDecl {outputVars=[invVar]} = foldr (\(old, new) decl -> renameDecl old new decl) injFFwdDecl (zip (inputVars correctDecl) pre)
  fromJust $ lookup invVar invDerivs
derivativeOfHornClause _ _ = IRConst (VFloat 1.0)

-- | Build the forward-chaining certificate for a whole program. The 'Set'
-- argument is the determinism field's known-anchor set (chain names whose value
-- is known without observing the sample); it seeds extra self-sufficient anchors
-- beyond the structural @Constant@-only approximation (modality-determinism-pass,
-- consumed here per modality-split-forwardchaining).
progToFCData :: Set ChainName -> Program -> FCData
progToFCData anchors prog =
  FCData { hornClauses = anchorClauses ++ baseClauses
         , chainNameInfo = cnInfo
         , fcAnchors = anchorInstances }
  where
    cnInfo = progToChainNameInfo prog
    baseClauses = progToHornClauses prog cnInfo
    -- Each known anchor is a self-sufficient (empty-premise) starting point for
    -- forward chaining, mirroring how @Constant@ already self-derives. This
    -- replaces FC's structural @Constant@-only under-approximation with the real
    -- determinism field, so ThetaI/Subtree/derived-deterministic operands become
    -- invertible-through.
    --
    -- Anchors are computed on the untagged program, but FC tags chain names per
    -- function invocation (e.g. @ast5_t0@) when it duplicates a helper-function
    -- body. So we anchor every chain name in the clause graph whose /untagged/
    -- form is a known anchor — otherwise a @theta@ inside an inverted helper
    -- (the @inner z = z + theta_0@ shape) would never match. The corresponding
    -- values are materialised in codegen (IRCompiler) for non-constant anchors.
    anchorInstances = Set.fromList
      [ cn | cn <- allClauseChainNames baseClauses, Set.member (untag cn) anchors ]
    anchorClauses = [ [ParameterHornClause cn] | cn <- Set.toList anchorInstances ]

-- Every chain name appearing as a premise or conclusion anywhere in a clause set.
allClauseChainNames :: [[HornClause]] -> [ChainName]
allClauseChainNames = nub . concatMap (concatMap (\c -> conclusion c : premises c))


progToChainNameInfo :: Program -> [(ChainName, ExprInfo)]
progToChainNameInfo Program{functions=fs} = concatMap (exprToChainNameInfo . snd) fs

exprToChainNameInfo :: Expr -> [(ChainName, ExprInfo)]
exprToChainNameInfo (Lambda TypeInfo{chainName=cn} n b) = (cn, LambdaInfo n (getChainName b)):exprToChainNameInfo b
exprToChainNameInfo (Constant TypeInfo{chainName=cn} v) = [(cn, ConstantInfo v)]
exprToChainNameInfo (Var TypeInfo{chainName=cn} n) = [(cn, VarInfo n)]
exprToChainNameInfo (Apply TypeInfo{chainName=cn} l v) = (cn, ApplyInfo (getChainName l) (getChainName v)):exprToChainNameInfo l ++ exprToChainNameInfo v
exprToChainNameInfo (IfThenElse TypeInfo{chainName=cn} c t e) = (cn, IfInfo (getChainName c) (getChainName t) (getChainName e)): exprToChainNameInfo c ++ exprToChainNameInfo t ++ exprToChainNameInfo e
exprToChainNameInfo e = (getChainName e, StubInfo (toStub e)):concatMap exprToChainNameInfo (getSubExprs e)

-- Convert a Program to a set of groups of Horn clauses
progToHornClauses :: Program -> [(ChainName, ExprInfo)] -> [[HornClause]]
progToHornClauses Program{functions=fs, adts=adts} _ = nub $ initialRun ++ topEquivClauses ++ equivClauses
  where
    -- We need two runs for this: first run is every expression converted into a group of Horn clauses
    initialRun = concatMap (exprToHornClauses adts . snd) fs
    topEquivClauses = constructTopLevelEquivalenceClauses initialRun fs
    equivClauses = lambdasToHornClauses (initialRun ++ topEquivClauses) fs

-- Converts an expression with all its subexpressions into Horn clauses
exprToHornClauses :: [ADTDecl] -> Expr -> [[HornClause]]
exprToHornClauses adts e = case e of
  Constant _ v -> [[ExprHornClause [] (getChainName e) (ConstantInfo v) 0]]
  -- Field constructors (Cons/TCons/user-ADT constructors) emit only their
  -- inverse clauses, each in its own group because the fields can be solved
  -- independently. The forward clause is omitted deliberately: constructing the
  -- container from its fields could create cycles in the chaining graph. This is
  -- safe (not merely defensive): container construction inference is handled
  -- out-of-band by IRCompiler's field-constructor path, so no program needs the
  -- forward clause (investigation forward-chaining-math-correctness, Q3).
  InjF _ (Named name) params
    | isFieldConstructor adts name ->
        map (: []) (tail (injFtoHornClause adts e)) ++ concatMap (exprToHornClauses adts) params
  InjF _ _ params -> injFtoHornClause adts e: concatMap (exprToHornClauses adts) params
  -- Some expressions are not invertable and therefor do not produce Horn clauses
  _ -> concatMap (exprToHornClauses adts) (getSubExprs e)

-- Converts an instance of a InjF into a Horn clause with corresponding variables in the premises and conclusion
injFtoHornClause :: [ADTDecl] -> Expr -> [HornClause]
injFtoHornClause adts e = case e of
  -- Forward Horn clause: Inverse Horn clauses with corresponding inversion number
  InjF _ (Named name) _ -> (constructInjFHornClause subst eCN name eFwd 0): zipWith (constructInjFHornClause subst eCN name) eInv [1..]
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
constructInjFHornClause subst _ name decl inv = ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv
  where
    FDecl {inputVars = inV, outputVars = [outV]} = decl
    lookupSubst v = fromJust (lookup v subst)

-- Find the chainName this a given chain name is equivalent to
-- TODO: Can multiple equivalences happen? What then?
getEquivCN :: [[HornClause]] -> ChainName -> ChainName
getEquivCN clauses cn = case (filter (\(EquivalenceHornClause [pre] _ _ _) -> pre == cn)) equiv of
  [EquivalenceHornClause _ back _ _] -> back
  [] -> error $ "Found no equivalent chain name to: " ++ cn
  _ ->  error $ "Found multiple equivalent chain name to: " ++ cn
  where
    equiv = filter isEquivalenceHornClause (map head clauses)

-- Applies create two different types of quivalences in a program.
-- 1. Bound variables are equivalent to the value of their binding apply
-- 2. An Apply is equivalent to the body of the lambda it applies
-- This function creates HornCLauses for these equivalences
lambdasToHornClauses :: [[HornClause]] -> [FnDecl] -> [[HornClause]]
lambdasToHornClauses clauses fns = fixpoint fExprs clauses
  where
    fExprs = map snd fns
    fixpoint exprs cs = let extension = concatMap (constructEquivalenceClauses cs fExprs) exprs in if null extension then cs else fixpoint exprs (extension ++ cs)

-- Top level functions act like an apply binding their body to their name
constructTopLevelEquivalenceClauses :: [[HornClause]] -> [FnDecl] -> [[HornClause]]
constructTopLevelEquivalenceClauses clauses decls = concatMap (constructTopLevelEquivalenceClauses' clauses (map snd decls)) decls

constructTopLevelEquivalenceClauses' :: [[HornClause]] -> [Expr] -> FnDecl -> [[HornClause]]
constructTopLevelEquivalenceClauses' clauses exprs (name, expr) = case rType (getTypeInfo expr) of
  TArrow _ _ -> concat $ evalSupply $ mapM (\otherExpr -> do
    let Lambda _ _ body = expr
    let dependent = getDependentGroups clauses (getChainName body)
    (varClauses, applyCnt) <- associateFunctionVariable name (getChainName expr) "" otherExpr
    let taggedDependents = concatMap (\tag -> map (tagGroup tag) dependent) [0..applyCnt - 1]
    return $ varClauses ++ taggedDependents) exprs
  _ -> concatMap (associateVariable name (getChainName expr) "") exprs

-- Construct horn clauses for equivalences induced by Applies. See lambdasToHornClauses for more info
constructEquivalenceClauses :: [[HornClause]] -> [Expr] -> Expr -> [[HornClause]]
constructEquivalenceClauses clauses exprs (Apply TypeInfo{chainName=exCn} l v) | not (isInClauseSet clauses exCn) && (isLambda l || isInClauseSet clauses (getChainName l)) = do
    -- Find the declaration of the lambda on the left side of the Apply. Trivial if the lambda is directly there, else follow equivalences
    let (_, lTag, lVar, lBody) = case l of
          Lambda TypeInfo{chainName=lCn'} n body -> (lCn', "", n, body)
          _ ->
            let appliedLambdaCn = getEquivCN clauses (getChainName l)
                appliedLambdaTag = getTag appliedLambdaCn
                Lambda _ name body = findExprWithCN exprs (untag appliedLambdaCn) in
                  (appliedLambdaCn, appliedLambdaTag, name, body)
    let lBodyCn = getChainName lBody ++ lTag
    -- The Apply is equivalent to the body of the lambda it is applying
    let appliedGroup = createEquivHornClauseGroup AppliedEquivalence exCn lBodyCn
    -- The Var expressions are equivalent to the value bound to them
    -- The following depends on whether the applied value is a function or a plain value
    case rType (getTypeInfo v) of
      -- If it is a function we have the problems if the function is invoked multiple times, because different invokations may have differrnt return values.
      -- This is not possible, because we identify values by their chainName, which is the same for different invokations
      -- Solve this by duplicating the sub-AST of the function and tagging each chainName with a tag unique for each invokation
      TArrow _ _ -> do
        -- Fing the lambda bound
        let vLambdaCn = case v of
              (Lambda TypeInfo{chainName = vlCn} _ _) -> vlCn
              _ -> getEquivCN clauses (getChainName v)
        let Lambda _ _ vBody = findExprWithCN exprs vLambdaCn
        -- Get all horn clauses, which corresspond to expressions in the sub-AST of the lambda
        let dependent = getDependentGroups clauses (getChainName vBody)
        -- Supply each invokation with a unique tag and create the corresponding clauses
        let (varClauses, applyCnt) = evalSupply $ associateFunctionVariable lVar vLambdaCn lTag lBody
        -- Create a tagged copy of the dependent Hron clauses
        let taggedDependents = concatMap (\tag -> map (tagGroup tag) dependent) [0..applyCnt - 1]
        appliedGroup:varClauses ++ taggedDependents
      -- Easy if the applied value is no function, because it is constant across the program.
      _ -> 
        -- We still need to create a tagged group if our original lambda was tagged
        let taggedGroups = if null lTag then [] else map (map (tagHornClause lTag)) (getDependentGroups clauses (getChainName lBody)) in
        appliedGroup:taggedGroups ++ associateVariable lVar (getChainName v) lTag lBody
  where
    isLambda (Lambda {}) = True
    isLambda _ = False
constructEquivalenceClauses clauses exprs ex = concatMap (constructEquivalenceClauses clauses exprs) (getSubExprs ex)


isInClauseSet :: [[HornClause]] -> ChainName -> Bool
isInClauseSet clauses cn = any (\cs -> isEquivalenceHornClause (head cs) && premises (getForwardClauseOfGroup cs) == [cn]) clauses

-- Creates Horn clauses implying an equivalence between a given chainName and all occurances of a given variable in an expression
associateVariable :: String -> ChainName -> String -> Expr -> [[HornClause]]
associateVariable varName chainTo tag (Var TypeInfo{chainName=cn} n) | n == varName = [createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) chainTo]
associateVariable varName chainTo tag ex = concatMap (associateVariable varName chainTo tag) (getSubExprs ex)

-- Creates Horn clauses implying an equivalence between a given chainName and all occurances of a given variable in an expression
-- Gives each variable a unique tag. The number of tags created is returned
associateFunctionVariable :: String -> ChainName -> String -> Expr -> Supply ([[HornClause]], Int)
associateFunctionVariable varName chainTo tag (Var TypeInfo{chainName=cn} n) | n == varName = demandUniqueNumber <&> \num -> ([createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) (chainTo ++ tagPrefix ++ show num)], 1)
associateFunctionVariable varName _ _ (Lambda _ n _) | n == varName = return ([], 0)  -- Variable is shadowed. Don't search in this branch
associateFunctionVariable varName chainTo tag ex = do
  a <- mapM (associateFunctionVariable varName chainTo tag) (getSubExprs ex)
  return (concatMap fst a, sum (map snd a))

-- Creates a Horn clause group implying equivalence between two chain names
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

-- A tag is a suffix to a chain name. It consists of this prefix with a number appended
tagPrefix :: String
tagPrefix = "_t"

-- Remove a tag from a chain name
untag :: ChainName -> ChainName
untag = fst . splitByString tagPrefix

getTag :: ChainName -> String
getTag = snd . splitByString tagPrefix

tagGroup :: Int -> [HornClause] -> [HornClause]
tagGroup tagNum group = do
  let tag = tagPrefix ++ show tagNum
  map (tagHornClause tag) group

-- Tag all clauses in a group
tagHornClause :: String -> HornClause -> HornClause
tagHornClause tag (ExprHornClause pre conc info inv) = ExprHornClause (map (++ tag) pre) (conc ++ tag) info inv
tagHornClause tag (EquivalenceHornClause pre conc info inv) = EquivalenceHornClause (map (++ tag) pre) (conc ++ tag) info inv


getDependentGroups :: [[HornClause]] -> ChainName -> [[HornClause]]
getDependentGroups clauses cn = directDependence cn ++ concatMap (getDependentGroups clauses) (concatMap forwardPremises (directDependence cn))
  where
    -- Variable equivalences work the other way around as other clauses
    --forwardConclusion cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc && isVariableEquivalence (equivalenceType fc) then head $ premises fc else conclusion fc
    forwardConclusion = conclusion . getForwardClauseOfGroup
    -- We want to include the equivalence clauses in the dependent clauses, but don't want to follow their jumps
    forwardPremises cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc then [] else premises fc
    --forwardPremises = premises . getForwardClauseOfGroup
    directDependence c = filter (\cs -> hasForwardClause cs && forwardConclusion cs == c) clauses
    hasForwardClause = any ((== 0) . inversion)

-- Some clause groups, like TCons, may not have a forward clause. You need to make sure this is not the case when incokink this function
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
  where
    annotFs = evalSupply (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)


-- Annotate an expression and all of its subexpressions
annotateExpr :: Expr -> Supply Expr
annotateExpr = tMapM (\ex -> demandUniqueNumber <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex))

-- Returns all recursively fulfilled clauses, in reverse discovery order (most
-- recently fulfilled first), matching the legacy accumulation order downstream
-- code (findConcludingHornClause / topSortDAG) relies on.
--
-- Each clause group contributes at most one fulfilled clause (the first whose
-- premises are all already known). We track used groups by index and known
-- conclusions in 'Set's, so membership tests are logarithmic rather than the
-- linear list 'delete'/'elem' scans this used to do (cleanup-forward-chaining).
solveHCSet :: [[HornClause]] -> [HornClause]
solveHCSet hcs = go Set.empty Set.empty []
  where
    groups = zip [0 :: Int ..] hcs
    go usedGroups detVars fulfilled =
      case [ (i, c) | (i, g) <- groups
                    , not (i `Set.member` usedGroups)
                    , c <- g
                    , all (`Set.member` detVars) (premises c) ] of
        [] -> fulfilled
        ((i, c):_) -> go (Set.insert i usedGroups) (Set.insert (conclusion c) detVars) (c : fulfilled)

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


-- Pretty printing / Debugging functions for horn clause sets
showClause :: HornClause -> [Char]
showClause (ExprHornClause pre conc info inv) = show pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Expression) " ++ show info
showClause (EquivalenceHornClause [pre] conc info inv) = pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Equivalence) " ++ show info
showClause (ParameterHornClause param) = "Parameter " ++ param

showClauseGroup :: [HornClause] -> String
showClauseGroup cs = intercalate "\n" (map showClause cs)

showClauseGroups :: [[HornClause]] -> String
showClauseGroups groups = intercalate "\n\n" (map showClauseGroup groups)

