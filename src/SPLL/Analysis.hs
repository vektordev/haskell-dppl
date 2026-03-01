module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  annotateAlgsProg,
  annotateConditionalProg
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.InferenceRule
import Data.Maybe (maybeToList, fromJust, isNothing, fromMaybe, isJust, listToMaybe)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (TypeInfo, TypeInfo(..), Tag(..), setTags)
import Data.Set (fromList, toList)
import Data.Set.Internal (merge, empty)
import Debug.Trace (trace)
import PredefinedFunctions
import Utils
import SPLL.Typing.ForwardChaining (FCData, ExprInfo (LambdaInfo), findEquivalentExpression, findExprWithCN, progToFCData)


annotateEnumsProg :: Program -> Program
annotateEnumsProg p@Program {functions=f, neurals=n, adts=adts} = p{functions = finalExprEnv}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    finalExprEnv = fixpoint iterateExprEnv []
    iterateExprEnv eEnv = map (second (annotate adts (neuralEnv ++ map (second $ tags . getTypeInfo) eEnv))) f
    neuralEnv = [(name, [DiscreteValues mv]) | (name, _, Just mv) <- n]
    isMultiDiscrete (MultiDiscretes _) = True
    isMultiDiscrete _ = False

annotateIfNotRecursive :: [ADTDecl] -> String -> [(String, [Tag])] -> Expr -> Expr
annotateIfNotRecursive _ name _ e | isRecursive name e = e
annotateIfNotRecursive adts _ env e = annotate adts env e

annotate :: [ADTDecl] -> [(String, [Tag])] -> Expr -> Expr
--annotate _ e | trace ((show e)) False = undefined
annotate adts env e = withNewTypeInfo
  where
    oldTags = tags $ getTypeInfo e
    newTags = case ([mv | DiscreteValues mv <- oldTags]) of
      [] -> case valuesTag of
        Just t -> t:oldTags
        Nothing -> oldTags
      _:_ -> oldTags
    valuesTag = fmap DiscreteValues values
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) newTags)
    withNewSubExpr = case e of
      Apply _ l@(Lambda _ n b) v -> do
        let annotatedV = annotate adts env v
            newEnv = (n, tags (getTypeInfo annotatedV)):env
            annotatedL = annotate adts env l in
              setSubExprs e [annotatedL, annotatedV]
      _ -> setSubExprs e (map (annotate adts env) (getSubExprs e))
    values = case withNewSubExpr of
      (Constant _ a) -> Just $ MultiDiscretes [a]
      (ReadNN _ name _) -> case lookup name env of
        Just tgs -> Just $ head [mv | DiscreteValues mv <- tgs]
        _ -> Nothing
      (InjF _ name params) -> do
        paramValues <- mapM getValuesFromExpr params
        let unpackedMultiVals = map multiValueToValueList paramValues
        return $ valueListToMultiValue $ propagateValues adts name unpackedMultiVals
      (IfThenElse _ _ left right) -> do
        valuesLeft <- getValuesFromExpr left
        valuesRight <- getValuesFromExpr right
        return $ unionMultiValues valuesLeft valuesRight
      (LetIn _ _ _ a) -> getValuesFromExpr a
      (Var _ name) -> do
        tags <- lookup name env
        listToMaybe [mv | DiscreteValues mv <- tags]
      _ -> Nothing


getValuesFromExpr :: Expr -> Maybe MultiValue
getValuesFromExpr e = case [mv | DiscreteValues mv <- tags $ getTypeInfo e] of
  [mv] -> Just mv
  [] -> Nothing

isRecursive :: String -> Expr -> Bool
isRecursive name (Var _ n) | name == n = True
isRecursive n e = any (isRecursive n) (getSubExprs e)

annotateAlgsProg :: Program -> Program
annotateAlgsProg p@Program {functions=fs} = p{functions=map (Data.Bifunctor.second (tMap tagAlgsExpression)) fs}

tagAlgsExpression :: Expr -> TypeInfo
tagAlgsExpression (InjF ti _ [_]) = ti
tagAlgsExpression expr =
  if likelihoodFunctionUsesTypeInfo (toStub expr) then
    setTags (getTypeInfo expr) (Alg (findAlgorithm expr):tags (getTypeInfo expr))
  else
    getTypeInfo expr

findAlgorithm :: Expr -> InferenceRule
findAlgorithm expr = case validAlgs of
  [alg] -> alg
  [] -> error ("no valid algorithms found in expr: " ++ show expr)
  --(_:_:_) -> error "multiple valid algorithms found" -- TODO: There might be leeway here.
  alg:_ -> alg  --If multiple choose the first one TODO: Check if correct
  where
    validAlgs = filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr
    correctExpr = filter (checkExprMatches expr) allAlgorithms

checkConstraint :: Expr -> InferenceRule -> RuleConstraint -> Bool
checkConstraint expr _ (SubExprNIsType n ptype) | length (getSubExprs expr) > n = ptype == p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr _ (SubExprNIsNotType n ptype) | length (getSubExprs expr) > n = ptype /= p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr alg ResultingTypeMatch = resPType == annotatedType
  where
    annotatedType = pType $ getTypeInfo expr
    resPType = resultingPType alg (map (pType . getTypeInfo) (getSubExprs expr))
checkConstraint expr _ (SubExprNIsEnumerable n) | length (getSubExprs expr) > n =
  isEnumerable (tags (getTypeInfo (getSubExprs expr !! n)))
checkConstraint _ _ _ = False

isEnumerable :: [Tag] -> Bool
isEnumerable =
  any (\t -> case t of
    DiscreteValues _ -> True
    _ -> False)

annotateConditionalProg :: Program -> Program
annotateConditionalProg p@Program {functions=fs} = p{functions=map (Data.Bifunctor.second (tMap (tagConditional (progToFCData p) p))) fs}

tagConditional :: FCData -> Program -> Expr -> TypeInfo
tagConditional fcData p (Lambda ti _ b) = if isConditional fcData p [] b then ti{tags=IsConditional:tags ti} else ti
tagConditional fcData p e@(Var ti b) = if isConditional fcData p [] e then ti{tags=IsConditional:tags ti} else ti
tagConditional fcData p x = getTypeInfo x

isConditional :: FCData -> Program -> [ChainName] -> Expr -> Bool
isConditional _ _ visited e | chainName (getTypeInfo e) `elem` visited = False
isConditional _ _ _ (IfThenElse _ _ _ _) = True
isConditional _ _ _ (Lambda _ _ _) = False
isConditional _ _ _ (Apply _ _ _) = False
isConditional fcData p visited (Var (TypeInfo{chainName=cn}) n) = case findEquivalentExpression fcData cn of
  Just (_, LambdaInfo _ bodyCn, _) -> isConditional fcData p (cn:visited) (findExprWithCN (map snd (functions p)) bodyCn)
  _ -> False
isConditional fcData p visited x = any (isConditional fcData p visited) (getSubExprs x)

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubEquals, StubGreaterThan, StubLessThan, StubInjF]
--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.