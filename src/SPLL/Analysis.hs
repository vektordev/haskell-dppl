module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  annotateAlgsProg
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.InferenceRule
import Data.Maybe (maybeToList, fromJust, isNothing, fromMaybe, isJust)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (TypeInfo, TypeInfo(..), Tag(..), setTags)
import Data.Set (fromList, toList)
import Data.Set.Internal (merge, empty)
import Debug.Trace (trace)
import PredefinedFunctions


annotateEnumsProg :: Program -> Program
annotateEnumsProg p@Program {functions=f, neurals=n} = p{functions = map (\(name, expr) -> (name, annotateIfNotRecursive name (exprEnv++neuralEnv) expr)) f}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    exprEnv = map (second (tags . getTypeInfo . annotate [])) f
    neuralEnv = map (\(n, _, Just t) -> (n, [t])) (filter (\(_, _, mTag) -> isJust mTag) n)

annotateIfNotRecursive :: String -> [(String, [Tag])] -> Expr -> Expr
annotateIfNotRecursive name _ e | isRecursive name e = e
annotateIfNotRecursive _ env e = annotate env e
annotate :: [(String, [Tag])] -> Expr -> Expr
--annotate _ e | trace ((show e)) False = undefined
annotate env e = withNewTypeInfo
  where
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) tgs)
    newEnv = case withNewSubExpr of
      (LetIn _ n v _) -> (n, tags $ getTypeInfo v):env
      _ -> env
    withNewSubExpr = setSubExprs e (map (annotate newEnv) (getSubExprs e))
    tgs = if null values then [] else [EnumList values]
    values = case withNewSubExpr of
      (Constant _ a@(VInt _)) -> [a]
      (ReadNN _ name _) -> case lookup name env of
        (Just [EnumList l]) -> l
        (Just [EnumRange (VInt a, VInt b)]) -> [VInt i | i <- [a..b]]
        _ -> error $ "Invalid Neural declaration for " ++ name ++ ".\n    found:" ++ show env
      (InjF _ name params) -> do
        let paramValues = map getValuesFromExpr params
        propagateValues name paramValues
      (IfThenElse _ _ left right) -> do
        let valuesLeft = getValuesFromExpr left
        let valuesRight = getValuesFromExpr right
        nub (valuesLeft ++ valuesRight)
      (LetIn _ _ _ a) -> getValuesFromExpr a
      (Var _ name) -> case (lookup name env) of
        Just tags -> concatMap valuesOfTag tags
        Nothing -> []
      _ -> []


getValuesFromExpr :: Expr ->  [Value]
getValuesFromExpr e = concatMap valuesOfTag (tags $ getTypeInfo e)

valuesOfTag :: Tag -> [Value]
valuesOfTag tag = case tag of
  EnumList l -> l
  EnumRange (VInt a, VInt b) -> [VInt i | i <- [a..b]]
  _ -> []

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
    EnumList _ -> True
    EnumRange _ -> True
    _ -> False)

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubGreaterThan, StubLessThan, StubInjF]
--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.