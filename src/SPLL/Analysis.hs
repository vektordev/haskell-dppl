module SPLL.Analysis (
  annotate,
  annotateProg
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.InferenceRule
import SPLL.Typing.RType
import SPLL.Typing.PType
import Data.Maybe (maybeToList, fromJust, isNothing, fromMaybe)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (TypeInfo, TypeInfo(..), Tag(..), setTags)
import Data.Set (fromList, toList)
import Data.Set.Internal (merge, empty)


annotateProg :: Program -> Program
annotateProg p@Program {functions=f} = p{functions = map (second (annotate env)) f}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where env = map (second (tags . getTypeInfo . annotate [])) f 

annotate :: [(String, [Tag])] -> Expr -> Expr
annotate env e = withNewTypeInfo
  where 
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) tgs)
    newEnv = case withNewSubExpr of 
      (LetIn _ n v _) -> (n, tags $ getTypeInfo v):env
      _ -> env
    withNewSubExpr = setSubExprs e (map (annotate newEnv) (getSubExprs e))
    tgs = EnumList (toList values):algs
    algs = [Alg $ findAlgorithm e | likelihoodFunctionUsesTypeInfo $ toStub e]
    values = case withNewSubExpr of
      (Constant _ a@(VInt _)) -> fromList [a]
      (ReadNN _ name _) -> case lookup name env of
        (Just [EnumList l]) -> fromList l
        (Just [EnumRange (VInt a, VInt b)]) -> fromList [VInt i | i <- [a..b]]
        _ -> error $ "Invalid Neural declaration for " ++ name
      (PlusI _ left right) -> do
        let valuesLeft = getValuesFromExpr left
        let valuesRight = getValuesFromExpr right
        fromList [VInt (a + b) | VInt a <- valuesLeft, VInt b <- valuesRight]
      (MultI _ left right) -> do
        let valuesLeft = getValuesFromExpr left
        let valuesRight = getValuesFromExpr right
        fromList [VInt (a * b) | VInt a <- valuesLeft, VInt b <- valuesRight]
      (IfThenElse _ _ left right) -> do
        let valuesLeft = fromList $ getValuesFromExpr left
        let valuesRight = fromList $ getValuesFromExpr right
        merge valuesLeft  valuesRight
      (LetIn _ _ _ a) -> fromList $ getValuesFromExpr a
      (Call _ name) -> case (lookup name env) of
        Just tags -> fromList $ concatMap valuesOfTag tags 
        Nothing -> empty
      _ -> empty
    

getValuesFromExpr :: Expr ->  [Value]
getValuesFromExpr e = concatMap valuesOfTag (tags $ getTypeInfo e)
      
valuesOfTag :: Tag -> [Value]
valuesOfTag tag = case tag of
  EnumList l -> l
  EnumRange (VInt a, VInt b) -> [VInt i | i <- [a..b]]
  _ -> []

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
checkConstraint expr _ (SubExprNIsType n ptype) = ptype == p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr _ (SubExprNIsNotType n ptype) = ptype /= p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr alg ResultingTypeMatch = resPType == annotatedType
  where
    annotatedType = pType $ getTypeInfo expr
    resPType = resultingPType alg (map (pType . getTypeInfo) (getSubExprs expr))

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubGreaterThan, StubLessThan, StubMultF, StubMultI, StubPlusF, StubPlusI, StubInjF]
--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.