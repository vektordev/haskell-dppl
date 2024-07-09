module SPLL.Transpiler where

import SPLL.Lang
import SPLL.Typing.PType
import Data.Graph
import SPLL.Typing.Typing
import SPLL.InferenceRule

data Annotation a = IIndex Int
                | IIdentifier String
                | IValue (Value a)
                deriving (Show)

data IRNode a = Simple ExprStub [Annotation a]
              | Complex InferenceRule
              deriving (Show)

type IRDefinition a = (String, Tree (IRNode a))

transpile :: Env (TypeInfo a) a -> [IRDefinition a]
transpile = map transpileDefinition

transpileDefinition :: (String, Expr (TypeInfo a) a) -> IRDefinition a
transpileDefinition (name, expression) = (name, transpileExpr expression)

-- OK, static analysis is amazing and just converted this lambda
-- (\alg -> and (map (\constr -> checkConstraint expr constr) (constraints alg) ) )
-- via this
-- (\alg -> all (checkConstraint expr) (constraints alg) )
-- into this
-- (all (checkConstraint expr) . constraints )

transpileExpr :: Expr (TypeInfo a) a -> Tree (IRNode a)
transpileExpr expr = if likelihoodFunctionUsesTypeInfo $ toStub expr
  then case filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr of
    [alg] -> Node (Complex alg) (map transpileExpr $ getSubExprs expr)
    [] -> error ("no algorithm found in transpiler in Expression " ++ (show $ toStub expr))
    algs -> error ("ambiguous algorithms in transpiler: " ++ show (map algName algs))
  else Node (Simple (toStub expr) (annotate expr)) (map transpileExpr $ getSubExprs expr)
  where
      correctExpr = filter (checkExprMatches expr) allAlgorithms

annotate :: Expr (TypeInfo a) a -> [Annotation a]
annotate expr = case expr of 
  ThetaI _ i    -> [IIndex i]
  Constant _ x  -> [IValue x]
  Call _ x      -> [IIdentifier x]
  LetIn _ x _ _ -> [IIdentifier x]
  Arg _ x _ _   -> [IIdentifier x]
  CallArg _ x _ -> [IIdentifier x]
  Lambda _ x _  -> [IIdentifier x]
  _             -> []


checkConstraint :: Expr (TypeInfo a) a -> InferenceRule -> RuleConstraint -> Bool
checkConstraint expr _ (SubExprNIsType n ptype) = ptype == p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr _ (SubExprNIsNotType n ptype) = ptype /= p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr alg ResultingTypeMatch = resPType == annotatedType
  where
    annotatedType = pType $ getTypeInfo expr
    resPType = resultingPType alg (map (pType . getTypeInfo) (getSubExprs expr))

arity :: ExprStub -> Int
arity = undefined

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubGreaterThan, StubMultF, StubMultI, StubPlusF, StubPlusI]
  
