module Transpiler where

import SPLL.Lang
import SPLL.Typing.PType
import Data.Graph
import SPLL.Typing.Typing

data ExprStub = StubIfThenElse
              | StubGreaterThan
              | StubThetaI
              | StubUniform
              | StubNormal
              | StubConstant
              | StubMult
              | StubPlus
              | StubNull
              | StubCons
              | StubCall
              | StubVar
              | StubLetIn
              | StubArg
              | StubCallArg
              | StubLambda
              | StubReadNN
              deriving (Show, Eq)

data Constraint = SubExprNIsType Int PType
                | SubExprNIsNotType Int PType
                | ResultingTypeMatch
                deriving Show

data Annotation a = IIndex Int
                | IIdentifier String
                | IValue (Value a)
                deriving (Show)

data IRNode a = Simple ExprStub [Annotation a]
              | Complex Algorithm
              deriving (Show)

type IRDefinition a = (String, Tree (IRNode a))
-- can we encode symmetries?
data Algorithm = Algorithm { forExpression :: ExprStub
                           , constraints :: [Constraint]
                           , algName :: String
                           --apply all subexpr PTypes to find PType
                           , resultingType :: [PType] -> PType
                           }

instance Show Algorithm where
  show (Algorithm _ _ name _ ) = name
  
instance Eq Algorithm where
  a1 == a2 = algName a1 == algName a2

--ok, new plan: Instead of generating dumb constraintless Algorithm structs for all expressions,
-- we can have the IR Defintion be a Tree (Maybe Algorithm, Expr). That way, we can omit a lot of useless filler.
-- Algorithm structs need only be annotated, if the semantics of the likelihood function are dependent on type info.

mostChaotic :: [PType] -> PType
mostChaotic = foldl1 downgrade

mostStructured :: [PType] -> PType
mostStructured = foldl1 upgrade

greaterThanLeft :: Algorithm
greaterThanLeft = Algorithm StubGreaterThan [SubExprNIsType 0 Deterministic] "greaterThanLeft" (const Integrate)

greaterThanRight :: Algorithm
greaterThanRight = Algorithm StubGreaterThan [SubExprNIsType 1 Deterministic] "greaterThanRight" (const Integrate)

greaterThanSigmoid :: Algorithm
greaterThanSigmoid = Algorithm StubGreaterThan [SubExprNIsType 0 Deterministic, SubExprNIsType 1 Deterministic] "greaterThanSigmoid" (const Integrate)

plusLeft :: Algorithm
plusLeft = Algorithm StubPlus [SubExprNIsType 0 Deterministic] "plusLeft" mostChaotic

plusRight :: Algorithm
plusRight = Algorithm StubPlus [SubExprNIsType 1 Deterministic] "plusRight" mostChaotic

multLeft :: Algorithm
multLeft = Algorithm StubMult [SubExprNIsType 0 Deterministic] "multLeft" mostChaotic

multRight :: Algorithm
multRight = Algorithm StubMult [SubExprNIsType 1 Deterministic] "multRight" mostChaotic

enumeratePlusLeft :: Algorithm
enumeratePlusLeft = Algorithm StubPlus [SubExprNIsNotType 0 Deterministic, SubExprNIsNotType 1 Deterministic] "enumeratePlusLeft" (const Chaos)

allAlgorithms :: [Algorithm]
allAlgorithms = [greaterThanLeft, greaterThanRight, greaterThanSigmoid, plusLeft, plusRight, multLeft, multRight, enumeratePlusLeft]

transpile :: Env TypeInfo a -> [IRDefinition a]
transpile = map transpileDefinition

transpileDefinition :: (String, Expr TypeInfo a) -> IRDefinition a
transpileDefinition (name, expression) = (name, transpileExpr expression)

-- OK, static analysis is amazing and just converted this lambda
-- (\alg -> and (map (\constr -> checkConstraint expr constr) (constraints alg) ) )
-- via this
-- (\alg -> all (checkConstraint expr) (constraints alg) )
-- into this
-- (all (checkConstraint expr) . constraints )

transpileExpr :: Expr TypeInfo a -> Tree (IRNode a)
transpileExpr expr = if likelihoodFunctionUsesTypeInfo $ toStub expr
  then case filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr of
    [alg] -> Node (Complex alg) (map transpileExpr $ recurse expr)
    [] -> error ("no algorithm found in transpiler in Expression " ++ (show $ toStub expr))
    algs -> error ("ambiguous algorithms in transpiler: " ++ show (map algName algs))
  else Node (Simple (toStub expr) (annotate expr)) (map transpileExpr $ recurse expr)
  where
      correctExpr = filter (checkExprMatches expr) allAlgorithms

annotate :: Expr TypeInfo a -> [Annotation a]
annotate expr = case expr of 
  ThetaI _ i    -> [IIndex i]
  Constant _ x  -> [IValue x]
  Call _ x      -> [IIdentifier x]
  LetIn _ x _ _ -> [IIdentifier x]
  Arg _ x _ _   -> [IIdentifier x]
  CallArg _ x _ -> [IIdentifier x]
  Lambda _ x _  -> [IIdentifier x]
  _             -> []

checkExprMatches :: Expr TypeInfo a -> Algorithm -> Bool
checkExprMatches e alg = toStub e == forExpression alg

checkConstraint :: Expr TypeInfo a -> Algorithm -> Constraint -> Bool
checkConstraint expr _ (SubExprNIsType n ptype) = ptype == p
  where TypeInfo r p = getTypeInfo (getSubExprs expr !! n)
checkConstraint expr _ (SubExprNIsNotType n ptype) = ptype /= p
  where TypeInfo r p = getTypeInfo (getSubExprs expr !! n)
checkConstraint expr alg ResultingTypeMatch = resPType == annotatedType
  where
    annotatedType = getP expr
    resPType = resultingType alg (map getP (getSubExprs expr))

arity :: ExprStub -> Int
arity = undefined

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubGreaterThan, StubMult, StubPlus]

toStub :: Expr x a -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  (ThetaI _ _)   -> StubThetaI
  (Uniform _)    -> StubUniform
  (Normal _)     -> StubNormal
  (Constant _ _) -> StubConstant
  Mult {}        -> StubMult
  Plus {}        -> StubPlus
  (Null _)       -> StubNull
  Cons {}        -> StubCons
  (Call _ _)     -> StubCall
  (Var _ _)      -> StubVar
  LetIn {}       -> StubLetIn
  Arg {}         -> StubArg
  CallArg {}     -> StubCallArg
  Lambda {}      -> StubLambda
  (ReadNN _ _ _) -> StubReadNN
  
