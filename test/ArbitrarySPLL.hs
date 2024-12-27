{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module ArbitrarySPLL (
  genExpr
, genProg
, genIdentifier
, genValidIdentifier
)where

import Test.QuickCheck

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Parser (reserved)

-- Arbitrary instances for generating test data
instance Arbitrary Value where
  arbitrary = oneof [
    VInt <$> arbitrary,
    VFloat <$> choose (-100, 100)
    ]

-- Generate simple identifiers
genIdentifier :: Gen String
genIdentifier = do
  first <- elements ['a'..'z']
  rest <- listOf (elements $ ['a'..'z'] ++ ['0'..'9'])
  return (first:rest)
  
-- Generator for valid identifiers (not in reserved list)
genValidIdentifier :: Gen String
genValidIdentifier = do
  ident <- genIdentifier
  if ident `elem` reserved
    then genValidIdentifier  -- try again
    else return ident

-- Generate simple expressions
instance Arbitrary Expr where
  arbitrary = sized genExpr

-- TODO: Missing a bunch of patterns.
genExpr :: Int -> Gen Expr
genExpr 0 = oneof [
  Constant makeTypeInfo <$> arbitrary,
  Var makeTypeInfo <$> genValidIdentifier
  ]
genExpr n = oneof [
  genExpr 0,
  Apply makeTypeInfo <$> genExpr (n `div` 2) <*> genExpr (n `div` 2),
  IfThenElse makeTypeInfo <$> genExpr (n `div` 3) <*> genExpr (n `div` 3) <*> genExpr (n `div` 3),
  Lambda makeTypeInfo <$> genValidIdentifier <*> genExpr (n-1)
  ]

-- Additional Arbitrary instances
instance Arbitrary Program where
  arbitrary = do
    numFuncs <- choose (0, 5)  -- reasonable limit for test cases
    numNeurals <- choose (0, 5)
    funcs <- vectorOf numFuncs genFunctionDecl
    neurals <- vectorOf numNeurals genNeuralDecl
    return $ Program funcs neurals

genFunctionDecl :: Gen FnDecl
genFunctionDecl = do
  name <- genValidIdentifier
  numArgs <- choose (0, 3)  -- reasonable limit for test cases
  args <- vectorOf numArgs genValidIdentifier
  body <- arbitrary
  let expr = foldr (Lambda makeTypeInfo) body args
  return (name, expr)

genNeuralDecl :: Gen NeuralDecl
genNeuralDecl = do
  name <- genValidIdentifier
  -- For now just using TInt, could expand to arbitrary RType if needed
  values <- listOf1 (VInt <$> arbitrary)
  return (name, TInt, EnumList values)

instance Arbitrary TypeInfo where
  arbitrary = return makeTypeInfo -- TODO: generates untyped programs for now.

genProg :: Gen Program
genProg = do
  names <- varNames
  genProgNames names

varNames :: Gen [String]
varNames = do
  size <- getSize
  let nNames = (size `div` 10) + 1
  k <- choose (0,nNames)
  vector k

genExprNames :: [String] -> Gen Expr
genExprNames names = sized (genExprNames' names)

genExprNames' :: [String] -> Int -> Gen Expr
genExprNames' varnames size = do
  generator <- elements $ map snd (filter (\(sizeReq, gen) -> sizeReq <= size) exprGens)
  generator varnames size
  
exprGens :: [(Int, [String] -> Int -> Gen Expr)]
exprGens = [
    (0, mkNormal),
    (0, mkUniform),
    --(0, mkThetaI),
    --(2, mkGreaterThan),
    (2, mkMultF),
    --(2, mkMultI),
    (2, mkPlusF),
    --(2, mkPlusI),
    (3, mkConditional)
  ]

mkNormal :: [String] -> Int -> Gen Expr
mkNormal varnames size = do
  Normal <$> arbitrary

mkUniform :: [String] -> Int -> Gen Expr
mkUniform varnames size = do
  Uniform <$> arbitrary
  
mkThetaI :: [String] -> Int -> Gen Expr
mkThetaI varnames size = do
  t0 <- arbitrary
  t1 <- arbitrary
  ix <- arbitrary
  return $ ThetaI t0 (Var t1 "thetas") ix
  
mkGreaterThan :: [String] -> Int -> Gen Expr
mkGreaterThan varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (GreaterThan t e1 e2)

mkMultF :: [String] -> Int -> Gen Expr
mkMultF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultF t e1 e2)

mkMultI :: [String] -> Int -> Gen Expr
mkMultI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultI t e1 e2)

mkPlusF :: [String] -> Int -> Gen Expr
mkPlusF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusF t e1 e2)

mkPlusI :: [String] -> Int -> Gen Expr
mkPlusI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusI t e1 e2)

mkConditional :: [String] -> Int -> Gen Expr
mkConditional varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 3)
  e2 <- genExprNames' varnames (size `div` 3)
  e3 <- genExprNames' varnames (size `div` 3)
  return (IfThenElse t e1 e2 e3)
  
genProgNames ::  [String] -> Gen Program
genProgNames names = do
  def_names <- choose (0, length names)
  defs <- mapM (\name -> do
    expr <- genExprNames names
    return (name, expr)) (take def_names names)
  return (Program defs [])
