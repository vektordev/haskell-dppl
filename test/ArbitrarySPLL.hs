module ArbitrarySPLL (
  genExpr
, genProg
)where

import Test.QuickCheck

import SPLL.Lang

--instance (Arbitrary a, Arbitrary t) => Arbitrary (Expr t a) where
--  arbitrary = genExpr

-- Property based testing: Define a Generator for Expr t a and Program t a:
genExpr :: (Arbitrary t) => Gen (Expr t a)
genExpr = do
  names <- varNames
  genExprNames names

genProg :: Arbitrary t => Gen (Program t a)
genProg = do
  names <- varNames
  genProgNames names

varNames :: Gen [String]
varNames = do
  size <- getSize
  let nNames = (size `div` 10) + 1
  k <- choose (0,nNames)
  vector k

genExprNames :: (Arbitrary t) => [String] -> Gen (Expr t a)
genExprNames names = sized (genExprNames' names)

genExprNames' :: (Arbitrary t) => [String] -> Int -> Gen (Expr t a)
genExprNames' varnames size = do
  generator <- elements $ map snd (filter (\(sizeReq, gen) -> sizeReq <= size) exprGens)
  generator varnames size
  
exprGens :: (Arbitrary t) => [(Int, [String] -> Int -> Gen (Expr t a))]
exprGens = [
    (0, mkNormal),
    (0, mkUniform),
    (0, mkThetaI),
    (2, mkGreaterThan),
    (2, mkMultF),
    (2, mkMultI),
    (2, mkPlusF),
    (2, mkPlusI),
    (3, mkConditional)
  ]

mkNormal :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkNormal varnames size = do
  Normal <$> arbitrary

mkUniform :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkUniform varnames size = do
  Uniform <$> arbitrary
  
mkThetaI :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkThetaI varnames size = do
  t <- arbitrary
  ix <- arbitrary
  return $ ThetaI t ix
  
mkGreaterThan :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkGreaterThan varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (GreaterThan t e1 e2)

mkMultF :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkMultF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultF t e1 e2)

mkMultI :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkMultI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultI t e1 e2)

mkPlusF :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkPlusF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusF t e1 e2)

mkPlusI :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkPlusI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusI t e1 e2)

mkConditional :: Arbitrary x => [String] -> Int -> Gen (Expr x a)
mkConditional varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 3)
  e2 <- genExprNames' varnames (size `div` 3)
  e3 <- genExprNames' varnames (size `div` 3)
  return (IfThenElse t e1 e2 e3)
  
genProgNames :: (Arbitrary t) => [String] -> Gen (Program t a)
genProgNames names = do
  def_names <- choose (0, length names)
  defs <- mapM (\name -> do
    expr <- genExprNames names
    return (name, expr)) (take def_names names)
  main <- genExprNames names
  return (Program defs main)
