module ArbitrarySPLL (
  genExpr
, genProg
)where

import Test.QuickCheck

import SPLL.Lang.Lang
import SPLL.Lang.Types (TypeInfo, makeTypeInfo)

instance (Arbitrary a) => Arbitrary (Expr a) where
  arbitrary = genExpr
  
instance (Arbitrary a) => Arbitrary (Program a) where
  arbitrary = genProg
  
instance (Arbitrary a) => Arbitrary (TypeInfo a) where
  arbitrary = return makeTypeInfo -- TODO: generates untyped programs for now.

-- Property based testing: Define a Generator for Expr t a and Program t a:
genExpr :: (Arbitrary a) => Gen (Expr a)
genExpr = do
  names <- varNames
  genExprNames names

genProg :: (Arbitrary a) => Gen (Program a)
genProg = do
  names <- varNames
  genProgNames names

varNames :: Gen [String]
varNames = do
  size <- getSize
  let nNames = (size `div` 10) + 1
  k <- choose (0,nNames)
  vector k

genExprNames :: (Arbitrary a) => [String] -> Gen (Expr a)
genExprNames names = sized (genExprNames' names)

genExprNames' :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
genExprNames' varnames size = do
  generator <- elements $ map snd (filter (\(sizeReq, gen) -> sizeReq <= size) exprGens)
  generator varnames size
  
exprGens :: (Arbitrary a) => [(Int, [String] -> Int -> Gen (Expr a))]
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

mkNormal :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkNormal varnames size = do
  Normal <$> arbitrary

mkUniform :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkUniform varnames size = do
  Uniform <$> arbitrary
  
mkThetaI :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkThetaI varnames size = do
  t0 <- arbitrary
  t1 <- arbitrary
  ix <- arbitrary
  return $ ThetaI t0 (Var t1 "thetas") ix
  
mkGreaterThan :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkGreaterThan varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (GreaterThan t e1 e2)

mkMultF :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkMultF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultF t e1 e2)

mkMultI :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkMultI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (MultI t e1 e2)

mkPlusF :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkPlusF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusF t e1 e2)

mkPlusI :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkPlusI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (PlusI t e1 e2)

mkConditional :: (Arbitrary a) => [String] -> Int -> Gen (Expr a)
mkConditional varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 3)
  e2 <- genExprNames' varnames (size `div` 3)
  e3 <- genExprNames' varnames (size `div` 3)
  return (IfThenElse t e1 e2 e3)
  
genProgNames :: (Arbitrary a) =>  [String] -> Gen (Program a)
genProgNames names = do
  def_names <- choose (0, length names)
  defs <- mapM (\name -> do
    expr <- genExprNames names
    return (name, expr)) (take def_names names)
  return (Program defs [])
