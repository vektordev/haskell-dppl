module ArbitrarySPLL (
  genExpr
, genProg
)where

import Test.QuickCheck

import SPLL.Lang.Lang
import SPLL.Lang.Types (TypeInfo, makeTypeInfo)

instance Arbitrary (Expr) where
  arbitrary = genExpr

instance Arbitrary Program where
  arbitrary = genProg

instance Arbitrary TypeInfo where
  arbitrary = return makeTypeInfo -- TODO: generates untyped programs for now.

-- Property based testing: Define a Generator for Expr t a and Program t a:
genExpr :: Gen Expr
genExpr = do
  names <- varNames
  genExprNames names

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

genExprNames' :: [String] -> Int -> Gen (Expr)
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
