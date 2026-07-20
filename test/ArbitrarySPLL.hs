{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module ArbitrarySPLL (
  genExpr
, genProg
, genIdentifier
, genValidIdentifier
, Ty(..)
, genTypedProgram
, genTypedExpr
, genValueWide
, genRawFuzzExpr
, genRawFuzzProgram
)where

import Test.QuickCheck

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Parser (reserved)
import PredefinedFunctions (globalFEnv, parameterCount)
import SPLL.Prelude

-- Arbitrary instances for generating test data.
-- Kept deliberately narrow (VInt/VFloat only): TestParser's
-- prop_parseShowRoundtrip pretty-prints every Constant this instance
-- produces and does not (yet) handle VBool/VUnit/VTuple/VEither/VList/VSymbol.
-- The wider raw-Expr fuzz generator below uses 'genValueWide' instead of this
-- instance so it can cover those shapes without breaking that test.
instance Arbitrary Value where
  arbitrary = oneof [
    VInt <$> arbitrary,
    VFloat <$> choose (-100, 100)
    ]

-- | Every GenericValue leaf that carries no closure/function payload
-- (VClosure is intentionally excluded -- it is a runtime-only value, never
-- produced by a surface Constant).
genValueWide :: Int -> Gen Value
genValueWide n
  | n <= 0 = oneof leaves
  | otherwise = oneof (leaves ++ recCases)
  where
    leaves =
      [ VBool <$> arbitrary
      , VInt <$> arbitrary
      , VFloat <$> choose (-100, 100)
      , VSymbol <$> genIdentifier
      , pure VUnit
      ]
    recCases =
      [ VTuple <$> genValueWide (n `div` 2) <*> genValueWide (n `div` 2)
      , (VEither . Left) <$> genValueWide (n - 1)
      , (VEither . Right) <$> genValueWide (n - 1)
      , VList . constructVListGen <$> listOf (genValueWide (n `div` 2))
      ]

constructVListGen :: [Value] -> GenericList Value
constructVListGen = foldr ListCont EmptyList

-- Generate simple identifiers
genIdentifier :: Gen String
genIdentifier = do
  first <- elements ['a'..'z']
  rest <- listOf (elements $ ['a'..'z'] ++ ['0'..'9'])
  return (first:rest)

-- Generator for valid identifiers (not reserved, not a builtin InjF name)
genValidIdentifier :: Gen String
genValidIdentifier = do
  ident <- genIdentifier
  if ident `elem` reserved || ident `elem` map fst (globalFEnv [])
    then genValidIdentifier  -- try again
    else return ident

-- | Full-space, untyped Expr generator: covers every Expr constructor. Used
-- for "does the compiler crash (rather than gracefully return Left) on any
-- syntactically valid AST" style fuzzing -- it makes no attempt at
-- well-typedness, so most generated programs are expected to be rejected by
-- validation/type inference.
instance Arbitrary Expr where
  arbitrary = sized genExpr

genExpr :: Int -> Gen Expr
genExpr 0 = oneof [
  Constant makeTypeInfo <$> arbitrary,
  Var makeTypeInfo <$> genLeafName
  ]
-- ReadNN is deliberately not generated here: TestParser's exprToString/parser
-- round-trip harness has no concrete syntax for an arbitrary-expression
-- ReadNN argument (only a bare call-position name resolves to one), so
-- including it here breaks prop_parseShowRoundtrip. It is still covered by
-- 'genRawFuzzExpr' below, which only needs to feed 'compile'/'validateProgram'
-- and has no round-trip requirement.
genExpr n = oneof [
  genExpr 0,
  Apply makeTypeInfo <$> genExpr (n `div` 2) <*> genExpr (n `div` 2),
  IfThenElse makeTypeInfo <$> genExpr (n `div` 3) <*> genExpr (n `div` 3) <*> genExpr (n `div` 3),
  Lambda makeTypeInfo <$> genValidIdentifier <*> genExpr (n-1),
  genInjFApp (n `div` 2),
  ThetaI makeTypeInfo <$> genExpr (n `div` 2) <*> arbitrary,
  Subtree makeTypeInfo <$> genExpr (n `div` 2) <*> arbitrary,
  GreaterThan makeTypeInfo <$> genExpr (n `div` 2) <*> genExpr (n `div` 2),
  LessThan makeTypeInfo <$> genExpr (n `div` 2) <*> genExpr (n `div` 2)
  ]

-- | Full Expr-constructor coverage (all 11 constructors, including ReadNN),
-- for use by generators that only need to feed the compiler, not round-trip
-- through the parser's pretty-printer.
genRawFuzzExpr :: Int -> Gen Expr
genRawFuzzExpr 0 = oneof [
  Constant makeTypeInfo <$> genValueWide 3,
  Var makeTypeInfo <$> genLeafName
  ]
genRawFuzzExpr n = oneof [
  genExpr n,
  ReadNN makeTypeInfo <$> genValidIdentifier <*> genRawFuzzExpr (n-1)
  ]

-- Leaf variable references: a mix of fresh identifiers (mostly unbound --
-- exercises the "unbound variable" rejection path) and the two nullary
-- distribution leaves ("Uniform"/"Normal"). Predefined-function names are
-- deliberately excluded here: a bare `Var "mult"` round-trips through the
-- parser as an eta-expanded lambda rather than the same Var node (InjF names
-- are only special-cased in call position), so it would break
-- prop_parseShowRoundtrip; genInjFName is still exercised via the InjF case below.
genLeafName :: Gen String
genLeafName = oneof [genValidIdentifier, elements ["Uniform", "Normal"]]

genInjFName :: Gen String
genInjFName = elements (map fst (globalFEnv []))

-- Named-call arity in the concrete syntax is positional (space-separated,
-- like Haskell application) and must match 'parameterCount' exactly, or the
-- printed-then-reparsed program silently becomes a different AST (fewer args
-- than expected builds a partial-application closure instead of the direct
-- InjF node) rather than round-tripping -- so, unlike raw-Expr's other
-- combinators, arity here is not left arbitrary.
genInjFApp :: Int -> Gen Expr
genInjFApp n = do
  name <- genInjFName
  args <- vectorOf (parameterCount [] name) (genExpr n)
  return (InjF makeTypeInfo (Named name) args)

-- Additional Arbitrary instances
instance Arbitrary Program where
  arbitrary = do
    numFuncs <- choose (0, 5)  -- reasonable limit for test cases
    numNeurals <- choose (0, 5)
    funcs <- vectorOf numFuncs genFunctionDecl
    neurals <- vectorOf numNeurals genNeuralDecl
    return $ Program funcs neurals [] []

genFunctionDecl :: Gen FnDecl
genFunctionDecl = do
  name <- genValidIdentifier
  numArgs <- choose (0, 3)  -- reasonable limit for test cases
  args <- vectorOf numArgs genValidIdentifier
  body <- arbitrary
  let expr = foldr (Lambda makeTypeInfo) body args
  return (name, expr)

-- | Full-space raw program generator: like the 'Arbitrary Program' instance,
-- but function bodies are drawn from 'genRawFuzzExpr' (all 11 Expr
-- constructors, wide Constant leaves) instead of the round-trip-safe
-- 'arbitrary'. Used only for "the compiler must not crash" fuzzing, never
-- for parser round-trip testing.
genRawFuzzProgram :: Gen Program
genRawFuzzProgram = do
  numExtraFuncs <- choose (0, 4)
  numNeurals <- choose (0, 5)
  -- Guarantee a "main" declaration so most draws get past the "missing main"
  -- validator check and actually exercise the deeper compilation stages.
  mainBody <- sized genRawFuzzExpr
  mainArgs <- choose (0, 3) >>= flip vectorOf genValidIdentifier
  let mainDecl = ("main", foldr (Lambda makeTypeInfo) mainBody mainArgs)
  extraFuncs <- vectorOf numExtraFuncs genRawFuzzFunctionDecl
  neurals <- vectorOf numNeurals genNeuralDecl
  return $ Program (mainDecl : extraFuncs) neurals [] []

genRawFuzzFunctionDecl :: Gen FnDecl
genRawFuzzFunctionDecl = do
  name <- genValidIdentifier
  numArgs <- choose (0, 3)
  args <- vectorOf numArgs genValidIdentifier
  body <- sized genRawFuzzExpr
  let expr = foldr (Lambda makeTypeInfo) body args
  return (name, expr)

genNeuralDecl :: Gen NeuralDecl
genNeuralDecl = do
  name <- genValidIdentifier
  -- For now just using TInt, could expand to arbitrary RType if needed
  values <- listOf1 (VInt <$> arbitrary)
  return (name, TInt, Just $ MultiDiscretes values)

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
  ti <- arbitrary
  return $ Var ti "Normal"

mkUniform :: [String] -> Int -> Gen Expr
mkUniform varnames size = do
  ti <- arbitrary
  return $ Var ti "Uniform"

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
  return (InjF t (Named "mult") [e1, e2])

mkMultI :: [String] -> Int -> Gen Expr
mkMultI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (InjF t (Named "multI") [e1, e2])

mkPlusF :: [String] -> Int -> Gen Expr
mkPlusF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (InjF t (Named "plus") [e1, e2])

mkPlusI :: [String] -> Int -> Gen Expr
mkPlusI varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (InjF t (Named "plusI") [e1, e2])

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
  return (Program defs [] [] [])

-- ---------------------------------------------------------------------------
-- Well-typed-by-construction generator (scalar fragment: Float/Int/Bool).
--
-- The raw 'Expr'/'Program' Arbitrary instances above cover the full AST shape
-- but very rarely type-check (an unconstrained Apply/Var/Lambda soup almost
-- never lines up), so they are unsuitable for exercising inference invariants
-- ("prob sums to 1", "topK never inflates", ...) without a prohibitive
-- discard rate. This generator instead builds expressions bottom-up, indexed
-- by the 'Ty' they are guaranteed to produce, using the same combinators
-- 'SPLL.Prelude'/'SPLL.Examples' hand-write example programs with. It only
-- covers Float/Int/Bool scalars (no lambdas/tuples/lists/ADTs/neural nets) --
-- narrow by design, so almost every generated 'Program' compiles.
data Ty = TyFloat | TyInt | TyBool deriving (Show, Eq)

tyToRType :: Ty -> RType
tyToRType TyFloat = TFloat
tyToRType TyInt = TInt
tyToRType TyBool = TBool

-- | A well-typed nullary "main" program of a randomly chosen scalar type.
genTypedProgram :: Gen Program
genTypedProgram = do
  ty <- elements [TyFloat, TyInt, TyBool]
  body <- sized (genTypedExpr ty)
  return $ Program [("main", body)] [] [] []

genTypedExpr :: Ty -> Int -> Gen Expr
genTypedExpr ty n
  | n <= 0 = genTypedLeaf ty
  | otherwise = oneof (genTypedLeaf ty : genTypedRec ty n)

genTypedLeaf :: Ty -> Gen Expr
genTypedLeaf TyFloat = oneof
  [ pure normal
  , pure uniform
  , constF <$> choose (-10, 10)
  ]
genTypedLeaf TyInt = oneof
  [ constI <$> choose (-10, 10)
  , dice <$> choose (2, 6)
  ]
genTypedLeaf TyBool = oneof
  [ constB <$> arbitrary
  , bernoulli <$> choose (0.01, 0.99)
  ]

genTypedRec :: Ty -> Int -> [Gen Expr]
genTypedRec ty n =
  [ ifThenElse <$> genTypedExpr TyBool half <*> genTypedExpr ty half <*> genTypedExpr ty half
  ] ++ tyRec
  where
    half = n `div` 2
    third = n `div` 3
    tyRec = case ty of
      TyFloat ->
        [ (#+#) <$> genTypedExpr TyFloat half <*> genTypedExpr TyFloat half
        , (#-#) <$> genTypedExpr TyFloat half <*> genTypedExpr TyFloat half
        , (#*#) <$> genTypedExpr TyFloat half <*> genTypedExpr TyFloat half
        , negF <$> genTypedExpr TyFloat (n - 1)
        , expF <$> genTypedExpr TyFloat (n - 1)
        ]
      TyInt ->
        [ (#<+>#) <$> genTypedExpr TyInt half <*> genTypedExpr TyInt half
        , (#<->#) <$> genTypedExpr TyInt half <*> genTypedExpr TyInt half
        , negIF <$> genTypedExpr TyInt (n - 1)
        ]
      TyBool ->
        [ (#&&#) <$> genTypedExpr TyBool half <*> genTypedExpr TyBool half
        , (#||#) <$> genTypedExpr TyBool half <*> genTypedExpr TyBool half
        , (#!#) <$> genTypedExpr TyBool (n - 1)
        , (#>#) <$> genTypedExpr TyFloat half <*> genTypedExpr TyFloat half
        , (#<#) <$> genTypedExpr TyFloat half <*> genTypedExpr TyFloat half
        ]
