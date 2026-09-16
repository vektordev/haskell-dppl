{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- The Arbitrary instances for Program/Expr/Value/TypeInfo are orphans by
-- design: they are test-suite fixtures, and the only way to un-orphan them
-- would be to declare them in SPLL.Lang.*, which would put a QuickCheck
-- dependency on the library itself.
{-# OPTIONS_GHC -Wno-orphans #-}

module ArbitrarySPLL (
  genExpr
, genProg
, genIdentifier
, genValidIdentifier
, Ty(..)
, genTy
, tyJoin
, tyCompatible
, genTypedProgram
, genTypedExpr
, genValueWide
, genRawFuzzExpr
, genRawFuzzProgram
, tyOfTypedExpr
, typedExprSize
, typedExprDepth
, shrinkTypedExpr
, shrinkTypedProgram
, typedLeaves
)where

import Test.QuickCheck
import Data.List (nub)
import Data.Maybe (isJust)

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
  (\v -> Expr makeTypeInfo (Constant v)) <$> arbitrary,
  (\n -> Expr makeTypeInfo (Var n)) <$> genLeafName
  ]
-- ReadNN is deliberately not generated here: TestParser's exprToString/parser
-- round-trip harness has no concrete syntax for an arbitrary-expression
-- ReadNN argument (only a bare call-position name resolves to one), so
-- including it here breaks prop_parseShowRoundtrip. It is still covered by
-- 'genRawFuzzExpr' below, which only needs to feed 'compile'/'validateProgram'
-- and has no round-trip requirement.
genExpr n = oneof [
  genExpr 0,
  (\a b -> Expr makeTypeInfo (Apply a b)) <$> genExpr (n `div` 2) <*> genExpr (n `div` 2),
  (\a b c -> Expr makeTypeInfo (IfThenElse a b c)) <$> genExpr (n `div` 3) <*> genExpr (n `div` 3) <*> genExpr (n `div` 3),
  (\x body -> Expr makeTypeInfo (Lambda x body)) <$> genValidIdentifier <*> genExpr (n-1),
  genInjFApp (n `div` 2),
  (\e i -> Expr makeTypeInfo (ThetaI e i)) <$> genExpr (n `div` 2) <*> arbitrary,
  (\e i -> Expr makeTypeInfo (Subtree e i)) <$> genExpr (n `div` 2) <*> arbitrary
  ]

-- | Full Expr-constructor coverage (every 'ExprF' constructor, incl. ReadNN),
-- for use by generators that only need to feed the compiler, not round-trip
-- through the parser's pretty-printer.
genRawFuzzExpr :: Int -> Gen Expr
genRawFuzzExpr 0 = oneof [
  (\v -> Expr makeTypeInfo (Constant v)) <$> genValueWide 3,
  (\n -> Expr makeTypeInfo (Var n)) <$> genLeafName
  ]
genRawFuzzExpr n = oneof [
  genExpr n,
  (\name body -> Expr makeTypeInfo (ReadNN name body)) <$> genValidIdentifier <*> genRawFuzzExpr (n-1)
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
  return (Expr makeTypeInfo (InjF (Named name) args))

-- Additional Arbitrary instances
instance Arbitrary Program where
  arbitrary = do
    numFuncs <- choose (0, 5)  -- reasonable limit for test cases
    numNeurals <- choose (0, 5)
    funcs <- vectorOf numFuncs genFunctionDecl
    neuralDecls <- vectorOf numNeurals genNeuralDecl
    return $ Program funcs neuralDecls [] []

genFunctionDecl :: Gen FnDecl
genFunctionDecl = do
  name <- genValidIdentifier
  numArgs <- choose (0, 3)  -- reasonable limit for test cases
  args <- vectorOf numArgs genValidIdentifier
  body <- arbitrary
  let expr = foldr (\x acc -> Expr makeTypeInfo (Lambda x acc)) body args
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
  let mainDecl = ("main", foldr (\x acc -> Expr makeTypeInfo (Lambda x acc)) mainBody mainArgs)
  extraFuncs <- vectorOf numExtraFuncs genRawFuzzFunctionDecl
  neuralDecls <- vectorOf numNeurals genNeuralDecl
  return $ Program (mainDecl : extraFuncs) neuralDecls [] []

genRawFuzzFunctionDecl :: Gen FnDecl
genRawFuzzFunctionDecl = do
  name <- genValidIdentifier
  numArgs <- choose (0, 3)
  args <- vectorOf numArgs genValidIdentifier
  body <- sized genRawFuzzExpr
  let expr = foldr (\x acc -> Expr makeTypeInfo (Lambda x acc)) body args
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
  generator <- elements $ map snd (filter (\(sizeReq, _) -> sizeReq <= size) exprGens)
  generator varnames size

exprGens :: [(Int, [String] -> Int -> Gen Expr)]
-- ThetaI, greaterThan, and the Int-typed arithmetic InjFs (multI/plusI) were
-- each commented out of this list at some point with no recorded reason, and
-- their generators left behind unreferenced. The generators are gone now, so
-- re-enabling any of them means writing it again -- which is the honest state
-- of things: one of the four, mkGreaterThan, had already lost its definition
-- while its commented entry stayed.
exprGens = [
    (0, mkNormal),
    (0, mkUniform),
    (2, mkMultF),
    (2, mkPlusF),
    (3, mkConditional)
  ]

mkNormal :: [String] -> Int -> Gen Expr
mkNormal _varnames _size = do
  ti <- arbitrary
  return $ Expr ti (Var "Normal")

mkUniform :: [String] -> Int -> Gen Expr
mkUniform _varnames _size = do
  ti <- arbitrary
  return $ Expr ti (Var "Uniform")

mkMultF :: [String] -> Int -> Gen Expr
mkMultF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (Expr t (InjF (Named "mult") [e1, e2]))

mkPlusF :: [String] -> Int -> Gen Expr
mkPlusF varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 2)
  e2 <- genExprNames' varnames (size `div` 2)
  return (Expr t (InjF (Named "plus") [e1, e2]))

mkConditional :: [String] -> Int -> Gen Expr
mkConditional varnames size = do
  t <- arbitrary
  e1 <- genExprNames' varnames (size `div` 3)
  e2 <- genExprNames' varnames (size `div` 3)
  e3 <- genExprNames' varnames (size `div` 3)
  return (Expr t (IfThenElse e1 e2 e3))

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
-- Milestone M1 widened this from the three scalars to the structured shapes
-- (tuples, Either, lists); 'Ty' is a test-local stand-in for the subset of
-- 'RType' the generator can build inhabitants of, not a copy of it.
--
-- 'TyAny' is not a generation target. It is the "this position's type is not
-- determined by the node itself" marker that type *recovery* needs: a
-- @left x@ node fixes only the left component, a @right y@ node only the
-- right, and neither says anything about the other. See 'tyOfTypedExpr'.
data Ty = TyFloat | TyInt | TyBool
        | TyTuple Ty Ty
        | TyEither Ty Ty
        | TyList Ty
        | TyAny
  deriving (Show, Eq)

-- | Size-bounded target types. Deliberately scalar-heavy: a structured target
-- multiplies the expression budget across components, and the invariant
-- properties still want a solid mass of the scalar shapes that reach a
-- probability function. Never emits 'TyAny'.
genTy :: Int -> Gen Ty
genTy n
  | n <= 0 = scalarTy
  | otherwise = frequency
      [ (6, scalarTy)
      , (2, TyTuple <$> genTy half <*> genTy half)
      , (2, TyEither <$> genTy half <*> genTy half)
      , (2, TyList <$> genTy half)
      ]
  where
    scalarTy = elements [TyFloat, TyInt, TyBool]
    half = n `div` 2

-- | Depth budget for the *type* (as opposed to the expression). Two is enough
-- for a tuple of lists or an Either of tuples without the component count
-- exploding.
tyDepth :: Int
tyDepth = 2

-- | A well-typed nullary "main" program of a randomly chosen type.
genTypedProgram :: Gen Program
genTypedProgram = do
  ty <- genTy tyDepth
  body <- sized (genTypedExpr ty)
  return $ Program [("main", body)] [] [] []

genTypedExpr :: Ty -> Int -> Gen Expr
genTypedExpr TyAny n = do
  -- Only reachable if a caller hands us a recovered type. Resolve the free
  -- position to a concrete one rather than failing.
  ty <- genTy 0
  genTypedExpr ty n
genTypedExpr ty n
  | n <= 0 = genTypedLeaf ty
  | otherwise = oneof (genTypedLeaf ty : genTypedRec ty n)

-- | Smallest inhabitants the *generator* uses. Note the list case: the
-- generator never emits a bare 'nul', because an empty-list constant carries
-- no element type and so would be opaque to 'tyOfTypedExpr'. A one-element
-- list is the smallest list whose type can be read back off the node.
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
genTypedLeaf TyAny = genTypedLeaf TyFloat
genTypedLeaf (TyTuple a b) = tuple <$> genTypedLeaf a <*> genTypedLeaf b
genTypedLeaf (TyEither a b) = oneof
  [ left <$> genTypedLeaf a
  , right <$> genTypedLeaf b
  ]
genTypedLeaf (TyList a) = (`cons` nul) <$> genTypedLeaf a

genTypedRec :: Ty -> Int -> [Gen Expr]
genTypedRec ty n =
  [ ifThenElse <$> genTypedExpr TyBool half <*> genTypedExpr ty half <*> genTypedExpr ty half
  ]
  -- Eliminators: reach the target type *through* a structured intermediate.
  -- These are what put the change-of-variables/dimension bookkeeping and the
  -- IRConformsTo structural checks in front of the invariant properties --
  -- building a tuple is easy, taking one apart is where the work is.
  ++ [ do other <- genTy 1
          tfst <$> genTypedExpr (TyTuple ty other) half
     , do other <- genTy 1
          tsnd <$> genTypedExpr (TyTuple other ty) half
     , lhead <$> genTypedExpr (TyList ty) half
     ]
  ++ tyRec
  where
    half = n `div` 2
    tyRec = case ty of
      TyAny -> []
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
        -- Structural tests: the only Bool-producing eliminators for lists and
        -- Either, and the reason those shapes get *observed* rather than just
        -- constructed and returned.
        , do a <- genTy 1
             isNull <$> genTypedExpr (TyList a) half
        , do a <- genTy 1
             b <- genTy 1
             sisLeft <$> genTypedExpr (TyEither a b) half
        , do a <- genTy 1
             b <- genTy 1
             sisRight <$> genTypedExpr (TyEither a b) half
        ]
      TyTuple a b ->
        [ tuple <$> genTypedExpr a half <*> genTypedExpr b half ]
      TyEither a b ->
        [ left <$> genTypedExpr a (n - 1)
        , right <$> genTypedExpr b (n - 1)
        ]
      TyList a ->
        [ cons <$> genTypedExpr a half <*> genTypedExpr (TyList a) half
        , ltail <$> genTypedExpr (TyList a) (n - 1)
        ]

-- ---------------------------------------------------------------------------
-- Type-preserving shrinking for the typed generator.
--
-- Design: typed-program-generator-expansion, Axis 2 / milestone M-S.
--
-- QuickCheck's default (absent) shrink leaves a failure reported as a
-- '--quickcheck-replay' seed against a large opaque draw, and those seeds
-- replay the RNG stream rather than the draw, so they do not survive an edit
-- to the generator or the property. A structural shrink would not help
-- either: almost every structural reduction of a well-typed SPLL expression
-- is ill-typed, so it is rejected downstream and reduces nothing.
--
-- Shrinking therefore has to be type-directed for the same reason generation
-- is. Because generation already is, the two are the same per-'Ty' table read
-- in opposite directions: 'genTypedLeaf' answers "some inhabitant of this Ty",
-- 'typedLeaves' answers "the smallest inhabitants of this Ty".

-- | The 'Ty' a 'genTypedExpr' output is guaranteed to have, recovered from the
-- node shape alone (the generator annotates every node with 'makeTypeInfo',
-- so the annotation carries nothing to read).
--
-- Total over the typed generator's output space and 'Nothing' outside it,
-- which is what makes 'shrinkTypedExpr' safe to apply to an arbitrary 'Expr':
-- an unrecognised node simply does not shrink, rather than shrinking to
-- something ill-typed.
tyOfTypedExpr :: Expr -> Maybe Ty
tyOfTypedExpr e = case node e of
  Constant (VFloat _) -> Just TyFloat
  Constant (VInt _)   -> Just TyInt
  Constant (VBool _)  -> Just TyBool
  Var "Uniform"       -> Just TyFloat
  Var "Normal"        -> Just TyFloat
  -- Both arms carry the node's type, and each may pin a different part of it
  -- (@if c then left x else right y@ is the canonical case), so the arms are
  -- joined rather than the first recognised one taken. A join failure means
  -- the node is outside the generator's output space.
  IfThenElse _ t f    -> case (tyOfTypedExpr t, tyOfTypedExpr f) of
    (Just a, Just b) -> tyJoin a b
    (Just a, Nothing) -> Just a
    (Nothing, mb)    -> mb
  InjF (Named f) args -> tyOfTypedInjF f args
  _                   -> Nothing

-- | Result type of an InjF application the typed generator can emit. The
-- structured entries are computed from the arguments rather than looked up:
-- @TCons@ is as wide as its components, the eliminators are as narrow as the
-- part of their argument's type they select, and @left@/@right@ pin only one
-- side of the Either they build (the other stays 'TyAny').
tyOfTypedInjF :: String -> [Expr] -> Maybe Ty
tyOfTypedInjF "TCons" [a, b] = TyTuple <$> tyOfTypedExpr a <*> tyOfTypedExpr b
tyOfTypedInjF "fst"   [x]    = tyOfTypedExpr x >>= \t -> case t of
  TyTuple a _ -> Just a
  _           -> Nothing
tyOfTypedInjF "snd"   [x]    = tyOfTypedExpr x >>= \t -> case t of
  TyTuple _ b -> Just b
  _           -> Nothing
-- The tail is deliberately not consulted: it may be the element-type-free
-- 'nul', and the head alone determines the list's element type.
tyOfTypedInjF "Cons"  [h, _] = TyList <$> tyOfTypedExpr h
tyOfTypedInjF "head"  [x]    = tyOfTypedExpr x >>= \t -> case t of
  TyList a -> Just a
  _        -> Nothing
tyOfTypedInjF "tail"  [x]    = tyOfTypedExpr x >>= \t -> case t of
  TyList a -> Just (TyList a)
  _        -> Nothing
tyOfTypedInjF "left"  [x]    = (`TyEither` TyAny) <$> tyOfTypedExpr x
tyOfTypedInjF "right" [x]    = TyEither TyAny <$> tyOfTypedExpr x
tyOfTypedInjF f       _      = lookup f typedInjFResultTy

-- | Result type of every *scalar* InjF the typed generator can emit. Note that
-- some generator combinators expand into others ('#-#' is @plus a (neg b)@,
-- 'bernoulli' is @lt uniform (constF p)@, 'dice' is nested 'ifThenElse'), so
-- this list covers the realized constructor space, not the combinator list.
typedInjFResultTy :: [(String, Ty)]
typedInjFResultTy =
  [ ("mult", TyFloat), ("plus", TyFloat), ("neg", TyFloat), ("exp", TyFloat)
  , ("plusI", TyInt), ("negI", TyInt)
  , ("gt", TyBool), ("lt", TyBool), ("and", TyBool), ("or", TyBool)
  , ("not", TyBool)
  , ("isNull", TyBool), ("isLeft", TyBool), ("isRight", TyBool)
  ]

-- | Least upper bound of two recovered types: 'TyAny' is the unknown that
-- either side may fill in, and two concrete types join only if they are equal
-- (structurally, component-wise). 'Nothing' means the two are incompatible,
-- which for an expression the generator produced cannot happen -- it means the
-- node is outside the recognised space.
tyJoin :: Ty -> Ty -> Maybe Ty
tyJoin TyAny t = Just t
tyJoin t TyAny = Just t
tyJoin (TyTuple a b)  (TyTuple c d)  = TyTuple  <$> tyJoin a c <*> tyJoin b d
tyJoin (TyEither a b) (TyEither c d) = TyEither <$> tyJoin a c <*> tyJoin b d
tyJoin (TyList a)     (TyList b)     = TyList   <$> tyJoin a b
tyJoin a b
  | a == b    = Just a
  | otherwise = Nothing

-- | Can these two recovered types describe the same expression? This, not
-- equality, is the shrinker's type-preservation test: @left 0@ recovers as
-- @Either Float ?@ and @right True@ as @Either ? Bool@, and in a context that
-- fixes @Either Float Bool@ either may legitimately replace the other.
tyCompatible :: Ty -> Ty -> Bool
tyCompatible a b = isJust (tyJoin a b)

-- | Node count. Used both as the shrinker's well-foundedness measure and by
-- the coverage instrumentation in TestFuzz.
typedExprSize :: Expr -> Int
typedExprSize e = 1 + sum (map typedExprSize (children e))

-- | Longest root-to-leaf path, counting the root as depth 1.
typedExprDepth :: Expr -> Int
typedExprDepth e = case children e of
  [] -> 1
  cs -> 1 + maximum (map typedExprDepth cs)

children :: Expr -> [Expr]
children e = case node e of
  IfThenElse c t f -> [c, t, f]
  InjF _ args      -> args
  _                -> []

-- | The smallest inhabitants of a 'Ty' -- the shrinker's workhorse reduction,
-- "replace any subexpression with a type-correct leaf". Constants only: a
-- distribution leaf ('normal'/'uniform') is the same size but strictly more
-- interesting, so offering it as a shrink target would let the shrinker walk
-- sideways forever.
typedLeaves :: Ty -> [Expr]
typedLeaves TyFloat = [constF 0]
typedLeaves TyInt   = [constI 0]
typedLeaves TyBool  = [constB False, constB True]
-- No leaf is offered for a free position, and that propagates: a leaf for
-- @Either Float ?@ is @left 0@ and never @right <something>@, because
-- committing the unknown side to a concrete type is exactly the shrink that
-- would be ill-typed in the surrounding context.
typedLeaves TyAny   = []
typedLeaves (TyTuple a b) =
  [ tuple x y | x <- take 1 (typedLeaves a), y <- take 1 (typedLeaves b) ]
typedLeaves (TyEither a b) =
  [ left x  | x <- take 1 (typedLeaves a) ]
  ++ [ right y | y <- take 1 (typedLeaves b) ]
typedLeaves (TyList a) = [ cons x nul | x <- take 1 (typedLeaves a) ]

-- | Type-preserving shrink for an expression produced by 'genTypedExpr'.
--
-- Every candidate has the same 'Ty' as its input and a strictly smaller node
-- count, so the result is well-founded and never hands the property an
-- ill-typed program (which would be discarded, minimizing nothing).
shrinkTypedExpr :: Expr -> [Expr]
shrinkTypedExpr e = case tyOfTypedExpr e of
  Nothing -> []
  Just ty -> nub (filter smaller (typedLeaves ty ++ collapses ty e ++ childShrinks e))
  where
    smaller c = typedExprSize c < typedExprSize e

-- | Replace the node by one of its own same-typed subexpressions: either
-- branch of an 'IfThenElse' (both share the node's type), or a type-matching
-- argument of an InjF/comparison (@neg x@ and @x + y@ shrink to @x@; @x > y@
-- does not, its arguments being Float where it is Bool).
collapses :: Ty -> Expr -> [Expr]
collapses ty e = filter (maybe False (tyCompatible ty) . tyOfTypedExpr) $ case node e of
  IfThenElse _ t f -> [t, f]
  InjF _ args      -> args
  _                -> []

-- | Shrink one child at a time, keeping the node and every sibling. This is
-- what actually minimizes a deep program: the collapses above cut whole
-- subtrees, this reduces the ones that have to stay.
childShrinks :: Expr -> [Expr]
childShrinks e = case node e of
  IfThenElse c t f ->
    [ rebuild (IfThenElse c' t f) | c' <- shrinkTypedExpr c ]
    ++ [ rebuild (IfThenElse c t' f) | t' <- shrinkTypedExpr t ]
    ++ [ rebuild (IfThenElse c t f') | f' <- shrinkTypedExpr f ]
  InjF name args ->
    [ rebuild (InjF name args') | args' <- shrinkOne shrinkTypedExpr args ]
  _ -> []
  where rebuild = Expr (ann e)

-- | All the ways to replace exactly one list element by one of its shrinks.
shrinkOne :: (a -> [a]) -> [a] -> [[a]]
shrinkOne _ [] = []
shrinkOne f (x:xs) =
  [ x' : xs | x' <- f x ] ++ [ x : xs' | xs' <- shrinkOne f xs ]

-- | Type-preserving shrink for a 'genTypedProgram' draw: shrink the body of
-- @main@ and leave the (empty) neural/ADT/writeLogits sections alone. Extra
-- function declarations, if a later milestone adds them, are preserved
-- untouched -- a wrong-but-conservative shrink is a big counterexample, while
-- a wrong-and-aggressive one is a *different* counterexample, which is worse.
shrinkTypedProgram :: Program -> [Program]
shrinkTypedProgram p = case lookup "main" (functions p) of
  Nothing   -> []
  Just body ->
    [ p { functions = map (replaceMain body') (functions p) }
    | body' <- shrinkTypedExpr body
    ]
  where
    replaceMain body' (n, b) = if n == "main" then (n, body') else (n, b)
