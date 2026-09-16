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
, tyGeneralizes
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
, LetShape(..)
, letShapeOf
, mentionsVar
, uniquifyBinders
, uniquifyBindersFrom
)where

import Test.QuickCheck
import Data.List (nub)
import Data.Maybe (fromMaybe)

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
-- 'SPLL.Prelude'/'SPLL.Examples' hand-write example programs with.
--
-- Milestone M1 widened this from the three scalars to the structured shapes
-- (tuples, Either, lists); 'Ty' is a test-local stand-in for the subset of
-- 'RType' the generator can build inhabitants of, not a copy of it.
-- Milestone M2 added 'let'-bindings, and with them a scope: generation,
-- type recovery and shrinking are all now indexed by a 'TyEnv' as well as by
-- a 'Ty'.
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

-- | The variables in scope and the 'Ty' each was bound at. Innermost binding
-- first, so a plain 'lookup' implements shadowing -- though the generator
-- itself never shadows (see 'freshName').
type TyEnv = [(String, Ty)]

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

-- | Generate at a type in the empty scope. The scope-carrying worker is
-- 'genTypedExprIn'; this is the entry point every property uses.
--
-- The result's binders are made globally distinct before it is handed out --
-- see 'uniquifyBinders' for why that is a hard requirement rather than
-- tidiness. A caller that *composes* two draws into one program (TestFuzz's
-- 'genMixturePair' does) must re-prefix at least one of them with
-- 'uniquifyBindersFrom', since two independent draws both start at @v0@.
genTypedExpr :: Ty -> Int -> Gen Expr
genTypedExpr ty n = uniquifyBinders <$> genTypedExprIn [] ty n

genTypedExprIn :: TyEnv -> Ty -> Int -> Gen Expr
genTypedExprIn env TyAny n = do
  -- Only reachable if a caller hands us a recovered type. Resolve the free
  -- position to a concrete one rather than failing.
  ty <- genTy 0
  genTypedExprIn env ty n
genTypedExprIn env ty n
  | n <= 0 = genTypedLeafIn env ty
  | otherwise = oneof (genTypedLeafIn env ty : genTypedRec env ty n)

-- | A leaf at the target type: either a closed one ('genTypedLeaf') or a
-- variable of that exact type from the enclosing scope.
--
-- Variables are weighted *above* closed leaves, deliberately. A 'let' whose
-- body never mentions its bound variable is an uninteresting draw -- the
-- binding is dead, and none of the inversion engines this milestone exists to
-- reach ever see it -- so once a scope is non-empty the generator leans on it.
genTypedLeafIn :: TyEnv -> Ty -> Gen Expr
genTypedLeafIn env ty = case [ v | (v, t) <- env, t == ty ] of
  [] -> genTypedLeaf ty
  vs -> frequency [ (2, genTypedLeaf ty), (3, elements (map varE vs)) ]

varE :: String -> Expr
varE v = Expr makeTypeInfo (Var v)

-- | Smallest *closed* inhabitants the generator uses. Note the list case: the
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

genTypedRec :: TyEnv -> Ty -> Int -> [Gen Expr]
genTypedRec env ty n =
  [ ifThenElse <$> gen TyBool half <*> gen ty half <*> gen ty half
  ]
  -- Eliminators: reach the target type *through* a structured intermediate.
  -- These are what put the change-of-variables/dimension bookkeeping and the
  -- IRConformsTo structural checks in front of the invariant properties --
  -- building a tuple is easy, taking one apart is where the work is.
  ++ [ do other <- genTy 1
          tfst <$> gen (TyTuple ty other) half
     , do other <- genTy 1
          tsnd <$> gen (TyTuple other ty) half
     , lhead <$> gen (TyList ty) half
     ]
  -- Milestone M2: the 'let' surface. Two productions, because the shape that
  -- reaches the *interesting* engine is a narrow corner of the shape space and
  -- a generic 'let' lands in it far too rarely to rely on.
  ++ [ genPlainLet env ty n
     , genWitnessLet env ty n
     ]
  ++ tyRec
  where
    gen = genTypedExprIn env
    half = n `div` 2
    tyRec = case ty of
      TyAny -> []
      TyFloat ->
        [ (#+#) <$> gen TyFloat half <*> gen TyFloat half
        , (#-#) <$> gen TyFloat half <*> gen TyFloat half
        , (#*#) <$> gen TyFloat half <*> gen TyFloat half
        , negF <$> gen TyFloat (n - 1)
        , expF <$> gen TyFloat (n - 1)
        ]
      TyInt ->
        [ (#<+>#) <$> gen TyInt half <*> gen TyInt half
        , (#<->#) <$> gen TyInt half <*> gen TyInt half
        , negIF <$> gen TyInt (n - 1)
        ]
      TyBool ->
        [ (#&&#) <$> gen TyBool half <*> gen TyBool half
        , (#||#) <$> gen TyBool half <*> gen TyBool half
        , (#!#) <$> gen TyBool (n - 1)
        , (#>#) <$> gen TyFloat half <*> gen TyFloat half
        , (#<#) <$> gen TyFloat half <*> gen TyFloat half
        -- Structural tests: the only Bool-producing eliminators for lists and
        -- Either, and the reason those shapes get *observed* rather than just
        -- constructed and returned.
        , do a <- genTy 1
             isNull <$> gen (TyList a) half
        , do a <- genTy 1
             b <- genTy 1
             sisLeft <$> gen (TyEither a b) half
        , do a <- genTy 1
             b <- genTy 1
             sisRight <$> gen (TyEither a b) half
        ]
      TyTuple a b ->
        [ tuple <$> gen a half <*> gen b half ]
      TyEither a b ->
        [ left <$> gen a (n - 1)
        , right <$> gen b (n - 1)
        ]
      TyList a ->
        [ cons <$> gen a half <*> gen (TyList a) half
        , ltail <$> gen (TyList a) (n - 1)
        ]

-- | A binder name that cannot collide with anything in scope, with any
-- predefined function, or with the two distribution leaves. Scopes only ever
-- grow inwards, so the depth of the scope is a sufficient discriminator and
-- the generator never shadows. That is worth having: shadowing is legal but it
-- would make every counterexample harder to read for no extra coverage.
freshName :: TyEnv -> String
freshName env = "v" ++ show (length env)

-- | @let v = <anything> in <anything>@. The bound type is drawn independently
-- of the target, so this reaches the whole 'Apply'/'Lambda' path: shared
-- draws, point-invertible observations through forward chaining, and
-- structured bound values.
genPlainLet :: TyEnv -> Ty -> Int -> Gen Expr
genPlainLet env ty n = do
  bty <- genTy 1
  val <- genTypedExprIn env bty half
  let v = freshName env
  body <- genTypedExprIn ((v, bty) : env) ty half
  return (letIn v val body)
  where half = n `div` 2

-- | @let v = <continuous> in if <comparison mentioning v> then _ else _@ --
-- the set-valued-witness surface, generated on purpose.
--
-- This is the shape the design (Axis 1b) identifies as the one worth
-- generating: the observation reaches @v@ only through a comparison and an
-- @if@, so no occurrence is point-invertible and 'setWitnessApply' is the only
-- engine that can answer it. @let x = Normal in if x < 0.0 then 0.0 - x else
-- x@ -- the corpus' @letProbAbsNormal@, whose density is @2*phi(y)@ -- is
-- exactly a draw from this production.
--
-- The bound value is a bare distribution leaf rather than an expression: the
-- engine seeds its interval transport at a distribution it can take a CDF of,
-- and a compound right-hand side is the *refused* shape, not the interesting
-- one.
genWitnessLet :: TyEnv -> Ty -> Int -> Gen Expr
genWitnessLet env ty n = do
  let v = freshName env
      env' = (v, TyFloat) : env
  val  <- elements [normal, uniform]
  cond <- genComparisonOn (varE v) (min 2 half)
  t    <- genTypedExprIn env' ty half
  f    <- genTypedExprIn env' ty half
  return (letIn v val (ifThenElse cond t f))
  where half = n `div` 2

-- | A comparison of a monotone chain over @var@ against a float literal.
--
-- The literal matters: the set-witness engine turns a comparison into an
-- interval only when the other operand is a *deterministic* bound, and
-- 'toSeededMonotoneInvExpr' transports that interval down the chain using a
-- static direction certificate. Drawing a general expression for the bound
-- would mostly produce the refusal path instead of the engine.
genComparisonOn :: Expr -> Int -> Gen Expr
genComparisonOn bv n = do
  lhs <- genMonotoneChain bv n
  bound <- constF <$> choose (-3, 3)
  op <- elements [(#>#), (#<#)]
  return (op lhs bound)

-- | A chain of steps 'ForwardChaining.stepMonotonicity' knows the direction
-- of: @plus@ by a literal, @neg@, @exp@, and @mult@ by a non-zero literal
-- (whose direction is that literal's sign). Anything outside that table is a
-- refusal rather than a transport, so the chain is kept inside it.
genMonotoneChain :: Expr -> Int -> Gen Expr
genMonotoneChain bv n
  | n <= 0 = pure bv
  | otherwise = oneof
      [ pure bv
      , (\c -> bv #+# constF c) <$> choose (-3, 3)
      , (\c -> bv #*# constF c) <$> elements [-3, -2, -0.5, 0.5, 2, 3]
      , negF <$> genMonotoneChain bv (n - 1)
      , expF <$> genMonotoneChain bv (n - 1)
      ]

-- ---------------------------------------------------------------------------
-- Recognising a generated 'let'.

-- | How much of the 'let' surface a draw reaches. Ordered, so a whole-program
-- verdict is the maximum over its nodes.
data LetShape
  = NoLet
  | PlainLet     -- ^ some @let@, observed by whatever the body happens to be
  | WitnessLet   -- ^ 'genWitnessLet' shape: continuous binding, observed only
                 --   through an @if@ whose condition reads it
  deriving (Show, Eq, Ord)

-- | A *syntactic* classifier, not a report from the compiler: it says which
-- shape was generated, not which engine ran. It is nonetheless a usable proxy
-- for the latter, because 'WitnessLet' is by construction the shape forward
-- chaining cannot point-invert -- so a 'WitnessLet' draw that compiles to a
-- probability function got it from 'setWitnessApply' and from nowhere else.
letShapeOf :: Expr -> LetShape
letShapeOf e = maximum (here : map letShapeOf (children e))
  where
    here = case asLet e of
      Nothing -> NoLet
      Just (x, val, body)
        | isContinuousLeaf val, observedOnlyByCondition x body -> WitnessLet
        | otherwise -> PlainLet

-- | @let x = v in b@, as the 'Apply'/'Lambda' pair 'SPLL.Prelude.letIn' builds.
asLet :: Expr -> Maybe (String, Expr, Expr)
asLet e = case node e of
  Apply l val | Lambda x body <- node l -> Just (x, val, body)
  _ -> Nothing

isContinuousLeaf :: Expr -> Bool
isContinuousLeaf e = case node e of
  Var "Normal"  -> True
  Var "Uniform" -> True
  _             -> False

observedOnlyByCondition :: String -> Expr -> Bool
observedOnlyByCondition x body = case node body of
  IfThenElse c _ _ -> mentionsVar x c
  _                -> False

-- | Does @x@ occur free in this expression? Respects shadowing, even though
-- 'freshName' means the generator never produces any.
mentionsVar :: String -> Expr -> Bool
mentionsVar x e = case node e of
  Var y                  -> y == x
  Lambda y b | y == x    -> False
             | otherwise -> mentionsVar x b
  _                      -> any (mentionsVar x) (children e)

-- ---------------------------------------------------------------------------
-- Globally distinct binder names.

-- | Alpha-rename every binder in the expression to @v0@, @v1@, ... in
-- traversal order.
--
-- This is not cosmetic. 'SPLL.Validator' is stricter than lexical scoping about
-- names: it rejects shadowing outright ("Duplicate declaration of identifier"),
-- and it rejects an @Apply l v@ whose two sides declare any name in common
-- ("Identifiers [...] are possibly declared multiple times") -- which two
-- *sibling* @let@s in disjoint scopes do, even though nothing about them is
-- ambiguous. Naming a binder after its scope depth, which is what generation
-- does, therefore produces well-scoped programs the validator refuses.
--
-- Renaming after the fact rather than threading a counter through generation
-- keeps 'genTypedExprIn' a plain 'Gen' with no supply, and costs one pass.
uniquifyBinders :: Expr -> Expr
uniquifyBinders = uniquifyBindersFrom "v"

-- | 'uniquifyBinders' with a caller-chosen prefix, so two independently
-- generated expressions can be combined into one program without their binder
-- names colliding.
uniquifyBindersFrom :: String -> Expr -> Expr
uniquifyBindersFrom prefix e0 = fst (go 0 [] e0)
  where
    go :: Int -> [(String, String)] -> Expr -> (Expr, Int)
    go i sub e = case node e of
      Var x -> (rebuild (Var (fromMaybe x (lookup x sub))), i)
      Lambda x b ->
        let x' = prefix ++ show i
            (b', i') = go (i + 1) ((x, x') : sub) b
        in (rebuild (Lambda x' b'), i')
      Apply a b ->
        let (a', i')  = go i sub a
            (b', i'') = go i' sub b
        in (rebuild (Apply a' b'), i'')
      IfThenElse c t f ->
        let (c', i1) = go i sub c
            (t', i2) = go i1 sub t
            (f', i3) = go i2 sub f
        in (rebuild (IfThenElse c' t' f'), i3)
      InjF nm args ->
        let (args', i') = goMany i args
        in (rebuild (InjF nm args'), i')
      _ -> (e, i)
      where
        rebuild = Expr (ann e)
        goMany j []       = ([], j)
        goMany j (a : as) = let (a', j')   = go j sub a
                                (as', j'') = goMany j' as
                            in (a' : as', j'')

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
--
-- With M2's 'let' bindings it must also be *scope*-directed: a candidate that
-- is well-typed but leaves a variable unbound is not a shrink, it is a
-- different (and invalid) program. Hence the 'TyEnv' parameter, and the
-- "collapse to the body only if the binding is dead" rule below.

-- | The 'Ty' a 'genTypedExpr' output is guaranteed to have, recovered from the
-- node shape alone (the generator annotates every node with 'makeTypeInfo',
-- so the annotation carries nothing to read).
--
-- Total over the typed generator's output space and 'Nothing' outside it,
-- which is what makes 'shrinkTypedExpr' safe to apply to an arbitrary 'Expr':
-- an unrecognised node simply does not shrink, rather than shrinking to
-- something ill-typed.
tyOfTypedExpr :: Expr -> Maybe Ty
tyOfTypedExpr = tyOfTypedExprIn []

tyOfTypedExprIn :: TyEnv -> Expr -> Maybe Ty
tyOfTypedExprIn env e = case node e of
  Constant (VFloat _) -> Just TyFloat
  Constant (VInt _)   -> Just TyInt
  Constant (VBool _)  -> Just TyBool
  Var "Uniform"       -> Just TyFloat
  Var "Normal"        -> Just TyFloat
  Var x               -> lookup x env
  -- Both arms carry the node's type, and each may pin a different part of it
  -- (@if c then left x else right y@ is the canonical case), so the arms are
  -- joined rather than the first recognised one taken. A join failure means
  -- the node is outside the generator's output space.
  IfThenElse _ t f    -> case (tyOfTypedExprIn env t, tyOfTypedExprIn env f) of
    (Just a, Just b)  -> tyJoin a b
    (Just a, Nothing) -> Just a
    (Nothing, mb)     -> mb
  InjF (Named f) args -> tyOfTypedInjF env f args
  -- A 'let': the binding's recovered type extends the scope for the body, and
  -- the body's type is the node's. An 'Apply' of anything but a literal lambda
  -- is outside the generator's space and recovers nothing.
  Apply l val | Lambda x body <- node l ->
    tyOfTypedExprIn env val >>= \vty -> tyOfTypedExprIn ((x, vty) : env) body
  _                   -> Nothing

-- | Result type of an InjF application the typed generator can emit. The
-- structured entries are computed from the arguments rather than looked up:
-- @TCons@ is as wide as its components, the eliminators are as narrow as the
-- part of their argument's type they select, and @left@/@right@ pin only one
-- side of the Either they build (the other stays 'TyAny').
tyOfTypedInjF :: TyEnv -> String -> [Expr] -> Maybe Ty
tyOfTypedInjF env "TCons" [a, b] = TyTuple <$> ty a <*> ty b
  where ty = tyOfTypedExprIn env
tyOfTypedInjF env "fst"   [x]    = tyOfTypedExprIn env x >>= \t -> case t of
  TyTuple a _ -> Just a
  _           -> Nothing
tyOfTypedInjF env "snd"   [x]    = tyOfTypedExprIn env x >>= \t -> case t of
  TyTuple _ b -> Just b
  _           -> Nothing
-- The tail is deliberately not consulted: it may be the element-type-free
-- 'nul', and the head alone determines the list's element type.
tyOfTypedInjF env "Cons"  [h, _] = TyList <$> tyOfTypedExprIn env h
tyOfTypedInjF env "head"  [x]    = tyOfTypedExprIn env x >>= \t -> case t of
  TyList a -> Just a
  _        -> Nothing
tyOfTypedInjF env "tail"  [x]    = tyOfTypedExprIn env x >>= \t -> case t of
  TyList a -> Just (TyList a)
  _        -> Nothing
tyOfTypedInjF env "left"  [x]    = (`TyEither` TyAny) <$> tyOfTypedExprIn env x
tyOfTypedInjF env "right" [x]    = TyEither TyAny <$> tyOfTypedExprIn env x
tyOfTypedInjF _   f       _      = lookup f typedInjFResultTy

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

-- | @tyGeneralizes general specific@: is @general@ at least as general as
-- @specific@? That is, does it agree with it at every position @general@ pins
-- down, leaving free ('TyAny') only positions @specific@ may also have pinned?
--
-- This, and not equality, is the shrinker's type-preservation test, because
-- recovery is partial: a @left x@ node fixes only the left component of its
-- Either, so replacing a node whose type was pinned by *both* arms of an
-- enclosing @if@ with a single-arm leaf is well-typed and strictly more
-- general.
--
-- It is deliberately *not* 'tyJoin'-compatibility, which was the original M-S
-- test and is too weak in both directions. A join succeeds whenever no
-- position actively disagrees, so 'TyAny' on the *node's* side absorbs an
-- unrelated type on the replacement's: @left (right e)@ recovers as
-- @Either (Either ? B) ?@ and its argument @right e@ as @Either ? B@, which
-- join happily -- and the resulting "shrink" strips a constructor, changing
-- the expression's type and breaking recovery somewhere further out. The
-- asymmetric test refuses that, and refuses the mirror-image error of
-- committing a position the context left free.
tyGeneralizes :: Ty -> Ty -> Bool
tyGeneralizes TyAny _ = True
tyGeneralizes (TyTuple a b)  (TyTuple c d)  = tyGeneralizes a c && tyGeneralizes b d
tyGeneralizes (TyEither a b) (TyEither c d) = tyGeneralizes a c && tyGeneralizes b d
tyGeneralizes (TyList a)     (TyList b)     = tyGeneralizes a b
tyGeneralizes a b = a == b

-- | Node count. Used both as the shrinker's well-foundedness measure and by
-- the coverage instrumentation in TestFuzz.
typedExprSize :: Expr -> Int
typedExprSize e = 1 + sum (map typedExprSize (children e))

-- | Longest root-to-leaf path, counting the root as depth 1.
typedExprDepth :: Expr -> Int
typedExprDepth e = case children e of
  [] -> 1
  cs -> 1 + maximum (map typedExprDepth cs)

-- | The sub-expressions of a node the typed generator can produce. 'Apply' and
-- 'Lambda' are here for M2's 'let': a @let@ is two nodes plus its two
-- children, which is what makes "collapse the let" a strict size reduction.
children :: Expr -> [Expr]
children e = case node e of
  IfThenElse c t f -> [c, t, f]
  InjF _ args      -> args
  Apply a b        -> [a, b]
  Lambda _ b       -> [b]
  _                -> []

-- | The smallest inhabitants of a 'Ty' -- the shrinker's workhorse reduction,
-- "replace any subexpression with a type-correct leaf". Constants only: a
-- distribution leaf ('normal'/'uniform') is the same size but strictly more
-- interesting, so offering it as a shrink target would let the shrinker walk
-- sideways forever.
--
-- Every leaf here is *closed*, which is also what keeps the shrinker
-- scope-safe: replacing an arbitrary subexpression with one of these can never
-- strand a reference to a binding the replacement is no longer under.
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
-- Every candidate has a 'tyCompatible' 'Ty' and a strictly smaller node count,
-- so the result is well-founded and never hands the property an ill-typed or
-- ill-scoped program (either of which would be discarded, minimizing nothing).
shrinkTypedExpr :: Expr -> [Expr]
shrinkTypedExpr = shrinkTypedExprIn []

shrinkTypedExprIn :: TyEnv -> Expr -> [Expr]
shrinkTypedExprIn env e = case tyOfTypedExprIn env e of
  Nothing -> []
  Just ty -> nub (filter smaller (typedLeaves ty ++ collapses env ty e ++ childShrinks env e))
  where
    smaller c = typedExprSize c < typedExprSize e

-- | Replace the node by one of its own same-typed subexpressions: either
-- branch of an 'IfThenElse' (both share the node's type), a type-matching
-- argument of an InjF/comparison (@neg x@ and @x + y@ shrink to @x@; @x > y@
-- does not, its arguments being Float where it is Bool), or -- for a @let@ --
-- the bound value or the body.
--
-- The body is only offered when the binding is *dead*. @let x = e in b@ with
-- @x@ free in @b@ has no well-scoped reduction to @b@, and offering one anyway
-- would replace a counterexample with an invalid program rather than a
-- smaller one.
collapses :: TyEnv -> Ty -> Expr -> [Expr]
collapses env ty e = filter compatible $ case asLet e of
  Just (x, val, body) -> [val] ++ [ body | not (mentionsVar x body) ]
  Nothing -> case node e of
    IfThenElse _ t f -> [t, f]
    InjF _ args      -> args
    _                -> []
  where
    -- Judged in the *outer* scope: a candidate that only type-checks under the
    -- binding being removed is not a candidate at all. And judged
    -- asymmetrically -- the replacement must be at least as general as the
    -- node it replaces, never merely joinable with it.
    compatible c = maybe False (`tyGeneralizes` ty) (tyOfTypedExprIn env c)

-- | Shrink one child at a time, keeping the node and every sibling. This is
-- what actually minimizes a deep program: the collapses above cut whole
-- subtrees, this reduces the ones that have to stay.
childShrinks :: TyEnv -> Expr -> [Expr]
childShrinks env e = case asLet e of
  Just (x, val, body) ->
    -- The bound value is shrunk in the outer scope, the body under the
    -- binding. A shrunk value may have a strictly more general recovered type
    -- (that is the shrinker's standing contract), and the body is re-typed
    -- against it here, which is why the env carries the *recovered* type
    -- rather than the one generation chose.
    [ mkLet x val' body | val' <- shrinkTypedExprIn env val ]
    ++ case tyOfTypedExprIn env val of
         Nothing  -> []
         Just vty -> [ mkLet x val body' | body' <- shrinkTypedExprIn ((x, vty) : env) body ]
  Nothing -> case node e of
    IfThenElse c t f ->
      [ rebuild (IfThenElse c' t f) | c' <- shrinkTypedExprIn env c ]
      ++ [ rebuild (IfThenElse c t' f) | t' <- shrinkTypedExprIn env t ]
      ++ [ rebuild (IfThenElse c t f') | f' <- shrinkTypedExprIn env f ]
    InjF name args ->
      [ rebuild (InjF name args') | args' <- shrinkOne (shrinkTypedExprIn env) args ]
    _ -> []
  where
    rebuild = Expr (ann e)
    mkLet x val' body' = letIn x val' body'

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
