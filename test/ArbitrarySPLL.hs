{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- The Arbitrary instances for Program/Expr/Value/TypeInfo are orphans by
-- design: they are test-suite fixtures, and the only way to un-orphan them
-- would be to declare them in SPLL.Lang.*, which would put a QuickCheck
-- dependency on the library itself.
{-# OPTIONS_GHC -Wno-orphans #-}

module ArbitrarySPLL (
  genExpr
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
, tyToRType
, rTypeToTy
, tyAllDiscrete
, genNeuralProgram
, genNeuralTwinProgram
, neuralTwin
, typedMainCoreExpr
, typedMainCoreTy
, hasNeural
, uniquifyBinders
, uniquifyBindersFrom
, InjFSig(..)
, injFCatalog
, injFCatalogFor
, injFExcluded
, InjFExclusion(..)
, injFNamesOf
, injFLeafApp
)where

import Test.QuickCheck
import Data.List (nub, find)
import Data.Maybe (fromMaybe)

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Parser (reserved)
import PredefinedFunctions (globalFEnv, parameterCount, FPair(..), FDecl, contract, applicability)
import SPLL.IntermediateRepresentation (IRExpr(..))
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

-- | A well-typed "main" program of a randomly chosen type.
--
-- Most draws are nullary. One in five (milestone M3) instead declares a neural
-- network and reads it: @main sym = let s = nn sym in \<observations of s\>@.
-- Those draws are the only way the plan-guided enumeration engine is reached
-- at all, and they cost the properties nothing extra -- the same eight
-- invariants apply unchanged. See 'genNeuralProgram'.
--
-- A neural draw's @main@ takes an argument, so a caller running it has to
-- supply a mock-network symbol rather than the empty argument list every other
-- draw wants. TestFuzz's @fuzzArgs@ derives that from the program.
genTypedProgram :: Gen Program
genTypedProgram = frequency [(4, genPlainProgram), (1, genNeuralProgram)]

-- | The nullary shape: @main = \<expr\>@, with no neural declaration.
genPlainProgram :: Gen Program
genPlainProgram = do
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
    -- Scalar InjF applications are drawn from 'injFCatalog', which is derived
    -- from the compiler's own 'globalFEnv' (Axis 1). The hand-written
    -- per-type table this replaced had drifted: it never emitted @double@,
    -- @sq@, @recip@ or @max@, never compared Ints, and never used @eq@ at
    -- all, none of which was a decision anyone took. (@recip@ is out again
    -- since, deliberately this time: its forward declaration was corrected to
    -- state the @a \/= 0@ domain it always had, so 'injFUnconditional' now
    -- excludes it -- the derivation working as designed.)
    catalogProds t = [ injF (injFName sig) <$> mapM argAt (injFArgs sig)
                     | sig <- injFCatalogFor t
                     , let arity = length (injFArgs sig)
                     , let argAt a = gen a (if arity <= 1 then n - 1 else n `div` arity)
                     ]
    tyRec = case ty of
      TyAny -> []
      -- The subtraction sugars stay explicit alongside the catalog: @a - b@ is
      -- @plus a (neg b)@, a *composite* shape the catalog cannot name, and the
      -- realized nesting is the point of having it.
      TyFloat ->
        catalogProds TyFloat ++
        [ (#-#) <$> gen TyFloat half <*> gen TyFloat half ]
      TyInt ->
        catalogProds TyInt ++
        [ (#<->#) <$> gen TyInt half <*> gen TyInt half ]
      TyBool ->
        catalogProds TyBool ++
        -- Structural tests: the only Bool-producing eliminators for lists and
        -- Either, and the reason those shapes get *observed* rather than just
        -- constructed and returned.
        [ do a <- genTy 1
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
      -- The symbol a milestone-M3 neural read is applied to is a 'Var' under
      -- the generated @main@'s own lambda, so it has to be renamed with it.
      -- Without this case the read keeps referring to the pre-rename name and
      -- the validator rejects the draw outright.
      ReadNN nm arg ->
        let (arg', i') = go i sub arg
        in (rebuild (ReadNN nm arg'), i')
      _ -> (e, i)
      where
        rebuild = Expr (ann e)
        goMany j []       = ([], j)
        goMany j (a : as) = let (a', j')   = go j sub a
                                (as', j'') = goMany j' as
                            in (a' : as', j'')

-- ---------------------------------------------------------------------------
-- Milestone M3: neural declarations and the plan-guided enumeration surface.
--
-- Design: typed-program-generator-expansion, Axis 1b (second half).
--
-- The engine with the least generated coverage is plan-guided lazy
-- enumeration: it is reached only through a @ReadNN@ whose result is observed,
-- and nothing in the scalar/structured/let generator can emit one. The shape
-- this produces is the corpus' @planEnum*@ shape,
--
--   neural nn :: (Symbol -> T)          -- optionally `of <MultiValue>`
--   main sym = let s = nn sym in if <observation of s> then _ else _
--
-- which is three separate pieces of machinery the earlier milestones lack: a
-- declaration generator, a target-type lattice narrower than 'Ty' (not every
-- type has a partition plan), and an observation generator that actually
-- *reads* the network rather than binding it and dropping it.
--
-- The `of` clause is what makes this milestone's second oracle free. A neural
-- declaration with an `of` clause over a purely discrete target gets a
-- 'DiscreteValues' tag (SPLL.Analysis.annotateEnumsProg), so it compiles by
-- materializing the whole support into an @IREnumSum@; without one it compiles
-- through the lazy plan-backed path. The two must agree to the last bit, which
-- is exactly what the corpus' hand-written @planEnumRec*@/@*Materialized@ file
-- pairs pin -- and here it comes without writing a second program.

-- | How a generated neural declaration is annotated, and hence which
-- compilation path its reads take.
data NeuralAnn
  = AnnAuto      -- ^ No @of@ clause: the lazy, plan-backed path.
  | AnnAutoOf    -- ^ @of _@ over a discrete target: the materializing twin.
  | AnnInts Int  -- ^ @of [0 .. k-1]@ on an @Int@ target: a k-way categorical.
  deriving (Show, Eq)

-- | The 'RType' a generated 'Ty' denotes. Total, because every 'Ty' the
-- generator targets is representable; 'TyAny' is never a generation target and
-- maps to 'TFloat' only so this stays a function.
tyToRType :: Ty -> RType
tyToRType TyFloat        = TFloat
tyToRType TyInt          = TInt
tyToRType TyBool         = TBool
tyToRType TyAny          = TFloat
tyToRType (TyTuple a b)  = Tuple (tyToRType a) (tyToRType b)
tyToRType (TyEither a b) = TEither (tyToRType a) (tyToRType b)
tyToRType (TyList a)     = ListOf (tyToRType a)

-- | Partial inverse of 'tyToRType', for reading a neural declaration's target
-- back out of a 'Program'. 'Nothing' for anything the typed generator cannot
-- build inhabitants of.
rTypeToTy :: RType -> Maybe Ty
rTypeToTy TFloat        = Just TyFloat
rTypeToTy TInt          = Just TyInt
rTypeToTy TBool         = Just TyBool
rTypeToTy (Tuple a b)   = TyTuple  <$> rTypeToTy a <*> rTypeToTy b
rTypeToTy (TEither a b) = TyEither <$> rTypeToTy a <*> rTypeToTy b
rTypeToTy (ListOf a)    = TyList   <$> rTypeToTy a
rTypeToTy _             = Nothing

-- | Does this type's partition plan consist of discrete slots only? Only then
-- does an @of@ clause change anything: 'SPLL.Analysis.annotateEnumsProg'
-- declines to tag a 'MultiValue' with a continuous leaf, because enumerating
-- it would sum over the discrete residue and silently drop the continuous
-- mass. A @Float@ anywhere in the target therefore makes @of _@ a no-op, and
-- the materialized-twin oracle vacuous.
tyAllDiscrete :: Ty -> Bool
tyAllDiscrete TyBool         = True
tyAllDiscrete (TyTuple a b)  = tyAllDiscrete a && tyAllDiscrete b
tyAllDiscrete (TyEither a b) = tyAllDiscrete a && tyAllDiscrete b
tyAllDiscrete _              = False

-- | Target types 'SPLL.Lang.Lang.autoDeriveMultiValue' can produce a plan for
-- with no annotation: @Float@ (one continuous slot), @Bool@ (a two-way
-- discrete), and tuples\/Eithers of those. Not @Int@ (unbounded domain, needs
-- explicit values), not lists, not ADTs -- ADT targets are milestone M4.
--
-- Depth-bounded hard: every leaf costs logits (2 for a continuous slot, 2 for
-- a Bool, plus a selector per Either), and the mock network has to produce a
-- vector of exactly the plan's width on every single draw.
genAutoNeuralTy :: Int -> Gen Ty
genAutoNeuralTy n
  | n <= 0 = elements [TyFloat, TyBool]
  | otherwise = frequency
      [ (5, elements [TyFloat, TyBool])
      , (2, TyTuple  <$> rec <*> rec)
      , (1, TyEither <$> rec <*> rec)
      ]
  where rec = genAutoNeuralTy (n - 1)

-- | 'genAutoNeuralTy' restricted to 'tyAllDiscrete' targets, for the draws
-- whose @of@ clause is supposed to *do* something.
genDiscreteNeuralTy :: Int -> Gen Ty
genDiscreteNeuralTy n
  | n <= 0 = pure TyBool
  | otherwise = frequency
      [ (4, pure TyBool)
      , (2, TyTuple  <$> rec <*> rec)
      , (1, TyEither <$> rec <*> rec)
      ]
  where rec = genDiscreteNeuralTy (n - 1)

-- | Depth budget for a neural target type. One less than 'tyDepth': the plan
-- width grows with the leaf count, and every draw pays it in mock logits.
neuralTyDepth :: Int
neuralTyDepth = 2

-- | A neural declaration plus the 'Ty' of its target, so callers do not have
-- to invert 'tyToRType' to find out what they generated.
--
-- Three flavours, because they reach different parts of the plan machinery:
-- 'AnnAuto' is the lazy path over anything auto-derivable (continuous slots
-- included), 'AnnAutoOf' the materializing path over a discrete target, and
-- 'AnnInts' the k-way categorical that @Bool@ alone cannot produce -- without
-- ADTs (M4), an explicit @of [0,1,..]@ on an @Int@ target is the only way to
-- get a plan slot wider than two.
genTypedNeuralDecl :: Gen (NeuralDecl, Ty)
genTypedNeuralDecl = do
  (annot, nty) <- frequency
    [ (3, (,) AnnAuto   <$> genAutoNeuralTy neuralTyDepth)
    , (2, (,) AnnAutoOf <$> genDiscreteNeuralTy neuralTyDepth)
    , (2, do k <- choose (2, 4)
             return (AnnInts k, TyInt))
    ]
  return ((neuralName, TArrow TSymbol (tyToRType nty), annMultiValue annot), nty)

annMultiValue :: NeuralAnn -> Maybe MultiValue
annMultiValue AnnAuto     = Nothing
annMultiValue AnnAutoOf   = Just MultiAuto
annMultiValue (AnnInts k) = Just (MultiDiscretes (map VInt [0 .. fromIntegral k - 1]))

-- | The one declared network's name. Fixed rather than generated: a second
-- network would multiply the plan width without reaching any shape one does
-- not, and a fixed name keeps counterexamples readable.
neuralName :: String
neuralName = "nn"

-- | The symbol parameter of a neural @main@. Renamed by 'uniquifyBinders'
-- before the program is handed out, like every other binder.
neuralSymName :: String
neuralSymName = "sym"

-- | @main sym = let s = nn sym in \<core\>@ with a matching declaration.
genNeuralProgram :: Gen Program
genNeuralProgram = do
  (decl, nty) <- genTypedNeuralDecl
  ty <- genTy tyDepth
  body <- sized (genNeuralMain nty ty)
  return $ Program [("main", body)] [decl] [] []

-- | The body of a neural @main@, at a given network target type and program
-- result type.
genNeuralMain :: Ty -> Ty -> Int -> Gen Expr
genNeuralMain nty ty n = do
  let s    = "s"
      env  = [(s, nty)]
  core <- genNeuralCore env s nty ty n
  return $ uniquifyBinders
         $ neuralSymName #-># letIn s (readNN neuralName (varE neuralSymName)) core

-- | The body under the neural binding.
--
-- Usually an explicit observation at the top, for the same reason
-- 'genWitnessLet' forces its @if@: a @let@ whose bound variable is never
-- *read* reaches none of the machinery the milestone exists to exercise, and
-- relying on 'genTypedLeafIn' to pick the variable up by chance does not work
-- once the network's type is structured (the eliminator productions draw the
-- other tuple component at random, so they rarely line up with it).
--
-- The remaining quarter is left to the ordinary generator, which does still
-- reach @s@ when its type is scalar, and otherwise produces the
-- bound-but-unobserved shape -- a legitimate program the generate path has to
-- handle, and the control case for the observed one.
genNeuralCore :: TyEnv -> String -> Ty -> Ty -> Int -> Gen Expr
genNeuralCore env s nty ty n = frequency
  [ (3, do obs <- genNeuralObs (varE s) nty
           t <- genTypedExprIn env ty half
           f <- genTypedExprIn env ty half
           return (ifThenElse obs t f))
  , (1, genTypedExprIn env ty n)
  ]
  where half = n `div` 2

-- | A Bool-valued observation of a neural read: project the value down to one
-- plan leaf and test that leaf.
--
-- This is what puts a *condition* in front of the enumeration engine, which is
-- the whole point -- a plan slot that is merely returned is never enumerated
-- over. The projections are limited to the eliminators the typed generator
-- already emits (and hence that 'tyOfTypedExpr' already recovers through):
-- @fst@\/@snd@ descend into a tuple, and an @Either@ is tested for which side
-- it is, there being no @fromLeft@\/@fromRight@ production to descend with.
genNeuralObs :: Expr -> Ty -> Gen Expr
genNeuralObs e TyBool = oneof
  [ pure e
  , pure ((#!#) e)
  , (e #==#) . constB <$> arbitrary
  ]
genNeuralObs e TyFloat = do
  op <- elements [(#>#), (#<#)]
  c  <- choose (-2, 2)
  return (op e (constF c))
-- The comparison value is drawn a little wider than the widest `of` clause
-- 'genTypedNeuralDecl' emits, so some draws test a value outside the declared
-- support. That branch is unreachable, which is a shape the engine has to get
-- right (zero mass, not a crash), not a malformed draw.
genNeuralObs e TyInt = (e #==#) . constI <$> choose (0, 4)
genNeuralObs e (TyTuple a b) = oneof
  [ genNeuralObs (tfst e) a
  , genNeuralObs (tsnd e) b
  ]
genNeuralObs e (TyEither _ _) = elements [sisLeft e, sisRight e]
-- Neither is a neural target type ('genAutoNeuralTy' emits neither, and an
-- Int target is always a bare leaf), so these exist only to keep the function
-- total.
genNeuralObs e (TyList _) = pure (isNull e)
genNeuralObs _ TyAny      = constB <$> arbitrary

-- | Does this program declare a neural network?
hasNeural :: Program -> Bool
hasNeural = not . null . neurals

-- | The part of @main@ the typed generator is responsible for, and the scope
-- it sits in.
--
-- For a plain draw that is the whole body in the empty scope. For a neural
-- draw the body is wrapped in a lambda and a @let@ whose bound value is a
-- 'ReadNN' -- neither of which 'tyOfTypedExpr' can recover a type for, the
-- network's target type living in the 'Program' rather than on the node. Every
-- consumer of the generator's output (the shrinker, and TestFuzz's coverage
-- axes) therefore goes through here rather than reading @main@ directly, or a
-- neural draw would report as unrecognised and silently stop shrinking.
typedMainCore :: Program -> Maybe (TyEnv, Expr)
typedMainCore p = fst <$> typedMainParts p

-- | The generated core of @main@, for consumers that only want the expression.
typedMainCoreExpr :: Program -> Maybe Expr
typedMainCoreExpr p = snd <$> typedMainCore p

-- | The 'Ty' of the generated core of @main@, recovered in the scope the core
-- actually sits in -- which for a neural draw is non-empty.
typedMainCoreTy :: Program -> Maybe Ty
typedMainCoreTy p = typedMainCore p >>= \(env, core) -> tyOfTypedExprIn env core

-- | 'typedMainCore' plus the rebuilder that puts a replacement core back
-- inside whatever wrapper it came out of.
typedMainParts :: Program -> Maybe ((TyEnv, Expr), Expr -> Expr)
typedMainParts p = do
  body <- lookup "main" (functions p)
  case node body of
    Lambda sym inner
      | Just (s, val, core) <- asLet inner
      , ReadNN nn _ <- node val
      , Just (_, nrt, _) <- find ((== nn) . fst3) (neurals p)
      , Just nty <- rTypeToTy (neuralTarget nrt)
      -> Just ( ((s, nty) : [], core)
              , \core' -> Expr (ann body) (Lambda sym (letIn s val core')) )
    _ -> Just (([], body), id)
  where
    fst3 (a, _, _) = a
    neuralTarget (TArrow _ t) = t
    neuralTarget t            = t

-- | The same program with its neural declaration's @of@ clause flipped on or
-- off -- the materializing twin of a lazy draw, or the reverse.
--
-- 'Nothing' unless the flip actually changes the compilation path: exactly one
-- declaration, its target auto-derivable *and* free of continuous slots, and
-- its annotation either absent or @of _@. An explicit value list
-- ('AnnInts') is left alone -- its target does not auto-derive, so there is no
-- annotation-free twin to compare it against.
neuralTwin :: Program -> Maybe Program
neuralTwin p = case neurals p of
  [(n, rt@(TArrow TSymbol target), annot)]
    | Just nty <- rTypeToTy target
    , tyAllDiscrete nty
    , Just annot' <- flipAnn annot
    -> Just p { neurals = [(n, rt, annot')] }
  _ -> Nothing
  where
    flipAnn Nothing          = Just (Just MultiAuto)
    flipAnn (Just MultiAuto) = Just Nothing
    flipAnn _                = Nothing

-- | A lazily-compiled neural draw and its materializing twin, for the
-- differential oracle. Both sides are the same program up to the @of@ clause,
-- so any disagreement in the answers is a disagreement between the two
-- engines and nothing else.
genNeuralTwinProgram :: Gen (Program, Program)
genNeuralTwinProgram = do
  nty <- genDiscreteNeuralTy neuralTyDepth
  ty  <- genTy tyDepth
  body <- sized (genNeuralMain nty ty)
  let decl = (neuralName, TArrow TSymbol (tyToRType nty), Nothing)
      lazyP = Program [("main", body)] [decl] [] []
  case neuralTwin lazyP of
    Just materialized -> return (lazyP, materialized)
    -- Unreachable: the target came from 'genDiscreteNeuralTy'. Fall back to
    -- the identical pair rather than failing the generator, so a future change
    -- to the lattice degrades the oracle instead of breaking the run.
    Nothing -> return (lazyP, lazyP)

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
-- The structural predicates. Their result is 'TyBool' whatever they test, but
-- they are *not* catalog entries -- the catalog is the scalar fragment, and
-- these take a container. Recovering them here rather than letting them fall
-- through matters more than it looks: an unrecognised node yields no shrinks,
-- so omitting these would silently stop minimization on every draw whose
-- condition happens to be a structural test, with nothing going red to say so.
tyOfTypedInjF env "isNull" [x]   = tyOfTypedExprIn env x >>= \t -> case t of
  TyList _ -> Just TyBool
  TyAny    -> Just TyBool
  _        -> Nothing
tyOfTypedInjF env "isLeft" [x]   = tyOfTypedEitherTest env x
tyOfTypedInjF env "isRight" [x]  = tyOfTypedEitherTest env x
-- Everything else is a scalar application, and its result type is whatever
-- the catalog entry matching the *recovered argument types* produces. This is
-- the same table 'genTypedRec' generates from, read backwards -- which is what
-- keeps a polymorphic InjF shrinkable: 'plus' has no single result type, and
-- the monomorphic table this replaced could only ever have claimed one of
-- them.
--
-- A recovered 'TyAny' argument (a position no node commits) matches any
-- catalog argument, so recovery stays as total as it was; an ambiguous match
-- yields 'Nothing' rather than a guess, because a wrong type here is a
-- type-changing "shrink", which M2 established is worse than no shrink.
tyOfTypedInjF env f args = do
  argTys <- mapM (tyOfTypedExprIn env) args
  case nub [ injFResult s
           | s <- injFCatalog
           , injFName s == f
           , length (injFArgs s) == length argTys
           , and (zipWith argMatches (injFArgs s) argTys) ] of
    [t] -> Just t
    _   -> Nothing
  where argMatches want got = got == TyAny || want == got

-- | @isLeft@/@isRight@ recover to 'TyBool' exactly when their argument is an
-- 'Either' (or an as-yet-uncommitted position).
tyOfTypedEitherTest :: TyEnv -> Expr -> Maybe Ty
tyOfTypedEitherTest env x = tyOfTypedExprIn env x >>= \t -> case t of
  TyEither _ _ -> Just TyBool
  TyAny        -> Just TyBool
  _            -> Nothing

-- | Every InjF name appearing anywhere in an expression. Used by the
-- @InjF catalog@ group to check that the generator never emits a name the
-- compiler does not define -- the failure a derived catalog is supposed to
-- make impossible, pinned rather than assumed.
injFNamesOf :: Expr -> [String]
injFNamesOf e =
  [ n | InjF (Named n) _ <- [node e] ] ++ concatMap injFNamesOf (children e)

-- | A catalog entry applied to the smallest inhabitant of each argument type.
-- This is the generation table and the recovery table meeting in the middle:
-- if 'tyOfTypedExpr' disagrees with 'injFResult' here, the shrinker has
-- quietly stopped working on every draw using that entry.
injFLeafApp :: InjFSig -> Maybe Expr
injFLeafApp sig = injF (injFName sig) <$> mapM leafOf (injFArgs sig)
  where leafOf t = case typedLeaves t of
                     (l:_) -> Just l
                     []    -> Nothing

-- ---------------------------------------------------------------------------
-- The InjF catalog: predefined-function productions derived from 'globalFEnv'.
--
-- Design: typed-program-generator-expansion, Axis 1 -- "InjF applications must
-- draw arity and argument types from 'globalFEnv'/'FDecl' rather than being
-- hard-coded, so the table stays correct as predefined functions change."
-- Milestone M1 deferred this and extended the hand-written table instead; this
-- is the deferred half.
--
-- Why it matters is rot, not breadth. A hand-maintained per-type table is a
-- second copy of 'globalFEnv' with no mechanism keeping the two in step: a
-- predefined function added to the compiler is simply never generated, and
-- nothing goes red to say so. Deriving the productions removes the copy, and
-- 'injFExcluded' makes the *deliberate* omissions a stated, testable list
-- rather than the residue of what nobody got round to adding.
--
-- The catalog covers the first-order scalar fragment only. Everything with a
-- container in its signature ('Cons', 'head', 'fst', 'left', 'isNull', ...)
-- already has a dedicated production in 'genTypedRec', because building and
-- eliminating structure needs the target type to drive the *shape*, not just
-- the argument list -- see 'InjFNotScalar'.

-- | One concrete scalar instantiation of a predefined function: the argument
-- types it is applied at and the type it produces. A polymorphic declaration
-- contributes one entry per instantiation ('plus' appears at both Float and
-- Int), which is precisely the coverage a monomorphic table silently lost.
data InjFSig = InjFSig
  { injFName   :: String
  , injFArgs   :: [Ty]
  , injFResult :: Ty
  } deriving (Show, Eq)

-- | Why a name in 'globalFEnv' has no catalog entry. Every exclusion is
-- derived from the declaration, never from a list of names, so it stays true
-- as 'PredefinedFunctions' changes.
data InjFExclusion
  = InjFGuarded     -- ^ the forward direction carries an applicability test
  | InjFNotScalar   -- ^ a container or function appears in the signature
  | InjFPolyArity   -- ^ more than one type variable; no instantiation rule
  deriving (Show, Eq, Ord)

-- | Does this forward direction *claim* to be total on its argument types?
-- @applicability@ is the declaration's own statement about its domain, and
-- @IRConst (VBool True)@ is how it says "always"
-- (api/src/PredefinedFunctions.md).
--
-- That claim is the safety condition for *generating* an application. @log@
-- and @sqrt@ are defined only on the positive reals, and a generator that
-- emitted @log <any Float>@ would manufacture NaN densities at a rate that
-- says nothing about the compiler. Reading the guard off the declaration keeps
-- that judgment in one place: a predefined function that later gains an
-- applicability test drops out of the catalog automatically, and one that
-- loses a spurious test is picked up.
--
-- What it is *not* is a proof of totality. The catalog is exactly as honest as
-- the declarations it reads, and a declaration that understates its domain
-- admits a partial function silently. @recip@ did precisely that -- body
-- @1\/a@, applicability @True@, while its own inverse carried a @b \/= 0@
-- guard -- and was generated for eight shifts, with @typedLeaves TyFloat =
-- [constF 0]@ making @recip 0@ the shrinker's preferred minimum. The repair
-- for that class belongs in 'PredefinedFunctions' (state the domain), not in a
-- name-based exclusion here, so that this derivation stays the single place
-- the judgment is made.
injFUnconditional :: FDecl -> Bool
injFUnconditional d = applicability d == IRConst (VBool True)

-- | Flatten an arrow chain into (arguments, result).
arrowParts :: RType -> ([RType], RType)
arrowParts (TArrow a b) = let (as, r) = arrowParts b in (a:as, r)
arrowParts t            = ([], t)

-- | The scalar types a type variable may be instantiated at, given its class
-- constraints. 'CNum' rules out Bool; an unconstrained variable (@eq@) admits
-- all three. Only the constraints that actually occur in 'globalFEnv' are
-- handled -- an unrecognised one yields no instantiations rather than a wrong
-- one, so the name drops out of the catalog instead of being generated at a
-- type it does not support.
tyVarInstances :: [ClassConstraint] -> [Ty]
tyVarInstances cs
  | any isNum cs      = [TyFloat, TyInt]
  | any isDiscrete cs = [TyInt, TyBool]
  | any unhandled cs  = []
  | otherwise         = [TyFloat, TyInt, TyBool]
  where
    isNum      (CNum _)        = True
    isNum      _               = False
    isDiscrete (CDiscrete _)   = True
    isDiscrete _               = False
    unhandled  (CFractional _) = True
    unhandled  _               = False

-- | Every concrete scalar signature a declaration's contract admits, or the
-- reason it admits none.
injFSigsOf :: String -> FDecl -> Either InjFExclusion [InjFSig]
injFSigsOf name d
  | not (injFUnconditional d) = Left InjFGuarded
  | otherwise = case tvs of
      []   -> scalarSig []
      [tv] -> case concatMap (\t -> either (const []) id (scalarSig [(tv, t)]))
                             (tyVarInstances cs) of
                [] -> Left InjFNotScalar
                ss -> Right ss
      _    -> Left InjFPolyArity
  where
    Forall tvs cs body = contract d
    scalarSig subst =
      let (as, r) = arrowParts (substRType subst body)
      in case (mapM rTypeToTy as, rTypeToTy r) of
           (Just argTys, Just resTy)
             -- Scalar in *every* position, not merely convertible. A
             -- container anywhere means the target type has to drive the
             -- shape rather than just the argument list -- @Cons@ needs an
             -- element type, @head@ needs a list to eliminate -- and
             -- 'genTypedRec' already owns those productions, drawing the
             -- element type from 'genTy' rather than from the three scalars.
             -- Admitting them here would double-cover them and narrow them at
             -- the same time.
             | not (null argTys)
             , all isScalarTy argTys
             , isScalarTy resTy -> Right [InjFSig name argTys resTy]
           _ -> Left InjFNotScalar

-- | The three types with no internal structure.
isScalarTy :: Ty -> Bool
isScalarTy TyFloat = True
isScalarTy TyInt   = True
isScalarTy TyBool  = True
isScalarTy _       = False

-- | Substitute concrete scalar types for type variables in a contract.
substRType :: [(TVarR, Ty)] -> RType -> RType
substRType sub (TVarR v)    = maybe (TVarR v) tyToRType (lookup v sub)
substRType sub (TArrow a b) = TArrow (substRType sub a) (substRType sub b)
substRType sub (Tuple a b)  = Tuple (substRType sub a) (substRType sub b)
substRType sub (TEither a b)= TEither (substRType sub a) (substRType sub b)
substRType sub (ListOf a)   = ListOf (substRType sub a)
substRType _   t            = t

-- | Every scalar InjF application the typed generator may emit, derived from
-- the compiler's own function environment. Called with no ADTs: user ADT
-- constructors enter 'globalFEnv' per declaration, and the typed generator
-- declares none (that is milestone M4).
injFCatalog :: [InjFSig]
injFCatalog =
  [ sig
  | (name, FPair fwd _) <- globalFEnv []
  , sig <- either (const []) id (injFSigsOf name fwd)
  ]

-- | The names 'globalFEnv' offers that the catalog deliberately does not, each
-- with the reason read off its declaration. Pinned by the @InjF catalog@ test
-- group: adding a predefined function moves it into one of these buckets or
-- into the catalog, and either way the pinned partition changes and goes red
-- until someone has decided which it should be.
injFExcluded :: [(String, InjFExclusion)]
injFExcluded =
  [ (name, why)
  | (name, FPair fwd _) <- globalFEnv []
  , Left why <- [injFSigsOf name fwd]
  ]

-- | Catalog entries producing a given scalar target type.
injFCatalogFor :: Ty -> [InjFSig]
injFCatalogFor ty = [ s | s <- injFCatalog, injFResult s == ty ]

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
-- Every candidate has a strictly smaller node count and a 'Ty' that
-- 'tyGeneralizes' the node's own -- the *asymmetric* test, not a symmetric
-- compatibility/join one, which M1 used and which was too weak (see
-- 'tyGeneralizes'). So the result is well-founded and never hands the property
-- an ill-typed or ill-scoped program (either of which would be discarded,
-- minimizing nothing).
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

-- | Type-preserving shrink for a 'genTypedProgram' draw: shrink the part of
-- @main@ the generator owns and leave the neural/ADT/writeLogits sections
-- alone. Extra function declarations, if a later milestone adds them, are
-- preserved untouched -- a wrong-but-conservative shrink is a big
-- counterexample, while a wrong-and-aggressive one is a *different*
-- counterexample, which is worse.
--
-- For a milestone-M3 neural draw, "the part the generator owns" is the core
-- under the @sym@ lambda and the @let@ that binds the network read, with the
-- bound variable in scope ('typedMainParts'). The wrapper is rebuilt around
-- every candidate rather than shrunk: the declaration, the read and the
-- binding are what makes the draw a neural draw at all, so reducing them would
-- minimize a plan-enumeration counterexample into a program that no longer
-- reaches the engine.
shrinkTypedProgram :: Program -> [Program]
shrinkTypedProgram p = case typedMainParts p of
  Nothing -> []
  Just ((env, core), rebuild) ->
    [ p { functions = map (replaceMain (rebuild core')) (functions p) }
    | core' <- shrinkTypedExprIn env core
    ]
  where
    replaceMain body' (n, b) = if n == "main" then (n, body') else (n, b)
