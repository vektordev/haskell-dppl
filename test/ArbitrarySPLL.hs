{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
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
, genHelperProgram
, genRecursiveProgram
, RecShape(..)
, recShapeOfProgram
, recursionSafe
, unguardedProjections
, withADTs
, adtPool
, adtPoolNames
, genADTDecls
, adtShapes
, adtDeclSize
, adtLeaf
, genMutualADTPair
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
, ArrowShape(..)
, arrowShapeOf
, arrowShapeOfProgram
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
, boundaryConstsOfProgram
, divisionOfProgram
, boundaryFloats
, boundaryInts
, injFCatalogFor
, injFExcluded
, InjFExclusion(..)
, injFNamesOf
, injFLeafApp
)where

import Test.QuickCheck
import Data.List (nub, find, stripPrefix)
import Control.Monad (filterM, foldM)
import Data.Maybe (fromMaybe, listToMaybe, isJust, isNothing)
import Data.Char (isDigit)

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Parser (reserved)
import SPLL.ReservedNames (reservedIdentifierReason)
import SPLL.Validator (validateProgram)
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

-- Generator for valid identifiers (not a keyword, not a builtin InjF name, not
-- a name the compiler claims -- 'SPLL.ReservedNames'; e.g. "sample" or "ast1")
genValidIdentifier :: Gen String
genValidIdentifier = do
  ident <- genIdentifier
  if ident `elem` reserved || ident `elem` map fst (globalFEnv []) || isJust (reservedIdentifierReason ident)
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
    return $ Program funcs neuralDecls [] [] []

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
  return $ Program (mainDecl : extraFuncs) neuralDecls [] [] []

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
-- The arrow axis (task fuzz-arrow-generator-coverage) adds 'TyArrow', which is
-- a generation target like any other *except* that 'genTy' never draws one:
-- an arrow-typed @main@ is a closure, and asking for its density or sampling
-- it is meaningless. Arrow-typed positions are opened by the productions that
-- immediately consume them -- an application, a function-valued @let@, a
-- top-level helper -- so every function value the generator emits is applied
-- (or bound and then applied) rather than returned.
--
-- 'TyAny' is not a generation target. It is the "this position's type is not
-- determined by the node itself" marker that type *recovery* needs: a
-- @left x@ node fixes only the left component, a @right y@ node only the
-- right, and neither says anything about the other. A 'Lambda' is the third
-- such node -- nothing on it records what its parameter was bound at -- so a
-- function value recovers as @TyArrow TyAny r@ unless it is read at an
-- application, where the argument pins the parameter. See 'tyOfTypedExpr'.
data Ty = TyFloat | TyInt | TyBool
        | TyTuple Ty Ty
        | TyEither Ty Ty
        | TyList Ty
        | TyArrow Ty Ty
        | TyADT String   -- ^ a declaration in the 'HasADTs' context, by name (milestone M4)
        | TyAny
  deriving (Show, Eq)

-- | The variables in scope and the 'Ty' each was bound at. Innermost binding
-- first, so a plain 'lookup' implements shadowing -- though the generator
-- itself never shadows (see 'freshName').
type TyEnv = [(String, Ty)]

-- | Size-bounded target types. Deliberately scalar-heavy: a structured target
-- multiplies the expression budget across components, and the invariant
-- properties still want a solid mass of the scalar shapes that reach a
-- probability function.
--
-- Never emits 'TyAny', and never emits 'TyArrow': this is the type of a
-- *result* -- a program's, a binding's, an argument's -- and every one of
-- those positions is one a function value must not be returned into. The
-- arrow productions open arrow-typed positions themselves, directly around
-- the application that eliminates them.
genTy :: Int -> Gen Ty
genTy n = withPool (genTyIn n)

-- | Is this type in a mutually recursive group (two or more types each
-- reaching the other)?
isMutualADT :: HasADTs => String -> Bool
isMutualADT n = any (\m -> m /= n && n `elem` adtReach m) (adtReach n)

-- | 'genTy' over the declarations in scope rather than the pool.
genTyIn :: HasADTs => Int -> Gen Ty
genTyIn n
  | n <= 0 = scalarTy
  | otherwise = frequency $
      [ (6, scalarTy)
      , (2, TyTuple <$> genTyIn half <*> genTyIn half)
      , (2, TyEither <$> genTyIn half <*> genTyIn half)
      , (2, TyList <$> genTyIn half)
      ]
      -- Milestone M4. Weighted below the other structured shapes: every ADT
      -- target also opens the field-projection eliminators at its fields'
      -- types ('adtElimProds'), so ADT nodes reach many more draws than this
      -- weight alone suggests.
      ++ [ (1, TyADT <$> elements adtNames) | not (null adtNames) ]
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
-- Three shapes. Three draws in five are nullary. One in five (milestone M3)
-- instead declares a neural network and reads it:
-- @main sym = let s = nn sym in \<observations of s\>@. Those draws are the
-- only way the plan-guided enumeration engine is reached at all, and they
-- cost the properties nothing extra -- the same invariants apply unchanged.
-- See 'genNeuralProgram'. The remaining one in five declares a named
-- top-level function and calls it (task fuzz-arrow-generator-coverage); see
-- 'genHelperProgram'.
--
-- A neural draw's @main@ takes an argument, so a caller running it has to
-- supply a mock-network symbol rather than the empty argument list every other
-- draw wants. TestFuzz's @fuzzArgs@ derives that from the program.
--
-- Milestone M4 adds a fourth, 'genRecursiveProgram' (a recursive top-level
-- function), and ADT declarations to all of them: every draw first draws a
-- declaration context ('genADTDecls': some pool seeds plus generated
-- declarations), any node may build or take apart a value of a type in it,
-- and the program declares exactly the ones it uses ('declareHere').
genTypedProgram :: Gen Program
genTypedProgram = withGeneratedADTs $ frequency
  [ (3, genPlainProgramIn)
  , (1, genHelperProgramIn)
  , (1, genNeuralProgramIn)
  , (1, genRecursiveProgramIn)
  ]

-- | The nullary shape: @main = \<expr\>@, with no neural declaration.
genPlainProgramIn :: HasADTs => Gen Program
genPlainProgramIn = do
  ty <- genTyIn tyDepth
  body <- sized (fmap uniquifyBinders . genTypedExprIn [] ty)
  return $ declareHere $ Program [("main", body)] [] [] [] []

-- | @helper x = \<expr\>; main = helper \<expr\>@ -- the named top-level
-- function with a probabilistic argument, which is the *low bar* of the arrow
-- axis: the one shape in it that already worked before the axis existed
-- (rows 1-2 of @modality-function-space-test-coverage@'s table).
--
-- It is a program-level production rather than an expression-level one
-- because that is what a top-level function is. Generating it matters for
-- two reasons beyond the shape itself: a bare name in callee position is the
-- one callee 'SPLL.CalleeNormalize' deliberately leaves alone, so nothing
-- else in the generator reaches the path forward chaining resolves by
-- itself; and the helper's body is generated in a scope holding only its
-- parameter, so the argument's randomness crosses a function boundary to
-- reach it.
--
-- The two functions' binders are renamed from *different* prefixes.
-- 'SPLL.Validator' is stricter than lexical scoping about name reuse (see
-- 'uniquifyBinders'), and two independently generated bodies both start at
-- @v0@.
genHelperProgram :: Gen Program
genHelperProgram = withGeneratedADTs genHelperProgramIn

genHelperProgramIn :: HasADTs => Gen Program
genHelperProgramIn = sized $ \n -> do
  aty <- genTyIn 1
  rty <- genTyIn 1
  hbody <- genTypedExprIn [(helperParam, aty)] rty (n `div` 2)
  arg   <- genTypedExprIn [(helperName, TyArrow aty rty)] aty (n `div` 2)
  let helper = uniquifyBindersFrom (declBinderPrefix helperName) (helperParam #-># hbody)
      body   = uniquifyBinders (apply (varE helperName) arg)
  return $ declareHere $ Program [(helperName, helper), ("main", body)] [] [] [] []

-- | The generated top-level function's name and parameter. Neither may
-- collide with a predefined function or a distribution leaf; both are
-- rewritten by 'uniquifyBindersFrom' before they reach a program, except the
-- name itself, which is a declaration rather than a binder.
helperName :: String
helperName = "helper"

helperParam :: String
helperParam = "hp"

-- | The prefix a top-level declaration's binders are renamed from. Distinct
-- per declaration, and from @main@'s @v@, because 'SPLL.Validator' rejects a
-- name declared in two places even when the scopes are disjoint (see
-- 'uniquifyBinders'). The shrinker re-uniquifies every candidate and so has
-- to agree with generation here.
declBinderPrefix :: String -> String
declBinderPrefix nm
  | nm == helperName = "h"
  | nm == loopName   = "r"
  | otherwise        = "d"

-- ---------------------------------------------------------------------------
-- Milestone M4: recursion.
--
-- A recursive top-level function, in the two shapes the corpus uses and that
-- terminate *by construction* -- a generated draw that may not terminate would
-- report itself as a per-case timeout, which is a false counterexample, and
-- the shrinker would then minimize toward the non-termination rather than
-- toward the bug:
--
-- * 'CountedRec' -- @loop k = if k < 1 then \<base\> else \<step\>@, where
--   @\<step\>@ calls @loop (k - 1)@. Structural recursion on an Int counter,
--   the @dice.ppl@ shape; @main@ applies it to a small literal or a die.
-- * 'GeometricRec' -- @loop = if \<bernoulli p\> then \<base\> else \<step\>@,
--   where @\<step\>@ is @Link \<x\> loop@ or @cons \<x\> loop@. Stochastic
--   stopping, the @recursiveAdtMultiCtor@ shape; @main@ is a generated
--   expression with @loop@ in scope.
--
-- The geometric step is **productive** -- every recursive call is the
-- recursive field of a constructor of the result -- and that restriction is a
-- deliberate one. Generating with probability one and *inferring* in finite
-- time are different properties: @loop = if Uniform < 0.5 then 0 else loop@
-- samples fine, but its probability function calls itself at the same query
-- point and never returns. That is the open, already-filed bug
-- @unbounded-recursion-admitted-then-diverges@ (the first Slow run of this
-- milestone found it again within seven draws, minimized to exactly that
-- program), and re-finding a filed bug on every run spends every probability
-- property's budget on timeouts while telling nobody anything. In the
-- productive shape each call consumes one constructor of the observation, so
-- a finite query bounds the recursion. When that bug is settled, a
-- non-productive step is the obvious next widening.
--
-- The counted step makes **at most one** recursive call per invocation: the
-- first occurrence of the hole outside a function-valued lambda becomes the
-- call, and every other one a closed leaf ('linearizeHole'). That keeps its
-- cost linear in its counter rather than exponential. An occurrence under a
-- function value's lambda is dropped too: such a lambda may be applied any
-- number of times, and nothing here bounds that.
--
-- The shrinker preserves both guarantees ('recursionSafe').

-- | The recursive function's name. Fixed, like 'neuralName'.
loopName :: String
loopName = "loop"

-- | The counter of a 'CountedRec' function, and the placeholder its step is
-- generated against. Both are renamed before the program is handed out
-- (the parameter by 'uniquifyBindersFrom'; the hole is substituted away).
loopParam, loopHole :: String
loopParam = "rk"
loopHole  = "rhole"

-- | Which recursive shape a program contains, by a syntactic test on its
-- declarations, for the coverage tabulation. Ordered like 'LetShape'.
data RecShape = NoRec | CountedRec | GeometricRec
  deriving (Show, Eq, Ord)

-- | A declaration (other than @main@) whose body mentions its own name is
-- recursive; taking a parameter makes it counted. Only this module's two
-- shapes are generated, so the classifier need not distinguish further.
recShapeOfProgram :: Program -> RecShape
recShapeOfProgram p = maximum (NoRec :
  [ case node e of
      Lambda _ _ -> CountedRec
      _          -> GeometricRec
  | (nm, e) <- functions p, nm /= "main", mentionsVar nm e ])

genRecursiveProgram :: Gen Program
genRecursiveProgram = withGeneratedADTs genRecursiveProgramIn

-- | The geometric shape needs a type with a directly self-recursive
-- constructor. A context without one gets the pool's @Chain@ added, so the
-- ADT half of the geometric draws does not vanish with the luck of the
-- declaration draw.
genRecursiveProgramIn :: HasADTs => Gen Program
genRecursiveProgramIn =
  let ?adts = if null selfRecursiveADTs then ?adts ++ [ d | d <- adtPool, dataName d == "Chain" ] else ?adts
  in sized $ \n -> oneof
    [ do ty <- genTyIn 1
         genCountedRec ty n
    , do ty <- oneof [TyADT <$> elements selfRecursiveADTs, TyList <$> genTyIn 0]
         genGeometricRec ty n
    ]

-- | @loop k = if k < 1 then \<base\> else \<step\>[loop (k - 1)]; main = loop \<arg\>@.
--
-- The counter is in scope in both arms, so the step can compute with it. The
-- argument is a literal or a die, never a general Int expression: an Int
-- expression can be large (products of dice), and while the recursion is
-- linear, a few hundred levels of it is a slow compile rather than a finding.
genCountedRec :: HasADTs => Ty -> Int -> Gen Program
genCountedRec ty n = do
  let kenv = [(loopParam, TyInt)]
  base <- genTypedExprIn kenv ty (n `div` 3)
  step <- genWithHole ((loopHole, ty) : kenv) ty (n `div` 2)
  leaf <- genTypedLeaf ty
  arg  <- frequency [ (2, constI <$> choose (0, 3)), (1, dice <$> choose (2, 4)) ]
  let call = apply (varE loopName) (varE loopParam #<->#  constI 1)
      body = loopParam #-># ifThenElse (varE loopParam #<# constI 1)
                                       base
                                       (linearizeHole loopHole call leaf step)
  return $ declareHere $ Program
    [ (loopName, uniquifyBindersFrom (declBinderPrefix loopName) body)
    , ("main", apply (varE loopName) arg)
    ] [] [] [] []

-- | @loop = if \<bernoulli p\> then \<base\> else \<step\>; main = \<expr using loop\>@,
-- at a type with a recursive constructor ('productiveStep').
genGeometricRec :: HasADTs => Ty -> Int -> Gen Program
genGeometricRec ty n = do
  p    <- choose (0.3, 0.9)
  base <- genTypedExprIn [] ty (n `div` 3)
  step <- productiveStep ty (n `div` 2)
  mty  <- genTyIn 1
  mainBody <- frequency
    [ (1, pure (varE loopName))
    -- At another type the program may simply not call @loop@; then @main@
    -- is the bare call instead, so the recursion is never dead.
    , (2, if mty == ty
            then genWithHole [(loopName, ty)] mty (n `div` 2)
            else do e <- genTypedExprIn [(loopName, ty)] mty (n `div` 2)
                    return (if mentionsVar loopName e then e else varE loopName)) ]
  let body = ifThenElse (bernoulli p) base step
  return $ declareHere $ Program
    [ (loopName, uniquifyBindersFrom (declBinderPrefix loopName) body)
    , ("main", uniquifyBinders mainBody)
    ] [] [] [] []

-- | One constructor around a recursive call, its other fields generated in the
-- empty scope (so they cannot call @loop@ themselves, unproductively). Sometimes
-- inside an @if@ whose other arm is an ordinary draw, which stays productive:
-- every path that recurses still consumes a constructor.
--
-- At an ADT, any constructor with a field of the type itself will do, and one
-- such field (drawn) holds the call. Any *other* self-typed field gets a closed
-- leaf rather than a second call: two calls per step would make the stopping
-- coin a branching process, supercritical for the lower half of its range,
-- which samples forever with positive probability.
productiveStep :: HasADTs => Ty -> Int -> Gen Expr
productiveStep ty n = do
  core <- case ty of
    TyList a -> (`cons` varE loopName) <$> genTypedExprIn [] a half
    TyADT nm | ctors@(_ : _) <- [ ctor | ctor@(_, fs) <- adtCtors nm, any ((== ty) . snd) fs ] -> do
      (c, fs) <- elements ctors
      i <- elements [ j | (j, (_, t)) <- zip [0 :: Int ..] fs, t == ty ]
      args <- sequence
        [ if j == i then pure (varE loopName)
          else if t == ty then genTypedLeaf t
          else genTypedExprIn [] t (half `div` max 1 (length fs))
        | (j, (_, t)) <- zip [0 ..] fs ]
      return (injF c args)
    -- Unreachable: 'genRecursiveProgramIn' draws only the two shapes above.
    _ -> genTypedLeaf ty
  frequency
    [ (3, pure core)
    , (1, do c   <- genTypedExprIn [] TyBool half
             alt <- genTypedExprIn [] ty half
             return (ifThenElse c core alt)) ]
  where half = n `div` 2

-- | Does a shrink candidate of declaration @nm@ keep the termination
-- guarantee the original had? Shrinks never duplicate a subterm, so the
-- number of calls cannot grow; what they *can* do is move a call out of the
-- position that made it terminate -- collapse @Link x loop@ to @loop@, or the
-- counted call's @k - 1@ to @k@ -- and the shrinker, rewarded for keeping a
-- timeout alive, would do exactly that. So: every call in the candidate must
-- be one the original already had, in the same productive position (a
-- nullary declaration) or with the same argument (a counted one).
--
-- "Productive" means a direct argument of a constructor of one of @decls@ (the
-- program's declarations) or of @Cons@: being well-typed, such a call sits in
-- a field of the recursive type itself, so it consumes one constructor of the
-- observation.
recursionSafe :: [ADTDecl] -> String -> Expr -> Expr -> Bool
recursionSafe decls nm orig cand = case node orig of
  Lambda _ _ -> all (`elem` callArgs orig) (callArgs cand) && bareCalls cand == 0
  _          -> unproductive cand == 0
  where
    callArgs e = case node e of
      Apply f a | Var v <- node f, v == nm -> a : callArgs a
      _ -> concatMap callArgs (children e)
    -- Occurrences of @nm@ not in callee position.
    bareCalls e = case node e of
      Var v -> if v == nm then 1 else 0 :: Int
      Apply f a | Var v <- node f, v == nm -> bareCalls a
      _ -> sum (map bareCalls (children e))
    -- Occurrences of @nm@ other than as a direct constructor argument.
    ctorNames = "Cons" : [ c | d <- decls, (c, _) <- constructors d ]
    unproductive e = case node e of
      Var v -> if v == nm then 1 else 0 :: Int
      InjF (Named c) args
        | c `elem` ctorNames -> sum [ if isCall a then 0 else unproductive a | a <- args ]
      _ -> sum (map unproductive (children e))
    isCall a = case node a of
      Var v -> v == nm
      _     -> False

-- | Generate at a type in a scope whose innermost entry is a hole the result
-- must mention. Retried a couple of times; if the hole is still absent --
-- which at a structured type is the common case, the hole being one leaf of
-- one exact type -- the draw is spliced in as the alternative of a generated
-- condition, @if \<cond\> then \<hole\> else \<draw\>@. Without that, most
-- structured recursive draws came out not recursive at all.
genWithHole :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genWithHole env ty n = go (2 :: Int)
  where
    hole = case env of
      ((h, _) : _) -> h
      []           -> ""
    go k = do
      e <- genTypedExprIn env ty n
      if mentionsVar hole e then return e
      else if k > 0 then go (k - 1)
      else do c <- genTypedExprIn env TyBool (n `div` 3)
              return (ifThenElse c (varE hole) e)

-- | Replace the first occurrence of @hole@ that is evaluated at most once per
-- evaluation of the whole expression by @call@, and every other occurrence by
-- @leaf@ -- see the section comment for why. "At most once" means not under a
-- function value's lambda; a @let@'s lambda is evaluated once and is
-- descended into normally.
linearizeHole :: String -> Expr -> Expr -> Expr -> Expr
linearizeHole hole call leaf e0 = fst (go False e0)
  where
    go :: Bool -> Expr -> (Expr, Bool)
    go used e = case node e of
      Var x | x == hole -> if used then (leaf, True) else (call, True)
      _ | Just (x, val, body) <- asLet e ->
            let (val', u1)  = go used val
                (body', u2) = go u1 body
            in (letIn x val' body', u2)
      Lambda x b -> (Expr (ann e) (Lambda x (dropHole b)), used)
      _ -> let (cs', u) = goMany used (children e) in (withChildren e cs', u)
    goMany u [] = ([], u)
    goMany u (c:cs) = let (c', u1) = go u c
                          (cs', u2) = goMany u1 cs
                      in (c' : cs', u2)
    dropHole e = case node e of
      Var x | x == hole -> leaf
      _ -> withChildren e (map dropHole (children e))

-- | Rebuild a node around replacement children, in 'children' order.
withChildren :: Expr -> [Expr] -> Expr
withChildren e cs = Expr (ann e) $ case (node e, cs) of
  (IfThenElse{}, [c, t, f]) -> IfThenElse c t f
  (InjF nm _, _)            -> InjF nm cs
  (Apply{}, [a, b])         -> Apply a b
  (Lambda x _, [b])         -> Lambda x b
  (other, _)                -> other

-- | Generate at a type in the empty scope. The scope-carrying worker is
-- 'genTypedExprIn'; this is the entry point every property uses.
--
-- The result's binders are made globally distinct before it is handed out --
-- see 'uniquifyBinders' for why that is a hard requirement rather than
-- tidiness. A caller that *composes* two draws into one program (TestFuzz's
-- 'genMixturePair' does) must re-prefix at least one of them with
-- 'uniquifyBindersFrom', since two independent draws both start at @v0@.
genTypedExpr :: Ty -> Int -> Gen Expr
genTypedExpr ty n = withPool (uniquifyBinders <$> genTypedExprIn [] ty n)

genTypedExprIn :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genTypedExprIn env TyAny n = do
  -- Only reachable if a caller hands us a recovered type. Resolve the free
  -- position to a concrete one rather than failing.
  ty <- genTyIn 0
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
genTypedLeafIn :: HasADTs => TyEnv -> Ty -> Gen Expr
genTypedLeafIn env ty = case [ v | (v, t) <- env, t == ty ] of
  [] -> genTypedLeaf ty
  vs -> frequency [ (2, genTypedLeaf ty), (3, elements (map varE vs)) ]

varE :: String -> Expr
varE v = Expr makeTypeInfo (Var v)

-- | Smallest *closed* inhabitants the generator uses. Note the list case: the
-- generator never emits a bare 'nul', because an empty-list constant carries
-- no element type and so would be opaque to 'tyOfTypedExpr'. A one-element
-- list is the smallest list whose type can be read back off the node.
genTypedLeaf :: HasADTs => Ty -> Gen Expr
genTypedLeaf TyFloat = oneof
  [ pure normal
  , pure uniform
  , constF <$> genFloatConst
  ]
genTypedLeaf TyInt = oneof
  [ constI <$> genIntConst
  , dice <$> choose (2, 6)
  ]
genTypedLeaf TyBool = oneof
  [ constB <$> arbitrary
  , bernoulli <$> choose (0.01, 0.99)
  ]
genTypedLeaf TyAny = genTypedLeaf TyFloat
-- The smallest function value is a constant one. It ignores its argument,
-- which is not a degenerate case to be avoided but a shape worth covering:
-- whatever randomness the argument carries is dropped on the floor, and the
-- inference engines have to agree that it was.
genTypedLeaf (TyArrow _ b) = (arrowLeafParam #->#) <$> genTypedLeaf b
genTypedLeaf (TyTuple a b) = tuple <$> genTypedLeaf a <*> genTypedLeaf b
genTypedLeaf (TyEither a b) = oneof
  [ left <$> genTypedLeaf a
  , right <$> genTypedLeaf b
  ]
genTypedLeaf (TyList a) = (`cons` nul) <$> genTypedLeaf a
-- A constructor applied to leaves, of one whose fields are all of strictly
-- lower 'adtRanks' rank, so a leaf stays finite ('leafCtors').
genTypedLeaf (TyADT n) = oneof
  [ injF c <$> mapM (genTypedLeaf . snd) fs | (c, fs) <- leafCtors n ]

-- | A numeric constant for a leaf: half the time one of the boundary values
-- 'boundaryFloats', half the time uniform in @(-10, 10)@ (task
-- fuzz-boundary-value-leaves).
--
-- A uniform 'Double' is exactly @0.0@ with probability ~0, and the special
-- cases worth fuzzing sit precisely there: the optimizer's constant folding
-- ('IROptimizer.softForceArithmetic' and friends) matches a literal @0@ and
-- @1@, and the inverses of @mult@ and @recip@ branch on a zero operand.
--
-- Non-finite values and high-exponent finite ones are deliberately absent.
-- @Infinity@ and @NaN@ have no source spelling (only an overflowing literal
-- such as @1e400@ reaches one), and on the value-level invariants they, and
-- magnitudes like @1e300@ that overflow under @exp@ or cancel catastrophically
-- under @+@, fail by IEEE design rather than by compiler bug; see the task
-- document for the decision.
genFloatConst :: Gen Double
genFloatConst = oneof [ elements boundaryFloats, choose (-10, 10) ]

-- | The Int twin of 'genFloatConst'.
genIntConst :: Gen Int
genIntConst = oneof [ elements boundaryInts, choose (-10, 10) ]

-- | The constants 'genFloatConst' favours: the identities and absorbing
-- element of the arithmetic the optimizer folds, and the sign flip.
boundaryFloats :: [Double]
boundaryFloats = [0, 1, -1]

boundaryInts :: [Int]
boundaryInts = [0, 1, -1]

-- | Which boundary constants a draw contains anywhere, as labels for
-- @prop_Fuzz_GeneratorCoverage@'s @boundary constant@ row: @"Float 0.0"@,
-- @"Int -1"@ and so on, each at most once, or @["none"]@.
boundaryConstsOfProgram :: Program -> [String]
boundaryConstsOfProgram p = case nub (concatMap (concatMap boundaryLabel . universeOf . snd) (functions p)) of
  [] -> ["none"]
  ls -> ls
  where
    boundaryLabel e = case node e of
      Constant (VFloat f) | f `elem` boundaryFloats -> ["Float " ++ show f]
      Constant (VInt i)   | i `elem` boundaryInts   -> ["Int " ++ show i]
      _ -> []

-- | How a draw divides, for the coverage property's @division@ row: not at
-- all, only by non-literal divisors, or by a literal zero somewhere.
divisionOfProgram :: Program -> String
divisionOfProgram p
  | any zeroDivisor recips = "by a literal zero"
  | null recips            = "none"
  | otherwise              = "by a non-literal or nonzero divisor"
  where
    recips = [ a | (_, e) <- functions p, n <- universeOf e
                 , InjF (Named "recip") [a] <- [node n] ]
    zeroDivisor a = case node a of
      Constant (VFloat 0) -> True
      _                   -> False

universeOf :: Expr -> [Expr]
universeOf e = e : concatMap universeOf (getSubExprs e)

-- | The binder of a closed function leaf. Any name does: 'uniquifyBinders'
-- renames every binder in the finished expression anyway, and a leaf is by
-- construction the innermost thing there is.
arrowLeafParam :: String
arrowLeafParam = "p"

genTypedRec :: HasADTs => TyEnv -> Ty -> Int -> [Gen Expr]
genTypedRec env ty n =
  [ ifThenElse <$> gen TyBool half <*> gen ty half <*> gen ty half
  ]
  -- Eliminators: reach the target type *through* a structured intermediate.
  -- These are what put the change-of-variables/dimension bookkeeping and the
  -- IRConformsTo structural checks in front of the invariant properties --
  -- building a tuple is easy, taking one apart is where the work is.
  ++ [ do other <- genTyIn 1
          tfst <$> gen (TyTuple ty other) half
     , do other <- genTyIn 1
          tsnd <$> gen (TyTuple other ty) half
     , lhead <$> gen (TyList ty) half
     ]
  -- Milestone M2: the 'let' surface. Two productions, because the shape that
  -- reaches the *interesting* engine is a narrow corner of the shape space and
  -- a generic 'let' lands in it far too rarely to rely on.
  ++ [ genPlainLet env ty n
     , genWitnessLet env ty n
     ]
  -- The arrow surface (task fuzz-arrow-generator-coverage). Withheld below a
  -- size threshold and at an arrow target, which keeps the function values
  -- shallow: a first-order function applied to a first-order argument is the
  -- whole region the task is about, and letting these fire all the way down
  -- would spend the budget building third-order shapes nothing infers.
  ++ (if n >= arrowProdSize && not (isArrowTy ty) then arrowProds env ty n else [])
  -- Milestone M4: reach the target through a field of, or a constructor test
  -- on, a pool ADT.
  ++ adtElimProds env ty n
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
      TyADT nm -> adtCtorProds env nm n
      -- The subtraction sugars stay explicit alongside the catalog: @a - b@ is
      -- @plus a (neg b)@, a *composite* shape the catalog cannot name, and the
      -- realized nesting is the point of having it.
      -- Division likewise: @a / b@ is @mult a (recip b)@, and @recip@ is out
      -- of the catalog for its @b /= 0@ guard ('injFUnconditional'). It is
      -- generated here regardless, at the weight of one catalog entry, so the
      -- @recip@ inverse family is fuzzed at all (task
      -- fuzz-boundary-value-leaves); with 'boundaryFloats' a literal zero
      -- divisor is a common draw, and what the compiler does with one is
      -- exactly what is under test.
      TyFloat ->
        catalogProds TyFloat ++
        [ (#-#) <$> gen TyFloat half <*> gen TyFloat half
        , (#/#) <$> gen TyFloat half <*> gen TyFloat half ]
      TyInt ->
        catalogProds TyInt ++
        [ (#<->#) <$> gen TyInt half <*> gen TyInt half ]
      TyBool ->
        catalogProds TyBool ++
        -- Structural tests: the only Bool-producing eliminators for lists and
        -- Either, and the reason those shapes get *observed* rather than just
        -- constructed and returned.
        [ do a <- genTyIn 1
             isNull <$> gen (TyList a) half
        , do a <- genTyIn 1
             b <- genTyIn 1
             sisLeft <$> gen (TyEither a b) half
        , do a <- genTyIn 1
             b <- genTyIn 1
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
      -- A lambda literal. Everything else that produces a function value --
      -- an @if@ choosing between two of them, a tuple or list one is
      -- projected out of, a variable bound to one -- comes from the
      -- *generic* productions above, which are indexed by the target type
      -- and so now fire at an arrow target like any other.
      TyArrow a b ->
        [ do let v = freshName env
             body <- genTypedExprIn ((v, a) : env) b (n - 1)
             return (v #-># body)
        ]

-- ---------------------------------------------------------------------------
-- The arrow surface (task fuzz-arrow-generator-coverage).
--
-- Three productions, matching the three ways a function value reaches an
-- argument in a program somebody would actually write: applied where it is
-- written, bound and then applied, and applied to two arguments in a row.
-- What *kind* of function value each one applies is not decided here -- it is
-- drawn at the arrow target by the ordinary productions, so a lambda literal,
-- an @if@ between two of them, one projected out of a tuple or list, and a
-- variable bound to any of those all arise without a production of their own.
--
-- The one shape deliberately *not* produced is a function value returned from
-- @main@: 'genTy' never draws an arrow, so every arrow-typed position the
-- generator opens is eliminated by the production that opened it.

-- | The size below which the arrow productions do not fire.
arrowProdSize :: Int
arrowProdSize = 4

isArrowTy :: Ty -> Bool
isArrowTy TyArrow{} = True
isArrowTy _         = False

-- The three share *one* slot in the node's production set rather than taking
-- three of them. 'genTypedExprIn' picks with 'oneof', so every production
-- added at a node dilutes all the others equally, and three more would have
-- cut the existing ones by about a fifth at every level. That is not a
-- cosmetic concern: the properties that draw a *pair* of programs
-- (@prop_Fuzz_MixtureFollowsCombinationRules@, and the neural twin oracle)
-- need both halves to reach a probability function, so they see the square of
-- that rate, and at three slots both stopped falsifying and started giving up
-- on their discard ratio -- a measured loss of power in properties that were
-- finding real bugs. One slot still puts a function value in a good third of
-- all draws (see the @arrow shape@ row of the coverage property).
arrowProds :: HasADTs => TyEnv -> Ty -> Int -> [Gen Expr]
arrowProds env ty n =
  [ oneof
      [ genApply env ty n
      , genFunctionLet env ty n
      , genCurriedApply env ty n
      ]
  ]

-- | @\<function value\> \<argument\>@.
--
-- The argument type is drawn to *match an in-scope function* where one
-- returns the target type, on the same reasoning 'genTypedLeafIn' prefers a
-- variable to a closed leaf: a bound function nothing ever calls is a dead
-- binding, and the engines this exists to reach never see it. Note that a
-- lambda literal drawn for the callee here makes the node a @let@ -- that is
-- not a degenerate outcome but the "directly-applied lambda" shape, spelled
-- the way the compiler spells every @let@ ('SPLL.Prelude.letIn').
genApply :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genApply env ty n = do
  aty <- argTyFor env ty
  f   <- genTypedExprIn env (TyArrow aty ty) half
  arg <- genTypedExprIn env aty half
  return (apply f arg)
  where half = n `div` 2

-- | An argument type for an application returning @ty@: one an in-scope
-- function already takes, where there is one.
argTyFor :: HasADTs => TyEnv -> Ty -> Gen Ty
argTyFor env ty = case [ a | (_, TyArrow a b) <- env, b == ty ] of
  [] -> genTyIn 1
  as -> frequency [ (1, genTyIn 1), (2, elements as) ]

-- | @(\\f -> f \<arg\>) \<function value\>@ -- a function value passed as an
-- argument and applied inside the body, which is 'SPLL.Prelude.letIn' of a
-- function value and so also the @let f = \\x -> ... in f ...@ shape.
--
-- Unlike 'genApply' this one *builds* the call rather than hoping the body
-- draws it, because the shape is the point: the bound variable is the
-- function, so the compiler has to resolve a callee that is a lambda
-- parameter -- the case whose absence was bug A of
-- @modality-arrow-apply-crashes@.
genFunctionLet :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genFunctionLet env ty n = do
  aty <- genTyIn 0
  let fv  = freshName env
      fty = TyArrow aty ty
  fun <- genTypedExprIn env fty half
  arg <- genTypedExprIn ((fv, fty) : env) aty half
  return (apply (fv #-># apply (varE fv) arg) fun)
  where half = n `div` 2

-- | @f a b@ -- two arguments to one function value, which is where
-- 'SPLL.Typing.ModalityInfer''s @TArrow@ arm is exercised at more than one
-- nesting depth.
genCurriedApply :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genCurriedApply env ty n = do
  aty <- genTyIn 0
  bty <- genTyIn 0
  f <- genTypedExprIn env (TyArrow aty (TyArrow bty ty)) third
  a <- genTypedExprIn env aty third
  b <- genTypedExprIn env bty third
  return (apply (apply f a) b)
  where third = n `div` 3

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
genPlainLet :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
genPlainLet env ty n = do
  bty <- genTyIn 1
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
genWitnessLet :: HasADTs => TyEnv -> Ty -> Int -> Gen Expr
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
-- Milestone M4: algebraic data types, with generated declarations (task
-- fuzz-generate-adt-declarations).
--
-- Every program draw first draws its *declaration context* ('genADTDecls'): a
-- random subset of the fixed pool below plus up to three generated
-- declarations. The pool stays as a named seed set -- its four entries are the
-- corpus' four ADT shapes, and pinned tests name them -- but a pool alone
-- cannot reach any shape outside those four, nor anything name-sensitive.
-- Generated declarations vary what the pool fixes:
--
-- * names, including (one name in seven) a name a target language claims --
--   @None@, @T@, @Module@, @len@, @end@ -- and, now and then, a constructor
--   spelled like its own type;
-- * one to five constructors, nullary-only enumerations through wide records;
-- * field types: scalars, tuples, Eithers and lists of them, other declared
--   ADTs, lists of ADTs, the type itself (in several fields at once, too), or
--   -- for a mutually recursive pair -- its partner;
-- * an optional @depth N@ on a directly self-recursive type.
--
-- The first constructor of a generated type only ever holds already-grounded
-- types, so every type has a finite leaf ('adtRanks', 'leafCtors').
--
-- The context reaches generation, recovery and shrinking as the implicit
-- parameter @?adts@ ('HasADTs'). Constructor, accessor and test names are what
-- recovery reads off a node, so all three need the same table; once a program
-- is declared, its own 'adts' field *is* that table, and the program-level
-- entry points ('shrinkTypedProgram', 'typedMainCoreTy', 'neuralTwin', ...)
-- bind it from there. The expression-level exports ('genTy',
-- 'genTypedExpr', 'tyOfTypedExpr', 'shrinkTypedExpr', 'typedLeaves') keep
-- their signatures and run against the pool ('withPool').

-- | The ADT declarations in scope.
type HasADTs = (?adts :: [ADTDecl])

-- | Run against the fixed pool.
withPool :: (HasADTs => a) -> a
withPool x = let ?adts = adtPool in x

-- | Run against a program's own declarations.
inProgram :: Program -> (HasADTs => a) -> a
inProgram p x = let ?adts = adts p in x

-- | Draw a declaration context and generate under it.
withGeneratedADTs :: (HasADTs => Gen a) -> Gen a
withGeneratedADTs g = do
  ds <- genADTDecls
  let ?adts = ds in g

-- | Declare exactly the in-scope types a generated program uses.
declareHere :: HasADTs => Program -> Program
declareHere = declareUsed ?adts

-- | The fixed seed pool, one declaration per corpus ADT shape:
--
-- * @Hue@   -- an enumeration, three nullary constructors: the k-way discrete
--   that @Bool@ cannot be (the M3 note asked for one wider than two);
-- * @Pt@    -- a single-constructor record, whose accessors are total;
-- * @Mix@   -- mixed arity (nullary, unary, binary), whose accessors are
--   partial and must be guarded by a constructor test;
-- * @Chain@ -- recursive, with a default @depth@ so a neural target
--   auto-derives.
adtPool :: [ADTDecl]
adtPool =
  [ ADTDecl "Hue"   [("Red", []), ("Green", []), ("Blue", [])] Nothing
  , ADTDecl "Pt"    [("MkPt", [("px", TFloat), ("pflag", TBool)])] Nothing
  , ADTDecl "Mix"   [ ("Zero", [])
                    , ("One", [("mu", TFloat)])
                    , ("Two", [("ma", TInt), ("mb", TBool)]) ] Nothing
  , ADTDecl "Chain" [ ("Stop", [])
                    , ("Link", [("lv", TFloat), ("lnext", TADT "Chain")]) ] (Just 3)
  ]

adtPoolNames :: [String]
adtPoolNames = map dataName adtPool

-- | The names of the types in scope.
adtNames :: HasADTs => [String]
adtNames = map dataName ?adts

-- | An in-scope type's constructors with their fields' 'Ty's.
adtCtors :: HasADTs => String -> [(String, [(String, Ty)])]
adtCtors n =
  [ (c, [ (f, fromMaybe TyAny (rTypeToTy rt)) | (f, rt) <- fs ])
  | d <- ?adts, dataName d == n, (c, fs) <- constructors d ]

-- | The ADT names a type mentions.
adtsInTy :: Ty -> [String]
adtsInTy t = case t of
  TyADT n      -> [n]
  TyTuple a b  -> adtsInTy a ++ adtsInTy b
  TyEither a b -> adtsInTy a ++ adtsInTy b
  TyList a     -> adtsInTy a
  TyArrow a b  -> adtsInTy a ++ adtsInTy b
  _            -> []

-- | Every type reachable from @n@'s fields, transitively. Contains @n@ itself
-- exactly when @n@ is (directly or mutually) recursive.
adtReach :: HasADTs => String -> [String]
adtReach n = go [] (direct n)
  where
    direct m = nub [ k | (_, fs) <- adtCtors m, (_, t) <- fs, k <- adtsInTy t ]
    go seen [] = seen
    go seen (k : ks)
      | k `elem` seen = go seen ks
      | otherwise     = go (seen ++ [k]) (ks ++ direct k)

isCyclicADT :: HasADTs => String -> Bool
isCyclicADT n = n `elem` adtReach n

-- | The types with a constructor holding a field of the type itself -- the
-- ones a productive geometric recursion can be built over.
selfRecursiveADTs :: HasADTs => [String]
selfRecursiveADTs = [ n | n <- adtNames, any (any ((== TyADT n) . snd) . snd) (adtCtors n) ]

-- | How deep the smallest closed value of each type is: a type's rank is one
-- more than the least, over its constructors, of the largest rank among the
-- constructor's fields (scalars rank 0). A type absent from the table has no
-- finite value at all. Computed to a fixpoint; contexts hold a handful of
-- types.
adtRanks :: HasADTs => [(String, Int)]
adtRanks = go []
  where
    go r = let r' = [ (n, k) | n <- adtNames, Just k <- [rankOf r n] ]
           in if r' == r then r else go r'
    rankOf r n = case [ m | (_, fs) <- adtCtors n, Just m <- [maxRank r (map snd fs)] ] of
      [] -> Nothing
      ms -> Just (1 + minimum ms)
    maxRank r ts = maximum . (0 :) <$> mapM (tyRank r) ts

tyRank :: [(String, Int)] -> Ty -> Maybe Int
tyRank r t = case t of
  TyFloat      -> Just 0
  TyInt        -> Just 0
  TyBool       -> Just 0
  TyTuple a b  -> max <$> tyRank r a <*> tyRank r b
  TyEither a b -> max <$> tyRank r a <*> tyRank r b
  TyList a     -> tyRank r a
  TyADT m      -> lookup m r
  _            -> Nothing

-- | The constructors a leaf of @n@ may use: those whose fields all rank
-- strictly below @n@, so building leaves of the fields terminates.
leafCtors :: HasADTs => String -> [(String, [(String, Ty)])]
leafCtors n = case lookup n ranks of
  Nothing -> []
  Just k  -> [ ctor | ctor@(_, fs) <- adtCtors n
                    , all (maybe False (< k) . tyRank ranks . snd) fs ]
  where ranks = adtRanks

-- | A constructor's owning type and field types.
ctorInfo :: HasADTs => String -> Maybe (String, [Ty])
ctorInfo c = listToMaybe
  [ (n, map snd fs) | n <- adtNames, (c', fs) <- adtCtors n, c' == c ]

-- | A field accessor's owning type, constructor, field type, and whether that
-- constructor is the type's only one (in which case the accessor is total).
fieldInfo :: HasADTs => String -> Maybe (String, String, Ty, Bool)
fieldInfo f = listToMaybe
  [ (n, c, t, length (adtCtors n) == 1)
  | n <- adtNames, (c, fs) <- adtCtors n, (f', t) <- fs, f' == f ]

-- | The type a constructor test (@isRed@) tests for.
testInfo :: HasADTs => String -> Maybe String
testInfo t = listToMaybe
  [ n | n <- adtNames, (c, _) <- adtCtors n, "is" ++ c == t ]

-- | The type a predefined name (constructor, accessor or test) belongs to.
adtOfName :: HasADTs => String -> Maybe String
adtOfName nm = case (ctorInfo nm, fieldInfo nm, testInfo nm) of
  (Just (n, _), _, _)          -> Just n
  (_, Just (n, _, _, _), _)    -> Just n
  (_, _, Just n)               -> Just n
  _                            -> Nothing

-- | The same program, declaring exactly the types it uses, out of its own
-- declarations and the pool (its own winning on a name clash, so a shrunk
-- pool type stays shrunk). Used: those whose constructors, accessors or tests
-- appear in any declaration, those a neural declaration's type mentions, and
-- (closing over field types) those those types mention. A draw using none
-- declares none, so every pre-M4 shape compiles exactly the program it did.
withADTs :: Program -> Program
withADTs p = declareUsed (adts p ++ [ d | d <- adtPool, dataName d `notElem` map dataName (adts p) ]) p

-- | 'withADTs' out of an explicit candidate list, kept in its order.
declareUsed :: [ADTDecl] -> Program -> Program
declareUsed cands p = p { adts = [ d | d <- cands, dataName d `elem` used ] }
  where used = let ?adts = cands in usedADTs p

usedADTs :: HasADTs => Program -> [String]
usedADTs p = nub (direct ++ concatMap adtReach direct)
  where
    direct = nub $
      [ n | (_, e) <- functions p, nm <- injFNamesOf e, Just n <- [adtOfName nm] ]
      ++ [ n | (_, rt, _) <- neurals p, n <- adtsOfRType rt ]
    adtsOfRType rt = case rt of
      TADT n      -> [ n | n `elem` adtNames ]
      TArrow a b  -> adtsOfRType a ++ adtsOfRType b
      Tuple a b   -> adtsOfRType a ++ adtsOfRType b
      TEither a b -> adtsOfRType a ++ adtsOfRType b
      ListOf a    -> adtsOfRType a
      _           -> []

-- | Productions for an ADT target: one constructor application per
-- constructor, sharing a single slot (see 'arrowProds' for why slots are
-- rationed). Every field is generated at a strictly smaller size than the
-- node, a unary recursive constructor included, which is what keeps
-- generation finite.
adtCtorProds :: HasADTs => TyEnv -> String -> Int -> [Gen Expr]
adtCtorProds env n sz =
  [ oneof [ injF c <$> mapM (\(_, t) -> genTypedExprIn env t ((sz - 1) `div` max 1 (length fs))) fs
          | (c, fs) <- adtCtors n ]
  | not (null (adtCtors n)) ]

-- | The size below which the ADT eliminators do not fire.
adtElimSize :: Int
adtElimSize = 3

-- | Eliminators reaching @ty@ through an in-scope type, sharing one slot: a
-- field projection for every field of type @ty@, and at a 'TyBool' target a
-- constructor test for every constructor.
--
-- A field of a multi-constructor type is projected only under its own
-- constructor test, @let v = \<value\> in if isC v then f v else \<alt\>@.
-- Unguarded, it is the ADT twin of @head []@ -- 'PredefinedFunctions' states
-- the accessor's applicability as exactly that test -- and a generator
-- emitting partial applications measures the interpreter's error path, not
-- the compiler. Binding the value first is what keeps the test and the
-- projection reading *one* draw.
adtElimProds :: HasADTs => TyEnv -> Ty -> Int -> [Gen Expr]
adtElimProds env ty n
  | n < adtElimSize || null opts = []
  | otherwise = [oneof opts]
  where
    half = n `div` 2
    opts = projections ++ tests
    projections =
      [ if sole
          then (\x -> injF f [x]) <$> genTypedExprIn env (TyADT owner) (n - 1)
          else do
            let v    = freshName env
                env' = (v, TyADT owner) : env
            val <- genTypedExprIn env (TyADT owner) half
            alt <- genTypedExprIn env' ty half
            return $ letIn v val
                   $ ifThenElse (injF ("is" ++ c) [varE v]) (injF f [varE v]) alt
      | owner <- adtNames
      , (c, fs) <- adtCtors owner
      , (f, fty) <- fs
      , fty == ty
      , let sole = length (adtCtors owner) == 1
      ]
    tests =
      [ (\x -> injF ("is" ++ c) [x]) <$> genTypedExprIn env (TyADT owner) (n - 1)
      | ty == TyBool, owner <- adtNames, (c, _) <- adtCtors owner ]

-- | Every field projection of a multi-constructor type the program declares,
-- anywhere in the program, whose argument is not a variable an enclosing
-- @if@'s condition tests for that constructor (on the then-arm) -- i.e. every
-- projection that may be evaluated on a value built by another constructor.
-- The generator emits none ('adtElimProds'), and the shrinker refuses to make
-- one ('shrinkTypedProgram'): collapsing @if isLink v then lv v else e@ onto
-- its then-arm is well-typed and smaller, and turns any failing draw into the
-- accessor's own error, which the first Aspirational run of milestone M4
-- duly minimized a crash to.
unguardedProjections :: Program -> [String]
unguardedProjections p = concatMap (go [] . snd) (functions p)
  where
    multiCtorFields =
      [ (f, c) | d <- adts p, length (constructors d) > 1
               , (c, fs) <- constructors d, (f, _) <- fs ]
    go :: [(String, String)] -> Expr -> [String]
    go g e = case node e of
      IfThenElse c t f
        | InjF (Named tst) [x] <- node c, Var v <- node x, Just ctor <- stripPrefix "is" tst
        -> go g c ++ go ((v, ctor) : g) t ++ go g f
      InjF (Named f) args
        | Just ctor <- lookup f multiCtorFields
        , not (case args of
                 [x] | Var v <- node x -> (v, ctor) `elem` g
                 _ -> False)
        -> f : concatMap (go g) args
      _ -> concatMap (go g) (children e)

-- ---------------------------------------------------------------------------
-- Generating declarations.

-- | A program's declaration context: each pool type with probability one in
-- three, then zero to three generated ones -- the last two of them, one
-- context in four, a mutually recursive pair while 'generateMutualPairs' is
-- on. Checked against 'SPLL.Validator' as declarations, so a name the
-- compiler would refuse is a redraw rather than a draw every property then
-- discards.
genADTDecls :: Gen [ADTDecl]
genADTDecls = (do
  seeds  <- filterM (const (frequency [(1, pure True), (2, pure False)])) adtPool
  k      <- frequency [(2, pure 0), (4, pure 1), (3, pure 2), (2, pure (3 :: Int))]
  mutual <- frequency [(3, pure False), (1, pure True)]
  fresh  <- if generateMutualPairs && mutual && k >= 2
              then do pre  <- genSequential seeds (k - 2)
                      pair <- genMutualPair (seeds ++ pre)
                      return (pre ++ pair)
              else genSequential seeds k
  return (seeds ++ fresh)) `suchThat` declsValid
  where
    genSequential _ 0 = pure []
    genSequential ctx i = do
      tname <- genTypeName (takenNames ctx)
      d <- genADTBody ctx tname []
      (d :) <$> genSequential (ctx ++ [d]) (i - 1)

-- | Do these declarations validate, as the declarations of a trivial program?
declsValid :: [ADTDecl] -> Bool
declsValid ds = validateProgram (Program [("main", constB True)] [] ds [] []) == Right ()

-- | Off: a program using a mutually recursive pair of types does not finish
-- compiling -- @data A = A0 | A1 ab::B; data B = B0 | B1 ba::A@ with @main =
-- A0@, or @main = isA1 (head [A0])@, never returns (internal-docs
-- @mutually-recursive-adt-hangs-compiler@; the first runs of this generator
-- found it within a few hundred draws). A hang reads as a timeout to every
-- property, so generating the shape would only re-find a filed bug on every
-- run while starving the budgets -- the reason milestone M4 does not
-- generate the diverging scalar recursion either. Turn on when that bug is
-- fixed; 'genMutualADTPair' is pinned meanwhile so the generator does not
-- rot.
generateMutualPairs :: Bool
generateMutualPairs = False

-- | A mutually recursive pair over the pool, for the pin that keeps
-- 'genMutualPair' working while 'generateMutualPairs' is off.
genMutualADTPair :: Gen [ADTDecl]
genMutualADTPair = genMutualPair adtPool

-- | Two types each holding the other in a non-first constructor.
genMutualPair :: [ADTDecl] -> Gen [ADTDecl]
genMutualPair ctx = do
  a  <- genTypeName (takenNames ctx)
  b  <- genTypeName (takenNames ctx ++ [a])
  da <- genADTBody' ctx [b] a [b]
  db <- genADTBody (ctx ++ [da]) b [a]
  return [da, db]

genADTBody :: [ADTDecl] -> String -> [String] -> Gen ADTDecl
genADTBody ctx = genADTBody' ctx []

-- | One declaration named @tname@ over the context @ctx@. The first
-- constructor's fields only use @ctx@'s types (all grounded), so the type has
-- a finite leaf; the others may also use the type itself and @partners@, and
-- each partner gets one extra constructor holding it. @avoid@ are names
-- reserved for declarations still to come.
genADTBody' :: [ADTDecl] -> [String] -> String -> [String] -> Gen ADTDecl
genADTBody' ctx avoid tname partners = do
  nctors <- frequency [(2, pure 1), (3, pure 2), (3, pure 3), (2, pure 4), (1, pure (5 :: Int))]
  let ground = map dataName ctx
  firstAr <- if nctors == 1
               then frequency [(1, pure 0), (3, pure 1), (3, pure 2), (2, pure 3), (1, pure (4 :: Int))]
               else frequency [(3, pure 0), (2, pure 1), (2, pure 2)]
  firstTys <- vectorOf firstAr (genFieldTy ground [])
  restTys  <- vectorOf (nctors - 1) $ do
    ar <- frequency [(3, pure 0), (3, pure 1), (3, pure 2), (1, pure (3 :: Int))]
    vectorOf ar (genFieldTy ground (tname : partners))
  let tyss = firstTys : restTys ++ [ [TyADT q] | q <- partners ]
  (ctors, _) <- foldM (\(acc, taken) tys -> do
      c <- genCtorName tname taken
      (fs, taken') <- foldM (\(fa, tk) t -> do
          f <- genFieldName tk
          return (fa ++ [(f, tyToRType t)], tk ++ [f])) ([], taken ++ [c, "is" ++ c]) tys
      return (acc ++ [(c, fs)], taken')) ([], takenNames ctx ++ avoid) tyss
  let selfRec = any (any ((== TADT tname) . snd) . snd) ctors
  depth <- if selfRec then frequency [(1, pure Nothing), (2, Just <$> choose (1, 3))] else pure Nothing
  return (ADTDecl tname ctors depth)

-- | A field type: mostly scalars, sometimes a structure of scalars, an
-- earlier (grounded) type, a list of a type, or one of @recs@ (the type
-- itself, or its mutual partner).
genFieldTy :: [String] -> [String] -> Gen Ty
genFieldTy ground recs = frequency $
  [ (6, scalar)
  , (1, TyTuple <$> scalar <*> scalar)
  , (1, TyEither <$> scalar <*> scalar)
  , (1, TyList <$> scalar) ]
  ++ [ (2, TyADT <$> elements ground) | not (null ground) ]
  ++ [ (3, TyADT <$> elements recs) | not (null recs) ]
  ++ [ (1, TyList . TyADT <$> elements (ground ++ recs)) | not (null (ground ++ recs)) ]
  where scalar = elements [TyFloat, TyInt, TyBool]

-- | Every name a declaration list claims: type names, constructors, their
-- tests and fields.
takenNames :: [ADTDecl] -> [String]
takenNames ds = concat
  [ dataName d : concat [ c : ("is" ++ c) : map fst fs | (c, fs) <- constructors d ] | d <- ds ]

genTypeName :: [String] -> Gen String
genTypeName taken = genName upperWords hazardUpper `suchThat` nameOk taken

-- | A constructor name; one in eight is the type's own name (@data Box = Box
-- ...@), which keeps the type and value namespaces honest.
genCtorName :: String -> [String] -> Gen String
genCtorName tname taken =
  frequency [ (1, pure tname), (7, genName upperWords hazardUpper) ] `suchThat` ctorOk
  where ctorOk c = nameOk taken c && nameOk taken ("is" ++ c)

genFieldName :: [String] -> Gen String
genFieldName taken = genName lowerWords hazardLower `suchThat` nameOk taken

-- | A plain word, a plain word with a number, or (one in seven) a name a
-- target language or its runtime claims.
genName :: [String] -> [String] -> Gen String
genName plain hazard = frequency
  [ (4, elements plain)
  , (2, (++) <$> elements plain <*> (show <$> choose (2, 99 :: Int)))
  , (1, elements hazard) ]

-- | A generated name must be new, not a keyword, predefined function or
-- reserved name, not a name the generator itself uses for a declaration or
-- binder, and not a pool name (so 'withADTs' can never confuse the two).
nameOk :: [String] -> String -> Bool
nameOk taken nm =
  not (null nm)
  && nm `notElem` taken
  && nm `notElem` reserved
  && nm `notElem` map fst (globalFEnv [])
  && isNothing (reservedIdentifierReason nm)
  && nm `notElem` generatorNames
  && nm `notElem` takenNames adtPool
  && nm `notElem` knownCollidingNames
  && not (binderLike nm)
  where
    generatorNames = [ "main", helperName, helperParam, loopName, loopParam, loopHole
                     , neuralName, neuralSymName, "s", "k", arrowLeafParam, "Uniform", "Normal" ]
    binderLike n = or [ case stripPrefix pfx n of
                          Just rest -> all isDigit rest
                          Nothing   -> False
                      | pfx <- ["v", "h", "r", "d", "va", "vb", "p"] ]

-- | Target-language names a generated declaration may *not* use, because a
-- backend breaks on them: a constructor @Any@ emits an @isAny@ test that
-- shadows the runtimes' own @isAny@ (Python recurses forever, Julia
-- overflows its stack), and a constructor @Base@ redefines Julia's @Base@
-- module, so the module does not load. Filed as internal-docs
-- @adt-constructor-name-shadows-runtime@, found by this generator's first
-- Slow runs and confirmed by sweeping every hazard name below through both
-- backends (the only two that broke). Excluded rather than re-found on every
-- run, like the hangs 'generateMutualPairs' avoids; drop them from here when
-- that bug is fixed.
knownCollidingNames :: [String]
knownCollidingNames = ["Any", "Base"]

upperWords, hazardUpper, lowerWords, hazardLower :: [String]
upperWords =
  [ "Shape", "Item", "Node", "Cell", "Card", "Coin", "Box", "Tag", "Opt", "Tree"
  , "Path", "Ring", "Slot", "Grid", "Pile", "Leaf", "Nil", "Wrap", "Pick", "Val"
  , "Empty", "Full", "Unit", "Lo", "Hi", "Mid", "Edge", "Solo", "Duo", "Trio"
  , "Step", "Halt", "Done", "More", "On", "Off", "Kind", "Sort", "Branch", "Tip" ]
-- Names Python, Julia or the runtimes bind: 'SPLL.ReservedNames' lists the
-- ones the backends escape, and a generated declaration is how they get used
-- as constructors at all.
hazardUpper =
  [ "T", "Left", "Right", "Module", "Iterable", "None", "True", "False", "Nothing"
  , "Some", "Int", "Float", "Bool", "String", "Tuple", "Any", "Type", "Base"
  , "Vector", "Array", "Symbol", "Missing", "Exception", "Function", "EnumBatch"
  , "InferenceList", "EmptyInferenceList", "Dict", "Set", "Union", "Ref", "Inf"
  , "NaN", "Main", "Core", "Float64", "Int64", "Char", "Real", "Number", "Tensor" ]
lowerWords =
  [ "val", "x", "y", "w", "lo", "hi", "size", "flag", "kid", "rest", "nxt"
  , "item", "tag", "score", "mass", "elem", "body", "key", "count", "weight"
  , "label", "info", "left", "right", "lhs", "rhs", "pos", "amount", "idx", "level" ]
hazardLower =
  [ "len", "sum", "type", "id", "list", "map", "min", "max", "abs", "round"
  , "print", "def", "end", "function", "begin", "local", "global", "in", "is"
  , "not", "lambda", "self", "cls", "torch", "math", "value", "inf", "nan", "pi"
  , "struct", "module", "let", "do", "try", "catch", "object", "range", "float"
  , "int", "bool", "tuple", "dict", "set", "nothing", "missing", "isa", "typeof"
  , "eltype", "length", "first", "last", "zip", "filter", "sort", "string"
  , "vec", "rand", "randn", "model", "forward", "args", "kwargs", "result"
  , "super", "next", "iter", "hash", "format", "input", "open", "exit", "quote"
  , "macro", "export", "using", "import", "mutable", "where", "true", "false" ]

-- ---------------------------------------------------------------------------
-- Coverage and shrinking of declarations.

-- | Every declaration's shape, as a base label and a list of features, for the
-- coverage tabulation. Names are not shapes, so a run's table stays a table.
adtShapes :: [ADTDecl] -> [(String, [String])]
adtShapes ds = let ?adts = ds in map adtShapeOf ds

adtShapeOf :: HasADTs => ADTDecl -> (String, [String])
adtShapeOf d = (base, features)
  where
    n  = dataName d
    cs = adtCtors n
    fieldTys = [ t | (_, fs) <- cs, (_, t) <- fs ]
    base
      | length cs == 1 && null fieldTys = "unit"
      | length cs == 1                  = "record"
      | null fieldTys                   = "enumeration"
      | otherwise                       = "mixed arity"
    selfFields = maximum (0 : [ length (filter (== TyADT n) (map snd fs)) | (_, fs) <- cs ])
    features =
      [ "pool" | d `elem` adtPool ]
      ++ [ "more than three constructors" | length cs > 3 ]
      ++ [ "self-recursive" | selfFields == 1 ]
      ++ [ "several recursive fields" | selfFields > 1 ]
      ++ [ "recursive through a list" | TyList (TyADT n) `elem` fieldTys ]
      ++ [ "mutually recursive" | isMutualADT n ]
      ++ [ "ADT field" | any (\t -> any (/= n) (adtsInTy t)) fieldTys ]
      ++ [ "structured field" | any isStructuredField fieldTys ]
      ++ [ "Int, Bool and Float fields" | all (`elem` fieldTys) [TyInt, TyBool, TyFloat] ]
      ++ [ "depth" | isJust (adtDepth d) ]
      ++ [ "constructor named like its type" | n `elem` map fst cs ]
      ++ [ "target-language name" | any (`elem` (hazardUpper ++ hazardLower)) (takenNames [d]) ]
    isStructuredField t = case t of
      TyTuple{}  -> True
      TyEither{} -> True
      TyList{}   -> True
      _          -> False

-- | The size a declaration contributes to a draw: one per type, constructor
-- and field. Part of TestFuzz's shrinker measure since declarations shrink.
adtDeclSize :: ADTDecl -> Int
adtDeclSize d = 1 + sum [ 1 + length fs | (_, fs) <- constructors d ]

-- | Shrinks of the program's declarations: drop a constructor nothing names
-- (not built, tested, or read through one of its fields), or drop a field
-- whose accessor nothing names, removing that argument from every
-- application of its constructor. Unused declarations need no rule of their
-- own: every candidate goes through 'withADTs', which drops them.
--
-- Termination and typing hold by construction. A dropped constructor was not
-- built anywhere, so no value changes; a candidate leaving some type without
-- a finite value ('adtRanks') is refused. A dropped field takes its argument
-- subtree with it, which can only remove calls, never move one -- so a
-- recursive declaration stays 'recursionSafe' and still makes at most one
-- call per step. A type that is no longer directly self-recursive loses its
-- @depth@ with it.
adtDeclShrinks :: Program -> [Program]
adtDeclShrinks p = filter grounded dropCtors ++ dropFields
  where
    used = nub (concatMap (injFNamesOf . snd) (functions p))
    ctorUnused (c, fs) = c `notElem` used && ("is" ++ c) `notElem` used
                         && all ((`notElem` used) . fst) fs
    replaceD p0 d' = p0 { adts = [ if dataName d == dataName d' then d' else d | d <- adts p0 ] }
    grounded p' = let ?adts = adts p' in all (\n -> isJust (lookup n adtRanks)) adtNames
    settleDepth d
      | any (any ((== TADT (dataName d)) . snd) . snd) (constructors d) = d
      | otherwise = d { adtDepth = Nothing }
    dropCtors =
      [ replaceD p (settleDepth d { constructors = dropAt i (constructors d) })
      | d <- adts p, length (constructors d) > 1
      , (i, ctor) <- zip [0 ..] (constructors d), ctorUnused ctor ]
    dropFields =
      [ (replaceD p (settleDepth d { constructors = [ if c' == c then (c', dropAt i fs) else (c', fs')
                                                    | (c', fs') <- constructors d ] }))
          { functions = [ (nm, dropArg c (length fs) i e) | (nm, e) <- functions p ] }
      | d <- adts p, (c, fs) <- constructors d
      , (i, (f, _)) <- zip [0 ..] fs, f `notElem` used ]

dropAt :: Int -> [a] -> [a]
dropAt i xs = take i xs ++ drop (i + 1) xs

-- | Remove argument @i@ from every application of constructor @c@ (of arity
-- @arity@), bottom-up.
dropArg :: String -> Int -> Int -> Expr -> Expr
dropArg c arity i e =
  let e' = withChildren e (map (dropArg c arity i) (children e))
  in case node e' of
       InjF (Named c') args | c' == c, length args == arity
         -> Expr (ann e') (InjF (Named c) (dropAt i args))
       _ -> e'

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

-- ---------------------------------------------------------------------------
-- Recognising a generated function value (task fuzz-arrow-generator-coverage).

-- | How much of the arrow surface a draw reaches. Ordered, so a whole-program
-- verdict is the maximum over its nodes -- by how much machinery the shape
-- puts in front of the compiler, not by how interesting it is.
--
-- 'NoArrow' is not "no 'Apply' node": every @let@ is one
-- ('SPLL.Prelude.letIn'), so a draw with no function value in it at all still
-- contains applications and lambdas. What the other three rungs have in
-- common is a callee the compiler cannot read off as a lambda literal
-- standing right there.
data ArrowShape
  = NoArrow      -- ^ every application is a @let@: a literal lambda called
                 --   where it is written
  | AppliedFun   -- ^ a *named* function value is applied -- a top-level
                 --   function, or a variable bound to a function value. The
                 --   one callee shape 'SPLL.CalleeNormalize' leaves for
                 --   forward chaining to resolve
  | SelectedFun  -- ^ the callee is *computed*: an @if@ between two function
                 --   values, or one projected out of a tuple or a list
  | CurriedFun   -- ^ two arguments reach one function value
  deriving (Show, Eq, Ord)

-- | A syntactic classifier, like 'letShapeOf' and for the same reason: the
-- compiler exposes no hook saying which callee path ran.
arrowShapeOf :: Expr -> ArrowShape
arrowShapeOf e = maximum (here : map arrowShapeOf (children e))
  where
    here = case node e of
      Apply f _
        -- A @let@. Classified first, so that @(let x = v in b) a@ -- applying
        -- the *result* of a let -- is not miscounted as a curried call.
        | Just _ <- asLet e               -> NoArrow
        | Apply{} <- node f
        , Nothing <- asLet f              -> CurriedFun
        | Var{} <- node f                 -> AppliedFun
        | otherwise                       -> SelectedFun
      _ -> NoArrow

-- | The whole program's verdict, which for a 'genHelperProgram' draw has to
-- include the declaration as well as @main@.
arrowShapeOfProgram :: Program -> ArrowShape
arrowShapeOfProgram p = maximum (NoArrow : map (arrowShapeOf . snd) (functions p))

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
tyToRType (TyArrow a b)  = TArrow (tyToRType a) (tyToRType b)
tyToRType (TyADT n)      = TADT n

-- | Partial inverse of 'tyToRType', for reading a neural declaration's target
-- back out of a 'Program'. 'Nothing' for anything the typed generator cannot
-- build inhabitants of.
rTypeToTy :: HasADTs => RType -> Maybe Ty
rTypeToTy TFloat        = Just TyFloat
rTypeToTy TInt          = Just TyInt
rTypeToTy TBool         = Just TyBool
rTypeToTy (Tuple a b)   = TyTuple  <$> rTypeToTy a <*> rTypeToTy b
rTypeToTy (TEither a b) = TyEither <$> rTypeToTy a <*> rTypeToTy b
rTypeToTy (ListOf a)    = TyList   <$> rTypeToTy a
rTypeToTy (TADT n)
  | n `elem` adtNames = Just (TyADT n)
rTypeToTy _             = Nothing

-- | Does this type's partition plan consist of discrete slots only? Only then
-- does an @of@ clause change anything: 'SPLL.Analysis.annotateEnumsProg'
-- declines to tag a 'MultiValue' with a continuous leaf, because enumerating
-- it would sum over the discrete residue and silently drop the continuous
-- mass. A @Float@ anywhere in the target therefore makes @of _@ a no-op, and
-- the materialized-twin oracle vacuous.
tyAllDiscrete :: HasADTs => Ty -> Bool
tyAllDiscrete TyBool         = True
tyAllDiscrete (TyTuple a b)  = tyAllDiscrete a && tyAllDiscrete b
tyAllDiscrete (TyEither a b) = tyAllDiscrete a && tyAllDiscrete b
-- A non-recursive ADT whose fields are all discrete: @Hue@ (no fields at all).
-- A recursive one (directly or mutually) is excluded even with discrete
-- fields -- its plan is depth-truncated, so the two engines answer over
-- different supports. Checked first, which is also what makes the descent into
-- field types terminate: below an acyclic type every type is visited once.
tyAllDiscrete (TyADT n)      = not (isCyclicADT n)
                               && and [ all (tyAllDiscrete . snd) fs | (_, fs) <- adtCtors n ]
tyAllDiscrete _              = False

-- | Target types 'SPLL.Lang.Lang.autoDeriveMultiValue' can produce a plan for
-- with no annotation: @Float@ (one continuous slot), @Bool@ (a two-way
-- discrete), and tuples\/Eithers of those. Not @Int@ (unbounded domain, needs
-- explicit values), not lists. Since milestone M4 also the pool ADTs @Hue@
-- and @Pt@ (see the frequency table).
--
-- Depth-bounded hard: every leaf costs logits (2 for a continuous slot, 2 for
-- a Bool, plus a selector per Either), and the mock network has to produce a
-- vector of exactly the plan's width on every single draw.
genAutoNeuralTy :: HasADTs => Int -> Gen Ty
genAutoNeuralTy n
  | n <= 0 = elements [TyFloat, TyBool]
  | otherwise = frequency $
      [ (5, elements [TyFloat, TyBool])
      , (2, TyTuple  <$> rec <*> rec)
      , (1, TyEither <$> rec <*> rec)
      ]
      -- Milestone M4: the in-scope ADTs a plan auto-derives for
      -- ('neuralADTs') -- of the pool, @Hue@ and @Pt@. Not @Mix@ (an Int
      -- field) and not @Chain@ (each unrolled level adds a continuous slot,
      -- which every draw pays for in mock logits).
      ++ [ (1, TyADT <$> elements ns) | let ns = neuralADTs False, not (null ns) ]
  where rec = genAutoNeuralTy (n - 1)

-- | The in-scope types a neural target may be without an explicit @of@
-- clause: not recursive (directly or mutually), every field auto-derivable
-- ('SPLL.Lang.Lang.autoDeriveMultiValue': Float, Bool, tuples and Eithers of
-- those, and nested types of the same kind) -- only Bool ones when
-- @discreteOnly@ -- and a plan at most 'neuralADTWidth' slots wide.
neuralADTs :: HasADTs => Bool -> [String]
neuralADTs discreteOnly =
  [ n | n <- adtNames, ok (TyADT n), maybe False (<= neuralADTWidth) (planWidth (TyADT n)) ]
  where
    ok t = case t of
      TyFloat      -> not discreteOnly
      TyBool       -> True
      TyTuple a b  -> ok a && ok b
      TyEither a b -> ok a && ok b
      TyADT m      -> not (isCyclicADT m) && all (ok . snd) (concatMap snd (adtCtors m))
      _            -> False
    planWidth t = case t of
      TyFloat      -> Just 1
      TyBool       -> Just 1
      TyTuple a b  -> (+) <$> planWidth a <*> planWidth b
      TyEither a b -> (\x y -> x + y + 1) <$> planWidth a <*> planWidth b
      TyADT m | not (isCyclicADT m)
                   -> (1 +) . sum <$> mapM (planWidth . snd) (concatMap snd (adtCtors m))
      _            -> Nothing

-- | Cap on a generated neural ADT target's plan, counted as one per slot plus
-- one per selector: @Pt@ is 3. Every draw pays the width in mock logits.
neuralADTWidth :: Int
neuralADTWidth = 6

-- | 'genAutoNeuralTy' restricted to 'tyAllDiscrete' targets, for the draws
-- whose @of@ clause is supposed to *do* something.
genDiscreteNeuralTy :: HasADTs => Int -> Gen Ty
genDiscreteNeuralTy n
  | n <= 0 = pure TyBool
  | otherwise = frequency $
      [ (4, pure TyBool)
      , (2, TyTuple  <$> rec <*> rec)
      , (1, TyEither <$> rec <*> rec)
      ]
      ++ [ (1, TyADT <$> elements ns) | let ns = neuralADTs True, not (null ns) ]
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
-- 'AnnInts' the k-way categorical that @Bool@ alone cannot produce. (Since
-- M4 an ADT target such as @Hue@ is a second way to a plan slot wider than
-- two.)
genTypedNeuralDecl :: HasADTs => Gen (NeuralDecl, Ty)
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
genNeuralProgram = withGeneratedADTs genNeuralProgramIn

genNeuralProgramIn :: HasADTs => Gen Program
genNeuralProgramIn = do
  (decl, nty) <- genTypedNeuralDecl
  ty <- genTyIn tyDepth
  body <- sized (genNeuralMain nty ty)
  return $ declareHere $ Program [("main", body)] [decl] [] [] []

-- | The body of a neural @main@, at a given network target type and program
-- result type.
genNeuralMain :: HasADTs => Ty -> Ty -> Int -> Gen Expr
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
genNeuralCore :: HasADTs => TyEnv -> String -> Ty -> Ty -> Int -> Gen Expr
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
genNeuralObs :: HasADTs => Expr -> Ty -> Gen Expr
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
-- A record is projected (its accessors are total); any other ADT is tested
-- for a constructor, which is the ADT spelling of 'sisLeft'.
genNeuralObs e (TyADT n) = case adtCtors n of
  [(_, fs@(_ : _))] -> oneof [ genNeuralObs (injF f [e]) t | (f, t) <- fs ]
  ctors             -> elements [ injF ("is" ++ c) [e] | (c, _) <- ctors ]
-- Neither is a neural target type ('genAutoNeuralTy' emits neither, and an
-- Int target is always a bare leaf), so these exist only to keep the function
-- total.
genNeuralObs e (TyList _) = pure (isNull e)
genNeuralObs _ TyAny      = constB <$> arbitrary
-- A network's target type is never an arrow: neither 'genAutoNeuralTy' nor
-- 'genDiscreteNeuralTy' can draw one, and 'autoDeriveMultiValue' has no plan
-- for a function anyway. Answering with a constant keeps this total rather
-- than adding an 'error' for a case the types cannot rule out.
genNeuralObs _ TyArrow{}  = constB <$> arbitrary

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
typedMainCore :: HasADTs => Program -> Maybe (TyEnv, Expr)
typedMainCore p = fst <$> typedMainParts p

-- | The generated core of @main@, for consumers that only want the expression.
typedMainCoreExpr :: Program -> Maybe Expr
typedMainCoreExpr p = inProgram p (snd <$> typedMainCore p)

-- | The 'Ty' of the generated core of @main@, recovered in the scope the core
-- actually sits in -- which for a neural draw is non-empty.
typedMainCoreTy :: Program -> Maybe Ty
typedMainCoreTy p = inProgram p (typedMainCore p >>= \(env, core) -> tyOfTypedExprIn env core)

-- | 'typedMainCore' plus the rebuilder that puts a replacement core back
-- inside whatever wrapper it came out of.
typedMainParts :: HasADTs => Program -> Maybe ((TyEnv, Expr), Expr -> Expr)
typedMainParts p = do
  body <- lookup "main" (functions p)
  case node body of
    Lambda sym inner
      | Just (s, val, core) <- asLet inner
      , ReadNN nn _ <- node val
      , Just (_, nrt, _) <- find ((== nn) . fst3) (neurals p)
      , Just nty <- rTypeToTy (neuralTarget nrt)
      -> Just ( ((s, nty) : helperEnv p, core)
              , \core' -> Expr (ann body) (Lambda sym (letIn s val core')) )
    _ -> Just ((helperEnv p, body), id)
  where
    fst3 (a, _, _) = a
    neuralTarget (TArrow _ t) = t
    neuralTarget t            = t

-- | Every top-level function other than @main@, with its arrow type recovered.
-- A 'genHelperProgram' draw's @main@ is a call to one of these, so without
-- them in scope its body recovers nothing and the whole draw would silently
-- stop shrinking.
--
-- A declaration is a bare 'Lambda', and nothing on it records what its
-- parameter was generated at -- so the parameter type is taken from **the
-- call site in @main@**, the same push-down 'tyOfApplied' does at an ordinary
-- application. That is not a refinement but the difference between recovering
-- and not: a helper that *destructures* its parameter (@fst h0@, @head h0@)
-- recovers nothing at all under a free parameter, since the eliminators
-- demand a concrete shape, and those are a good half of the draws.
--
-- Where @main@ does not apply the function -- it cannot happen in a generated
-- draw, but this is total over any 'Program' -- the free-parameter reading is
-- the fallback, which is what a function value read but not called recovers
-- as anyway.
--
-- Two passes, for milestone M4's recursive declarations: the first types every
-- declaration with none of them in scope, the second again with the first
-- pass's answers in scope. A recursive body's own call recovers only in the
-- second -- in the first, the @if@ around it recovers from the base arm alone,
-- which is what makes the second pass possible.
helperEnv :: HasADTs => Program -> TyEnv
helperEnv p = pass (pass [])
  where
    pass scope =
      [ (nm, t)
      | (nm, e) <- functions p
      , nm /= "main"
      , Just t <- [declaredTy scope nm e]
      ]
    declaredTy scope nm e = case node e of
      Lambda x body
        | Just aty <- callSiteArgTy nm
        -> TyArrow aty <$> tyOfTypedExprIn ((x, aty) : scope) body
      _ -> tyOfTypedExprIn scope e
    -- Recovered in the *empty* scope, which both terminates and is right: an
    -- argument mentioning the function being typed cannot pin its parameter.
    --
    -- Every call site is tried, not only the first, and a site through a
    -- @let@ alias counts (@let v = helper in v e@, a 'genFunctionLet' draw
    -- with the helper as its function value): where the direct call's
    -- argument mentions the helper itself, the alias's call may be the only
    -- one that recovers (task adt-generator-core-type-recoverable-flake).
    callSiteArgTy nm = do
      body <- lookup "main" (functions p)
      listToMaybe [ t | arg <- callSites nm body, Just t <- [tyOfTypedExprIn [] arg] ]

-- | 'appliedToAll', plus the arguments of every @let@-bound alias of @nm@
-- (@(\\v -> ... v a ...) nm@ contributes @a@).
callSites :: String -> Expr -> [Expr]
callSites nm e = appliedToAll nm e ++
  [ a | Just (x, val, body) <- map asLet (subExprs e)
      , Var v <- [node val], v == nm, x /= nm
      , a <- callSites x body ]
  where subExprs t = t : concatMap subExprs (children t)

-- | Every argument @nm@ is applied to in an expression, outermost first.
appliedToAll :: String -> Expr -> [Expr]
appliedToAll nm e = case node e of
  Apply f arg | Var v <- node f, v == nm -> arg : rest
  _ -> rest
  where rest = concatMap (appliedToAll nm) (children e)

-- | The same program with its neural declaration's @of@ clause flipped on or
-- off -- the materializing twin of a lazy draw, or the reverse.
--
-- 'Nothing' unless the flip actually changes the compilation path: exactly one
-- declaration, its target auto-derivable *and* free of continuous slots, and
-- its annotation either absent or @of _@. An explicit value list
-- ('AnnInts') is left alone -- its target does not auto-derive, so there is no
-- annotation-free twin to compare it against.
neuralTwin :: Program -> Maybe Program
neuralTwin p = inProgram p $ case neurals p of
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
genNeuralTwinProgram = withGeneratedADTs $ do
  nty <- genDiscreteNeuralTy neuralTyDepth
  ty  <- genTyIn tyDepth
  body <- sized (genNeuralMain nty ty)
  let decl = (neuralName, TArrow TSymbol (tyToRType nty), Nothing)
      lazyP = declareHere $ Program [("main", body)] [decl] [] [] []
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
tyOfTypedExpr e = withPool (tyOfTypedExprIn [] e)

tyOfTypedExprIn :: HasADTs => TyEnv -> Expr -> Maybe Ty
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
  -- An application: the argument's type pins the callee's parameter, so the
  -- node's type is whatever the callee returns *given that argument type*
  -- ('tyOfApplied'). A @let@ is this case with a literal lambda for the
  -- callee, which is how 'SPLL.Prelude.letIn' spells one.
  Apply f val         -> tyOfArgument env f val >>= \vty -> tyOfApplied env vty f
  -- A function value read somewhere other than at an application -- bound by
  -- a @let@, passed as an argument, chosen by an @if@. Nothing on a 'Lambda'
  -- node records what its parameter was bound at, so the parameter position
  -- stays free and the result is recovered under it. That is the same 'TyAny'
  -- contract @left@/@right@ already use for the component they do not pin.
  Lambda x body       -> TyArrow TyAny <$> tyOfTypedExprIn ((x, TyAny) : env) body
  _                   -> Nothing

-- | The type of applying @f@ to an argument of type @aty@.
--
-- The argument type is pushed *into* the callee rather than read off it,
-- which is the only way a lambda literal or an @if@ between two of them is
-- recoverable at all: neither node records its own parameter type, but at an
-- application the context knows it. Anything else must have a recoverable
-- arrow type of its own -- a variable bound to a function value, a top-level
-- function, or a nested application returning one.
tyOfApplied :: HasADTs => TyEnv -> Ty -> Expr -> Maybe Ty
tyOfApplied env aty = tyOfSpine env [aty]

-- | 'tyOfApplied' over a whole application spine: the type of applying @f@ to
-- arguments of the given types, innermost first.
--
-- A callee that is itself an application (@(f a) b@) adds its own argument to
-- the front of the spine rather than being recovered on its own, so a
-- curried literal lambda (@(\\x -> \\y -> neg y) a b@) has *both* its
-- parameters pushed in. Recovered on its own, the inner @\\y -> neg y@ would
-- have a free parameter, and a polymorphic catalog entry such as @neg@ matches
-- more than one row at 'TyAny' and recovers 'Nothing' -- the whole draw then
-- stops being recognised (task adt-generator-core-type-recoverable-flake).
tyOfSpine :: HasADTs => TyEnv -> [Ty] -> Expr -> Maybe Ty
tyOfSpine env [] f = tyOfTypedExprIn env f
tyOfSpine env tys@(aty : rest) f = case node f of
  Lambda x body    -> tyOfSpine ((x, aty) : env) rest body
  -- Both arms are applied to the same arguments, so each is pushed the same
  -- types and the results are joined -- the same treatment, for the same
  -- reason, that 'tyOfTypedExprIn' gives an @if@'s own arms.
  IfThenElse _ t g -> case (tyOfSpine env tys t, tyOfSpine env tys g) of
    (Just a, Just b)  -> tyJoin a b
    (Just a, Nothing) -> Just a
    (Nothing, mb)     -> mb
  Apply g a        -> tyOfArgument env g a >>= \t -> tyOfSpine env (t : tys) g
  _ -> tyOfTypedExprIn env f >>= peel tys
  where
    peel [] r                = Just r
    peel (_ : ts) (TyArrow _ r) = peel ts r
    peel _ _                 = Nothing

-- | The type of the argument @val@ that callee @f@ is applied to.
--
-- Ordinarily just @val@'s own recovered type. The exception is a @let@ that
-- binds a function value -- @(\\f -> f a) (\\x -> neg x)@, which is what
-- 'genFunctionLet' draws. Read as a value, the bound function has a free
-- parameter, and recovers either nothing (@neg@ over 'TyAny' matches two
-- catalog rows, see 'tyOfSpine') or a result that is 'TyAny' where it should
-- not be (@(\\a -> \\b -> b) e@ reads as @? -> ?@, and a @neg@ applied to
-- its call is again ambiguous). So where the body applies the bound name, its
-- parameter type is taken from **that call site**, the same push-down
-- 'helperEnv' does for a top-level helper applied in @main@: the first
-- argument the name is applied to that recovers in the outer scope. The
-- value's own reading is the fallback, for a function the body only passes
-- on (task adt-generator-core-type-recoverable-flake).
tyOfArgument :: HasADTs => TyEnv -> Expr -> Expr -> Maybe Ty
tyOfArgument env f val = case node f of
  Lambda x body
    | (t : _) <- [ TyArrow aty r
                 | arg <- appliedToAll x body
                 , Just aty <- [tyOfTypedExprIn env arg]
                 , Just r <- [tyOfApplied env aty val] ]
    -> Just t
  _ -> tyOfTypedExprIn env val

-- | Result type of an InjF application the typed generator can emit. The
-- structured entries are computed from the arguments rather than looked up:
-- @TCons@ is as wide as its components, the eliminators are as narrow as the
-- part of their argument's type they select, and @left@/@right@ pin only one
-- side of the Either they build (the other stays 'TyAny').
tyOfTypedInjF :: HasADTs => TyEnv -> String -> [Expr] -> Maybe Ty
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
-- @recip@, the half of @a / b@ the catalog does not own ('genTypedRec''s
-- division production). Without it every draw containing a division would be
-- unrecognised, and so unshrinkable.
tyOfTypedInjF env "recip" [x]    = tyOfTypedExprIn env x >>= \t -> case t of
  TyFloat -> Just TyFloat
  TyAny   -> Just TyFloat
  _       -> Nothing
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
-- Milestone M4: the in-scope ADTs' constructors, accessors and tests. Read off
-- the 'HasADTs' context, the same table generation draws from. A constructor checks its
-- arguments (each must be at least as general as its field's type), because
-- a constructor node's own type says nothing about them and the shrinker's
-- per-node re-typing would otherwise accept an argument of the wrong type.
tyOfTypedInjF env f args
  | Just (owner, ftys) <- ctorInfo f
  = if length ftys == length args
      then do argTys <- mapM (tyOfTypedExprIn env) args
              if and (zipWith (flip tyGeneralizes) ftys argTys)
                then Just (TyADT owner) else Nothing
      else Nothing
  | Just (owner, _, fty, _) <- fieldInfo f, [x] <- args
  = tyOfTypedExprIn env x >>= \t ->
      if t == TyADT owner || t == TyAny then Just fty else Nothing
  | Just owner <- testInfo f, [x] <- args
  = tyOfTypedExprIn env x >>= \t ->
      if t == TyADT owner || t == TyAny then Just TyBool else Nothing
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
tyOfTypedEitherTest :: HasADTs => TyEnv -> Expr -> Maybe Ty
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
      -- No ADT is in scope: the catalog is built from @globalFEnv []@.
      let ?adts = [] in
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
-- constructors enter 'globalFEnv' per declaration, and the pool ADTs
-- milestone M4 generates have their own, non-scalar productions
-- ('adtCtorProds', 'adtElimProds') and recovery cases.
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
-- Both positions join covariantly, including the parameter. The parameter of
-- a recovered arrow is not a declared domain that a caller must satisfy -- it
-- is whatever an application was seen to pin it to, and 'TyAny' when none
-- was. Joining two such observations is the same "fill in what the other side
-- knows" operation it is everywhere else.
tyJoin (TyArrow a b)  (TyArrow c d)  = TyArrow  <$> tyJoin a c <*> tyJoin b d
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
-- Covariant in the parameter too, for the reason 'tyJoin' gives: a free
-- parameter position means "no application pinned this", so a replacement
-- that leaves it free is more general, and one that commits it is not. The
-- shrink this admits is the one worth having -- @\\p -> 0@ replacing a
-- function of a known argument type, which is well-typed precisely because it
-- ignores the argument.
tyGeneralizes (TyArrow a b)  (TyArrow c d)  = tyGeneralizes a c && tyGeneralizes b d
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
typedLeaves t = withPool (typedLeavesIn t)

-- | 'typedLeaves' over the declarations in scope.
typedLeavesIn :: HasADTs => Ty -> [Expr]
typedLeavesIn TyFloat = [constF 0]
typedLeavesIn TyInt   = [constI 0]
typedLeavesIn TyBool  = [constB False, constB True]
-- No leaf is offered for a free position, and that propagates: a leaf for
-- @Either Float ?@ is @left 0@ and never @right <something>@, because
-- committing the unknown side to a concrete type is exactly the shrink that
-- would be ill-typed in the surrounding context.
typedLeavesIn TyAny   = []
typedLeavesIn (TyTuple a b) =
  [ tuple x y | x <- take 1 (typedLeavesIn a), y <- take 1 (typedLeavesIn b) ]
typedLeavesIn (TyEither a b) =
  [ left x  | x <- take 1 (typedLeavesIn a) ]
  ++ [ right y | y <- take 1 (typedLeavesIn b) ]
typedLeavesIn (TyList a) = [ cons x nul | x <- take 1 (typedLeavesIn a) ]
-- The first leaf constructor ('leafCtors') applied to the smallest field
-- values: @Red@, @MkPt 0 False@, @Zero@, @Stop@.
typedLeavesIn (TyADT n) = take 1
  [ injF c ls
  | (c, fs) <- leafCtors n
  , Just ls <- [mapM (listToMaybe . typedLeavesIn . snd) fs] ]
-- A constant function, which is closed and (being independent of its
-- argument) inhabits @TyArrow a b@ for every @a@ at once.
typedLeavesIn (TyArrow _ b) = [ arrowLeafParam #-># x | x <- take 1 (typedLeavesIn b) ]

-- | The smallest closed value of a declared type, under the given
-- declarations ('typedLeaves' at that type).
adtLeaf :: [ADTDecl] -> String -> Maybe Expr
adtLeaf ds n = let ?adts = ds in listToMaybe (typedLeavesIn (TyADT n))

-- | Type-preserving shrink for an expression produced by 'genTypedExpr'.
--
-- Every candidate has a strictly smaller node count and a 'Ty' that
-- 'tyGeneralizes' the node's own -- the *asymmetric* test, not a symmetric
-- compatibility/join one, which M1 used and which was too weak (see
-- 'tyGeneralizes'). So the result is well-founded and never hands the property
-- an ill-typed or ill-scoped program (either of which would be discarded,
-- minimizing nothing).
-- Candidates are re-uniquified, for the reason 'uniquifyBinders' gives about
-- generation: a shrink can *introduce* a binder. The constant-function leaf
-- ('typedLeaves' at an arrow type) is a lambda, so replacing two function
-- values with it puts two identically-named binders in one program, and
-- 'SPLL.Validator' rejects that ("Duplicate declaration of identifier")
-- although nothing about it is ambiguous. Renaming here rather than inventing
-- a fresh name inside 'typedLeaves' keeps the leaf a *closed* expression,
-- which is what makes it safe to drop in at an arbitrary position.
shrinkTypedExpr :: Expr -> [Expr]
shrinkTypedExpr e = withPool (map uniquifyBinders (shrinkTypedExprIn [] e))

shrinkTypedExprIn :: HasADTs => TyEnv -> Expr -> [Expr]
shrinkTypedExprIn env e = case tyOfTypedExprIn env e of
  Nothing -> []
  Just ty -> nub (filter (\c -> smaller c && preserves ty c)
                         (typedLeavesIn ty ++ collapses e ++ childShrinks env e))
  where
    smaller c = typedExprSize c < typedExprSize e
    -- Every candidate is re-typed *here*, at this node, including the ones
    -- 'childShrinks' rebuilt around a shrunk child -- not only the ones this
    -- node proposes itself. Type preservation is not preserved by contexts:
    -- recovery is partial and context-sensitive, so a child replacement that
    -- 'tyGeneralizes' the child at its own site can still change what the
    -- enclosing node recovers. Two ways it happens (both found by the
    -- 'Shrinker' group's type-preservation property, task
    -- shrinker-type-recovery-flake):
    --
    --   * 'TyAny' at the child's site reads as "free", but may only mean "not
    --     recovered": @sq a@ with @a : ?@ collapses to @a@, and an enclosing
    --     polymorphic @neg@ then recovers 'Nothing'.
    --   * The replacement is recovered by a *different, more precise* rule once
    --     it sits in the parent: a callee @(\\v0 -> \\v1 -> v1) x@ collapses to
    --     the literal @\\v1 -> v1@, the enclosing 'Apply' becomes a @let@ that
    --     pushes the argument type in, and a position the original left free
    --     is now committed.
    --
    -- Checking at every level of the recursion means a candidate that reaches
    -- the root has been verified against every node on its path, which is what
    -- the property actually asks. The price is that rejected candidates cost a
    -- re-typing per enclosing level (quadratic in depth), accepted as cheaper
    -- than a shrinker that hands the property ill-typed programs.
    --
    -- Judged in the node's own scope: a @let@ collapse that only type-checks
    -- under the binding being removed is not a candidate at all. And judged
    -- asymmetrically ('tyGeneralizes') -- the replacement must be at least as
    -- general as the node it replaces, never merely joinable with it.
    preserves ty c = maybe False (`tyGeneralizes` ty) (tyOfTypedExprIn env c)

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
--
-- Unfiltered: the type test is applied by 'shrinkTypedExprIn' to every
-- candidate uniformly, these included.
collapses :: Expr -> [Expr]
collapses e = case asLet e of
  Just (x, val, body) -> [val] ++ [ body | not (mentionsVar x body) ]
  Nothing -> case node e of
    IfThenElse _ t f -> [t, f]
    InjF _ args      -> args
    _                -> []

-- | Shrink one child at a time, keeping the node and every sibling. This is
-- what actually minimizes a deep program: the collapses above cut whole
-- subtrees, this reduces the ones that have to stay.
childShrinks :: HasADTs => TyEnv -> Expr -> [Expr]
childShrinks env e = case asLet e of
  Just (x, val, body) ->
    -- The bound value is shrunk in the outer scope, the body under the
    -- binding. A shrunk value may have a strictly more general recovered type
    -- (that is the shrinker's standing contract), and the body is re-typed
    -- against it here, which is why the env carries the *recovered* type
    -- rather than the one generation chose.
    [ mkLet x val' body | val' <- shrinkTypedExprIn env val ]
    ++ case tyOfArgument env (x #-># body) val of
         Nothing  -> []
         Just vty -> [ mkLet x val body' | body' <- shrinkTypedExprIn ((x, vty) : env) body ]
  Nothing -> case node e of
    IfThenElse c t f ->
      [ rebuild (IfThenElse c' t f) | c' <- shrinkTypedExprIn env c ]
      ++ [ rebuild (IfThenElse c t' f) | t' <- shrinkTypedExprIn env t ]
      ++ [ rebuild (IfThenElse c t f') | f' <- shrinkTypedExprIn env f ]
    InjF name args ->
      [ rebuild (InjF name args') | args' <- shrinkOne (shrinkTypedExprIn env) args ]
    -- The arrow surface. A @let@ is an 'Apply' of a literal lambda and is
    -- handled above; this is every *other* application -- a named or selected
    -- function value called on an argument -- and the lambda itself where it
    -- is read as a value rather than called.
    --
    -- The callee is shrunk in the outer scope like any other subexpression:
    -- its recovered type is an arrow, and 'shrinkTypedExprIn' offers the
    -- constant-function leaf for it, which is how a selected or named callee
    -- minimizes away.
    Apply f a ->
      [ rebuild (Apply f' a) | f' <- shrinkTypedExprIn env f ]
      ++ [ rebuild (Apply f a') | a' <- shrinkTypedExprIn env a ]
    -- A lambda read as a *value* offers no child shrinks, because at this
    -- node nothing says what its parameter was bound at, and the shrinker has
    -- no type for a binder it cannot name.
    --
    -- Binding it at 'TyAny' and descending anyway is wrong, and not subtly:
    -- 'tyGeneralizes' reads 'TyAny' as "this position is free, so anything may
    -- fill it", which is true of a position *no node commits* and false of a
    -- variable whose type merely was not recovered. With @v : TyAny@ in scope,
    -- @collapses@ accepts @v@ as a replacement for any node at all, and
    -- @fst (v, xs)@ -- whose value is @v@ -- duly shrank to @fst v@, which is
    -- @fst@ of an Int. (Found by the @Shrinker@ group's type-preservation
    -- property, which is exactly its job.)
    --
    -- Nothing is lost that matters: the lambda itself still reduces, to the
    -- constant function 'typedLeaves' offers at its arrow type, so a large
    -- function value in a counterexample minimizes to @\\p -> 0@ rather than
    -- being minimized from within. Where a lambda *is* applied, its parameter
    -- type is known from the argument, and that is the @let@ case above.
    Lambda{} -> []
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
--
-- Milestone M4: the other top-level declarations shrink too ('declShrinks'),
-- after @main@'s candidates, so a helper's or a recursive function's body is
-- minimized rather than carried whole into every counterexample.
--
-- And a candidate may not add an unguarded partial projection
-- ('unguardedProjections'), for the reason given there.
--
-- Last, the ADT declarations themselves shrink ('adtDeclShrinks'): an unused
-- constructor or field goes, and 'withADTs' drops a declaration nothing uses
-- any more. Recovery runs against the program's own declarations.
shrinkTypedProgram :: Program -> [Program]
shrinkTypedProgram p = inProgram p $ filter guarded $ map withADTs $ (case typedMainParts p of
  Nothing -> []
  Just ((env, core), rebuild) ->
    [ replaceDecl "main" (uniquifyBinders (rebuild core'))
    | core' <- shrinkTypedExprIn env core
    ]
    ++ [ replaceDecl nm (uniquifyBindersFrom (declBinderPrefix nm) e')
       | (nm, e) <- functions p, nm /= "main"
       , e' <- declShrinks (helperEnv p) nm e ])
  ++ adtDeclShrinks p
  where
    guarded p' = length (unguardedProjections p') <= length (unguardedProjections p)
    replaceDecl nm body' =
      p { functions = [ (n, if n == nm then body' else b) | (n, b) <- functions p ] }

-- | Shrinks of one non-@main@ declaration, in a scope holding every
-- declaration's recovered type (its own included, for a recursive call) and
-- its parameter at the type the call site in @main@ pins.
--
-- A recursive declaration's **skeleton is never shrunk**: for
-- @[\k ->] if \<stop\> then \<base\> else \<step\>@ with @\<step\>@ calling it,
-- only @\<base\>@ and @\<step\>@ are. Shrinking the stopping condition --
-- @k < 1@ to @False@, or the coin to a constant -- produces a function that
-- never returns, which the property reports as a timeout, i.e. "still
-- failing"; the shrinker would then walk straight into non-termination and
-- report *that* as the minimal counterexample. Shrinks never duplicate a
-- subterm, so a step that made at most one call keeps making at most one.
declShrinks :: HasADTs => TyEnv -> String -> Expr -> [Expr]
declShrinks scope nm e = case node e of
  Lambda x body
    | Just (TyArrow aty _) <- lookup nm scope
    -> [ Expr (ann e) (Lambda x b') | b' <- inBody ((x, aty) : scope) body ]
  Lambda{} -> []
  _ -> inBody scope e
  where
    -- The whole declaration with its step replaced, which is what
    -- 'recursionSafe' compares against the original.
    rebuildWith f' = case node e of
      Lambda x body | IfThenElse c t _ <- node body
        -> Expr (ann e) (Lambda x (Expr (ann body) (IfThenElse c t f')))
      IfThenElse c t _ -> Expr (ann e) (IfThenElse c t f')
      _ -> e
    inBody env b = case node b of
      IfThenElse c t f
        | mentionsVar nm f ->
            [ Expr (ann b) (IfThenElse c t' f) | t' <- shrinkTypedExprIn env t ]
            ++ [ Expr (ann b) (IfThenElse c t f') | f' <- shrinkTypedExprIn env f
                                                  , recursionSafe ?adts nm e (rebuildWith f') ]
      _ -> shrinkTypedExprIn env b
