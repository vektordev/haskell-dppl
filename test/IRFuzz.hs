{-# LANGUAGE ScopedTypeVariables #-}

-- | The IR fuzz generator (docs-repo design @ir-fuzz-generator@), milestones
-- M1 (deterministic-value IR) and M2 ('PResult' bodies in every semiring, see
-- "PResult bodies" below) on the scalar Python and Julia backends, with the
-- interpreter as the oracle.
--
-- 'prop_Fuzz_BackendsAgree' reaches the backends only through what the SPLL
-- compiler emits from programs its generator can draw. This module draws
-- 'IREnv's directly instead, within the IR's type contract
-- ('SPLL.IRTypeCheck'), so a construct is exercised because it has a
-- production here, not because some SPLL program happens to compile to it.
--
-- One drawn case is one function group @main@ whose normal-parameter body (or
-- writeLogits body: same calling convention, different method) is a plain
-- value expression over its parameters and a few top-level constants. It
-- carries several argument vectors, drawn by the same type discipline and
-- leaning on boundary values (0, negative zero, the infinities, NaN, the
-- largest and smallest doubles, the empty list).
--
-- Each argument vector is one query. The interpreter answers it with a value,
-- a /program raise/ (a partial destructor out of its domain, an 'IRError'
-- node), or a /refusal/ (anything else: a type error, a Haskell exception,
-- a timeout). A refusal on IR the checker accepts is an interpreter bug or an
-- unwritten IR invariant (the design's review decision (1)), so refusals are
-- not compared but tabulated by reason ('refusalKey'), and a reason not in
-- 'knownRefusals' fails the property.
--
-- A backend must answer a value where the interpreter does, and raise where
-- it raises. Values are compared structurally, floats with 'probAgrees' and
-- the sign of a zero.
--
-- What has no production here, and why, is 'noProduction'.
module IRFuzz
  ( IRCase(..)
  , BodyKind(..)
  , SemiringChoice(..)
  , genIRCase
  , shrinkIRCase
  , irCaseEnv
  , irCaseFunction
  , irCaseWellTyped
  , renderIRCase
  , InterpOutcome(..)
  , interpretIRCase
  , refusalKey
  , knownRefusals
  , knownRefusal
  , knownDisagreements
  , KnownFamily(..)
  , knownDisagreement
  , IRDisagreement(..)
  , renderIRDisagreement
  , runIRCasesPython
  , runIRCasesJulia
  , checkedIRConstructs
  , irGeneratorConstructs
  , noProduction
  , valueAgrees
  , irFuzzGeneratorTests
  ) where

import Control.Exception (SomeException, SomeAsyncException(..), ErrorCall(..), try, evaluate, fromException, throwIO)
import Control.Monad (replicateM)
import Control.Monad.State.Strict (StateT, evalStateT, get, put, lift, State, execState, evalState, modify)
import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf, isInfixOf, nub, sort)
import Data.Maybe (mapMaybe, isJust)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import System.Directory (getCurrentDirectory, findExecutable)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Timeout (timeout)
import Test.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertEqual, assertFailure)
import Text.Read (readMaybe)
import Data.Text (pack, unpack, replace)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.IRTypeCheck (IRType(..), checkIREnv, showIRType, showIRTypeError)
import SPLL.Semiring
import SPLL.IRCompiler (stripBranchCount)
import Control.Monad.Writer.Lazy (runWriterT)
import SPLL.Typing.RType (RType(..), TVarR(..))
import IRInterpreter (generateDet)
import qualified SPLL.CodeGenPyTorch as Py
import qualified SPLL.CodeGenJulia as Jl
import BackendAgreement (Answer(..), parseAnswerLine, pythonSerializer, juliaSerializer,
                         readNum, runBounded, forcedSource, oneLine, probAgrees, irConstructs)
import End2EndTesting (juliaTestFlags)

-- ---------------------------------------------------------------------------
-- Cases

-- | Which deterministic body of @main@ the expression is: its normal-parameter
-- function, its writeLogits function, or (a 'PResult'-shaped body, M2) its
-- probability or integrate function. All are plain functions of the group's
-- parameters; they differ in the method name each backend emits.
data BodyKind = NormalBody | WriteLogitsBody | ProbBody | IntegBody deriving (Show, Eq)

-- | The semiring a 'PResult' body was built in ('presultSemiring').
data SemiringChoice = SRLinear | SRLog | SRMaxLinear | SRMaxLog deriving (Show, Eq, Enum, Bounded)

data IRCase = IRCase
  { icKind   :: BodyKind
  , icShape  :: Maybe (SemiringChoice, Bool)
    -- ^ a 'PResult' body: its semiring, and whether its branch count was
    -- stripped (as the compiler does unless @countBranches@)
  , icParams :: [(String, IRType)]
  , icResult :: IRType
  , icConsts :: [(String, IRValue)]   -- ^ the env's top-level constants
  , icBody   :: IRExpr                -- ^ under the parameter lambdas
  , icArgs   :: [[IRValue]]           -- ^ one argument vector per query
  } deriving (Show)

-- | The body with its parameter lambdas.
irCaseFunction :: IRCase -> IRExpr
irCaseFunction c = foldr IRLambda (icBody c) (map fst (icParams c))

irCaseEnv :: IRCase -> IREnv
irCaseEnv c = IREnv [group] [] (icConsts c)
  where
    decl = Just (irCaseFunction c, "")
    group = IRFunGroup
      { groupName = "main", genFun = Nothing
      , writeLogitsFun = if icKind c == WriteLogitsBody then decl else Nothing
      , normalFun = if icKind c == NormalBody then decl else Nothing
      , probFun = if icKind c == ProbBody then decl else Nothing
      , integFun = if icKind c == IntegBody then decl else Nothing
      , groupDoc = "", refusedVariants = [], sampleDomain = Nothing, maskVariantOf = Nothing }

-- | The name the checker reports the body's type under.
bodyName :: IRCase -> String
bodyName c = "main" ++ bodySuffix (icKind c)

bodySuffix :: BodyKind -> String
bodySuffix k = case k of
  NormalBody -> "_normal"
  WriteLogitsBody -> "_writeLogits"
  ProbBody -> "_prob"
  IntegBody -> "_integ"

-- | The checker's type for the body, printed; 'Left' with its message when it
-- rejects the case.
irCaseType :: IRCase -> Either String IRType
irCaseType c = case checkIREnv (irCaseEnv c) of
  Left err -> Left (showIRTypeError err)
  Right tys -> maybe (Left ("no type for " ++ bodyName c)) Right (lookup (bodyName c) tys)

-- | The checker accepts the case, at a type the drawn one is an instance of.
-- (An unused parameter or a constant arm leaves the checked type more
-- general than the drawn one.)
irCaseWellTyped :: IRCase -> Either String ()
irCaseWellTyped c = do
  t <- irCaseType c
  let expected = foldr (ITArrow . snd) (icResult c) (icParams c)
  if isJust (instanceOf t expected IM.empty) then Right ()
    else Left ("drawn at " ++ showIRType expected ++ ", checked as " ++ showIRType t)

-- | Whether the second type is an instance of the first: one substitution of
-- the first's variables makes them equal.
instanceOf :: IRType -> IRType -> IM.IntMap IRType -> Maybe (IM.IntMap IRType)
instanceOf general specific sub = case (general, specific) of
  (ITVar v, _) -> case IM.lookup v sub of
    Nothing -> Just (IM.insert v specific sub)
    Just bound -> if bound == specific then Just sub else Nothing
  (ITList a, ITList b) -> instanceOf a b sub
  (ITTuple a1 b1, ITTuple a2 b2) -> instanceOf a1 a2 sub >>= instanceOf b1 b2
  (ITEither a1 b1, ITEither a2 b2) -> instanceOf a1 a2 sub >>= instanceOf b1 b2
  (ITArrow a1 b1, ITArrow a2 b2) -> instanceOf a1 a2 sub >>= instanceOf b1 b2
  (ITTensor s1 a, ITTensor s2 b) | s1 == s2 -> instanceOf a b sub
  _ -> if general == specific then Just sub else Nothing

renderIRCase :: IRCase -> String
renderIRCase c = unlines $
  [ "IR CASE (" ++ show (icKind c) ++ maybe "" (\(sr, stripped) -> ", " ++ show sr ++ (if stripped then ", branch count stripped" else "")) (icShape c)
    ++ "): main :: " ++ showIRType (foldr (ITArrow . snd) (icResult c) (icParams c)) ]
  ++ [ "  const " ++ n ++ " = " ++ show v | (n, v) <- icConsts c ]
  ++ [ "  params " ++ unwords (map fst (icParams c))
     , "  body " ++ show (icBody c) ]

-- ---------------------------------------------------------------------------
-- The generator

-- | A drawn name is fresh: the counter makes every binder distinct, so no
-- case exercises shadowing (a property of the source language, not of the
-- IR the compiler emits).
type G = StateT Int Gen

fresh :: String -> G String
fresh pre = do
  n <- get
  put (n + 1)
  return (pre ++ show n)

liftG :: Gen a -> G a
liftG = lift

-- | Types a case is drawn at. 'ITThetaTree' only appears where a theta
-- accessor consumes it (a theta tree is a Python tuple of lists and has no
-- token form to compare), and neither 'ITSymbol' (no text backend can render
-- a symbol constant) nor the M3 types (tensors, arrows, ADTs) appear at all.
genType :: Int -> Gen IRType
genType d
  | d <= 0 = scalar
  | otherwise = frequency
      [ (6, scalar)
      , (1, ITList <$> genType (d - 1))
      , (1, ITTuple <$> genType (d - 1) <*> genType (d - 1))
      , (1, ITEither <$> genType (d - 1) <*> genType (d - 1))
      ]
  where scalar = frequency [(3, return ITFloat), (2, return ITInt), (2, return ITBool), (1, return ITUnit)]

isNumeric :: IRType -> Bool
isNumeric t = t == ITFloat || t == ITInt

-- | What 'OpLessThan'/'OpGreaterThan' are drawn over: numbers, and tuples of
-- them. Lists are ordered in the contract too, but compare only at equal
-- length (the interpreter fails otherwise), which this generator does not
-- track.
isOrderedTy :: IRType -> Bool
isOrderedTy t = case t of
  ITTuple a b -> isOrderedTy a && isOrderedTy b
  _ -> isNumeric t

-- | The contract's equality: no functions, tensors or theta trees.
isEquatable :: IRType -> Bool
isEquatable t = case t of
  ITThetaTree -> False
  ITList a -> isEquatable a
  ITTuple a b -> isEquatable a && isEquatable b
  ITEither a b -> isEquatable a && isEquatable b
  _ -> True

-- | Every theta tree drawn has this shape: three parameters per node, two
-- subtrees per node down to depth 'thetaDepth', leaves below. An accessor
-- index is drawn inside it, but nesting 'AcSubtree' deeper than the tree is
-- possible and raises.
thetaDepth :: Int
thetaDepth = 3

genTheta :: Int -> Gen ThetaTree
genTheta d = ThetaTree <$> vectorOf 3 genPlainFloat <*> (if d <= 0 then return [] else vectorOf 2 (genTheta (d - 1)))

genPlainFloat :: Gen Double
genPlainFloat = frequency [(3, choose (-3, 3)), (1, elements [0, 1, -1, 0.5])]

-- | A float, leaning on the boundary values the backends' float handling
-- (literal emission, the IEEE-total unary math) has to get right.
genFloat :: Gen Double
genFloat = frequency
  [ (5, choose (-3, 3))
  , (3, elements [0, -0.0, 1, -1, 0.5, 2, 10])
  , (2, elements [1 / 0, -1 / 0, 0 / 0, 1e300, -1e300, 5e-324, 1e-300, 800, -800])
  ]

-- | Small ints: Python's are unbounded and Haskell's and Julia's wrap at 64
-- bits, so the generator keeps products far from the wrap.
genInt :: Gen Int
genInt = frequency [(4, choose (-5, 5)), (1, elements [0, 1, -1, 1000, -1000])]

genValue :: IRType -> Gen IRValue
genValue t = case t of
  ITBool -> VBool <$> arbitrary
  ITInt -> VInt <$> genInt
  ITFloat -> VFloat <$> genFloat
  ITUnit -> return VUnit
  ITThetaTree -> VThetaTree <$> genTheta thetaDepth
  ITList a -> do
    n <- frequency [(2, return 0), (3, choose (1, 3))]
    xs <- vectorOf n (genValue a)
    return (VList (foldr ListCont EmptyList xs))
  ITTuple a b -> VTuple <$> genValue a <*> genValue b
  ITEither a b -> oneof [VEither . Left <$> genValue a, VEither . Right <$> genValue b]
  _ -> error ("IRFuzz.genValue: no values drawn at " ++ show t)

type Scope = [(String, IRType)]

-- | An expression of type @t@ over the variables in scope, of roughly the
-- given size.
genExpr :: Scope -> IRType -> Int -> G IRExpr
genExpr sc t n
  | n <= 0 = leaf sc t
  | otherwise = do
      join' (liftG (frequency [ (w, return p) | (w, p) <- general ++ specific ]))
  where
    join' m = m >>= id
    half = n `div` 2
    third = n `div` 3
    general =
      [ (2, leaf sc t)
      , (3, IRIf <$> genExpr sc ITBool third <*> genExpr sc t third <*> genExpr sc t third)
      , (1, IRSelect <$> genExpr sc ITBool third <*> genExpr sc t third <*> genExpr sc t third)
      , (3, letIn)
      , (1, do s <- liftG (genType 1); IRDestruct AcFst <$> genExpr sc (ITTuple t s) (n - 1))
      , (1, do s <- liftG (genType 1); IRDestruct AcSnd <$> genExpr sc (ITTuple s t) (n - 1))
      , (1, guardedHead)
      , (1, guardedFromEither True)
      , (1, guardedFromEither False)
      , (1, betaRedex)
      ]
      ++ [ (1, IRIf <$> genExpr sc ITBool half <*> genExpr sc t half <*> return (IRError "drawn IRError")) | n > 4 ]
    letIn = do
      s <- liftG (genType 1)
      v <- fresh "l"
      IRLetIn v <$> genExpr sc s half <*> genExpr ((v, s) : sc) t half
    betaRedex = do
      s <- liftG (genType 1)
      v <- fresh "p"
      body <- genExpr ((v, s) : sc) t half
      IRApply (IRLambda v body) <$> genExpr sc s half
    -- @head xs@ guarded by @xs == []@ where the element type has equality,
    -- else unguarded (and raising on an empty list).
    guardedHead = do
      xs <- genExpr sc (ITList t) half
      if isEquatable t && n > 2
        then do
          v <- fresh "h"
          dflt <- genExpr sc t half
          return (IRLetIn v xs (IRIf (IROp OpEq (IRVar v) (IRConst (VList EmptyList))) dflt (IRDestruct AcHead (IRVar v))))
        else return (IRDestruct AcHead xs)
    guardedFromEither isL = do
      s <- liftG (genType 1)
      let et = if isL then ITEither t s else ITEither s t
      e <- genExpr sc et half
      guarded <- liftG (frequency [(6, return True), (1, return False)])
      let (test, proj) = if isL then (AcIsLeft, AcFromLeft) else (AcIsRight, AcFromRight)
      if guarded
        then do
          v <- fresh "e"
          dflt <- genExpr sc t half
          return (IRLetIn v e (IRIf (IRDestruct test (IRVar v)) (IRDestruct proj (IRVar v)) dflt))
        else return (IRDestruct proj e)
    bin op ty = IROp op <$> genExpr sc ty half <*> genExpr sc ty half
    un op ty = IRUnaryOp op <$> genExpr sc ty (n - 1)
    specific = case t of
      ITFloat ->
        [ (2, bin OpPlus ITFloat), (2, bin OpMult ITFloat), (2, bin OpSub ITFloat)
        , (1, bin OpMax ITFloat), (2, bin OpDiv ITFloat)
        , (1, un OpNeg ITFloat), (1, un OpSign ITFloat), (1, un OpAbs ITFloat)
        , (1, un OpExp ITFloat), (1, un OpLog ITFloat)
        , (2, do d <- liftG (elements [IRNormal, IRUniform])
                 ls <- liftG (elements [Linear, Log])
                 cum <- liftG arbitrary
                 (if cum then IRCumulative d ls else IRDensity d ls) <$> genExpr sc ITFloat (n - 1))
        , (2, do i <- liftG (choose (0, 2)); IRDestruct (AcTheta i) <$> genExpr sc ITThetaTree (n - 1))
        ]
      ITInt ->
        [ (2, bin OpPlus ITInt), (2, bin OpMult ITInt), (2, bin OpSub ITInt), (1, bin OpMax ITInt)
        , (1, un OpNeg ITInt), (1, un OpSign ITInt), (1, un OpAbs ITInt)
        , (2, exactDivision)
        ]
      ITBool ->
        [ (2, do s <- liftG (suchThat (genType 1) isOrderedTy)
                 op <- liftG (elements [OpLessThan, OpGreaterThan])
                 bin op s)
        , (3, do s <- liftG (suchThat (genType 2) isEquatable); bin OpEq s)
        , (1, bin OpApprox ITFloat)
        , (2, bin OpAnd ITBool), (2, bin OpOr ITBool), (2, un OpNot ITBool)
        , (1, do s <- liftG (genType 1)
                 e <- frequency' [(3, genExpr sc s (n - 1)), (1, return (IRConst VAny))]
                 return (IRUnaryOp OpIsAny e))
        , (1, do a <- liftG (genType 1); b <- liftG (genType 1)
                 acc <- liftG (elements [AcIsLeft, AcIsRight])
                 IRDestruct acc <$> genExpr sc (ITEither a b) (n - 1))
        , (1, do s <- liftG (genType 1)
                 rt <- liftG (frequency [(3, return (rTypeOf s)), (1, rTypeOf <$> genType 1)])
                 IRConformsTo rt <$> genExpr sc s (n - 1))
        , (1, do s <- liftG (suchThat (genType 1) (\ty -> isJust' (domainShape ty)))
                 dom <- liftG (genDomain s)
                 IRIsPossible dom <$> genExpr sc s (n - 1))
        ]
      ITList a ->
        [ (3, IRConstruct TgCons <$> sequence [genExpr sc a half, genExpr sc t half])
        , (1, guardedTail a)
        ]
      ITTuple a b -> [ (4, IRConstruct TgTuple <$> sequence [genExpr sc a half, genExpr sc b half]) ]
      ITEither a b ->
        [ (2, IRConstruct TgLeft . (: []) <$> genExpr sc a (n - 1))
        , (2, IRConstruct TgRight . (: []) <$> genExpr sc b (n - 1)) ]
      ITThetaTree ->
        [ (1, do i <- liftG (choose (0, 1)); IRDestruct (AcSubtree i) <$> genExpr sc ITThetaTree (n - 1)) ]
      _ -> []
    frequency' xs = join' (liftG (frequency [ (w, return m) | (w, m) <- xs ]))
    guardedTail a = do
      xs <- genExpr sc t half
      if isEquatable a
        then do
          v <- fresh "t"
          return (IRLetIn v xs (IRIf (IROp OpEq (IRVar v) (IRConst (VList EmptyList))) (IRVar v) (IRDestruct AcTail (IRVar v))))
        else return (IRDestruct AcTail xs)
    -- 'OpIntDiv' and 'OpMod' in the only shape the compiler emits them in
    -- ('PredefinedFunctions.multIInv1'): a division by a nonzero constant,
    -- guarded by the remainder being zero. Outside it the backends differ by
    -- design (Python floors, Julia truncates), and a zero divisor is a
    -- Haskell exception in the interpreter.
    exactDivision = do
      a <- genExpr sc ITInt half
      k <- liftG (suchThat genInt (/= 0))
      v <- fresh "q"
      dflt <- genExpr sc ITInt half
      let x = IRVar v
          kc = IRConst (VInt k)
      return (IRLetIn v a (IRIf (IROp OpEq (IROp OpMod x kc) (IRConst (VInt 0))) (IROp OpIntDiv x kc) dflt))
    isJust' = maybe False (const True)

-- | A leaf: a variable of the type in scope, or a constant.
leaf :: Scope -> IRType -> G IRExpr
leaf sc t = case [ v | (v, t') <- sc, t' == t ] of
  [] -> IRConst <$> liftG (genValue t)
  vs -> liftG (frequency [(3, IRVar <$> elements vs), (1, IRConst <$> genValue t)])

rTypeOf :: IRType -> RType
rTypeOf t = case t of
  ITBool -> TBool
  ITInt -> TInt
  ITFloat -> TFloat
  ITUnit -> TUnit
  ITThetaTree -> TThetaTree
  ITSymbol -> TSymbol
  ITList a -> ListOf (rTypeOf a)
  ITTuple a b -> Tuple (rTypeOf a) (rTypeOf b)
  ITEither a b -> TEither (rTypeOf a) (rTypeOf b)
  _ -> NotSetYet

-- | The types 'IRIsPossible' is drawn at: those a 'MultiValue' describes
-- (no lists, no unit).
domainShape :: IRType -> Maybe ()
domainShape t = case t of
  ITBool -> Just ()
  ITInt -> Just ()
  ITFloat -> Just ()
  ITTuple a b -> domainShape a >> domainShape b
  ITEither a b -> domainShape a >> domainShape b
  _ -> Nothing

genDomain :: IRType -> Gen MultiValue
genDomain t = case t of
  ITBool -> MultiDiscretes . map VBool <$> sublistOf' [False, True]
  ITInt -> MultiDiscretes . map VInt . nub <$> listOf1 (choose (-3, 3))
  ITFloat -> oneof [return MultiContinuous, MultiDiscretes . map VFloat . nub <$> listOf1 (elements [0, 1, -1, 0.5])]
  ITTuple a b -> MultiTuple <$> genDomain a <*> genDomain b
  ITEither a b -> MultiEither <$> genDomain a <*> genDomain b
  _ -> error ("IRFuzz.genDomain: no domain at " ++ show t)
  where sublistOf' xs = sublistOf xs `suchThat` (not . null)

-- | The size bodies are drawn at.
caseSize :: Int
caseSize = 14

-- | A case: a value body (M1) or a 'PResult' body (M2), in equal parts.
genIRCase :: Gen IRCase
genIRCase = oneof [genValueCase, genPResultCase]

-- | A value-body case: zero to three parameters, up to two top-level
-- constants, a body and four argument vectors.
genValueCase :: Gen IRCase
genValueCase = do
  kind <- frequency [(3, return NormalBody), (1, return WriteLogitsBody)]
  np <- choose (0, 3)
  ptys <- vectorOf np (genType 2)
  nc <- frequency [(3, return 0), (1, choose (1, 2))]
  ctys <- vectorOf nc (genType 1)
  cvals <- mapM genValue ctys
  rt <- genType 2
  size <- choose (2, caseSize)
  let params = zip [ "a" ++ show i | i <- [0 :: Int ..] ] ptys
      consts = zip [ "k" ++ show i | i <- [0 :: Int ..] ] cvals
      sc = params ++ zip (map fst consts) ctys
  body <- evalStateT (genExpr sc rt size) 0
  args <- replicateM 4 (mapM genValue ptys)
  return (IRCase kind Nothing params rt consts body args)

-- ---------------------------------------------------------------------------
-- PResult bodies (M2)
--
-- A probability or integrate body returns a 'PResult', packed. It is drawn as
-- a /plan/, a tree whose nodes name 'SPLL.Semiring''s combinators, and the
-- plan is then built by those very combinators ('buildPlan') in a semiring
-- the case draws: linear and log-space sum-product, and the two max-product
-- instances. So the body is what the compiler would emit for the same
-- combinator tree, in that semiring, without a program that compiles to it
-- and without compiling through the log-space or max-product config. The
-- dims and the impossibility flag come out of the combinators too: a mixture
-- of a mass and a density, an indicator, a guard, an ANY-guarded leaf.
--
-- Half the bodies have their branch count stripped as the compiler does
-- unless @countBranches@ ('stripBranchCount'), so both result layouts are
-- drawn. The leaves' operands are M1's value expressions.

-- | A 'PResult' built from the combinator of the same name.
data PPlan
  = PDensity Distribution IRExpr                -- ^ 'density' of 'distDensity' at a sample
  | PScaledNormal IRExpr [IRExpr]               -- ^ 'density' of 'scaledNormalDensity'
  | PCdf Distribution IRExpr                    -- ^ 'mass' of 'distCumulative'
  | PMass IRExpr                                -- ^ 'mass' of a linear value ('fromLinearSR')
  | PDet IRExpr                                 -- ^ 'detP' of a linear value
  | PIndicator IRExpr                           -- ^ 'indicatorP'
  | PImpossible                                 -- ^ 'impossibleP'
  | PMeasureDiff Distribution IRExpr IRExpr     -- ^ 'measureDiffSR' of two CDFs, at @lo@ and @lo + |w|@
  | PSumAll [IRExpr]                            -- ^ 'mass' of 'sumAllSR' over linear values
  | PImpossibleWhen IRExpr PPlan
  | PProd PPlan PPlan
  | PGuard [IRExpr] PPlan
  | PScaleCoV Bool IRExpr PPlan
  | PScaleCoVAtom IRExpr PPlan PPlan
  | PComplement PPlan                           -- ^ 'srComplement' of the probability
  | PComplementWhen IRExpr PPlan
  | PAnySafe IRExpr PPlan
  | PAnySafeShared IRExpr PPlan                 -- ^ over the sub-result's own let block
  | PMix PPlan PPlan
  | PMixSub PPlan PPlan                         -- ^ not drawn under max-product ('srMinus' is undefined there)
  | PIf IRExpr PPlan PPlan                      -- ^ 'zipResult' of an 'IRIf'
  | PLet String IRExpr PPlan                    -- ^ a let-binding the sub-plan may read
  | PShare [IRExpr] PPlan                       -- ^ 'shareResult' under guards
  | PEnumSum Bool String MultiValue PPlan       -- ^ 'enumSumP', with or without branch counts
  | PEnumMix Bool IRExpr String MultiValue PPlan -- ^ 'enumMixP', with its density dim
  deriving (Show)

semiringFor :: SemiringChoice -> Semiring
semiringFor c = case c of
  SRLinear -> linearSemiring
  SRLog -> logSemiring
  SRMaxLinear -> maxLinearSemiring
  SRMaxLog -> maxLogSemiring

isMaxProduct :: SemiringChoice -> Bool
isMaxProduct c = c == SRMaxLinear || c == SRMaxLog

-- | The plan's nodes by constructor name, for the coverage check.
planNodes :: PPlan -> [String]
planNodes pl = takeWhile (/= ' ') (show pl) : concatMap planNodes (subPlans pl)
  where
    subPlans x = case x of
      PImpossibleWhen _ a -> [a]
      PProd a b -> [a, b]
      PGuard _ a -> [a]
      PScaleCoV _ _ a -> [a]
      PScaleCoVAtom _ a b -> [a, b]
      PComplement a -> [a]
      PComplementWhen _ a -> [a]
      PAnySafe _ a -> [a]
      PAnySafeShared _ a -> [a]
      PMix a b -> [a, b]
      PMixSub a b -> [a, b]
      PIf _ a b -> [a, b]
      PLet _ _ a -> [a]
      PShare _ a -> [a]
      PEnumSum _ _ _ a -> [a]
      PEnumMix _ _ _ _ a -> [a]
      _ -> []

-- | Every 'PPlan' constructor; 'PMixSub' is not drawn under max-product.
planLabels :: SemiringChoice -> [String]
planLabels c =
  [ "PDensity", "PScaledNormal", "PCdf", "PMass", "PDet", "PIndicator", "PImpossible", "PMeasureDiff"
  , "PSumAll", "PImpossibleWhen", "PProd", "PGuard", "PScaleCoV", "PScaleCoVAtom", "PComplement"
  , "PComplementWhen", "PAnySafe", "PAnySafeShared", "PMix", "PIf", "PLet", "PShare", "PEnumSum", "PEnumMix" ]
  ++ [ "PMixSub" | not (isMaxProduct c) ]

-- | The packed result the plan builds, its floated let-bindings around it.
buildPlan :: SemiringChoice -> PPlan -> IRExpr
buildPlan c plan = case runCompilerMonad (go plan) of
  Right (r, binds) -> generateLetInExpr binds (packResult r)
  Left refusal -> error ("IRFuzz.buildPlan: a combinator refused: " ++ show refusal)
  where
    sr = semiringFor c
    nested p = lift (runWriterT (go p))
    packedOf p = do
      (r, binds) <- nested p
      return (generateLetInExpr binds (packResult r))
    go :: PPlan -> CompilerMonad PResult
    go pl = case pl of
      PDensity d x -> return (density (distDensity sr d x) x)
      PScaledNormal z fs -> return (density (scaledNormalDensity sr z fs) z)
      PCdf d x -> return (mass (distCumulative sr d x))
      PMass e -> return (mass (fromLinearSR sr e))
      PDet e -> return (detP (fromLinearSR sr e))
      PIndicator cond -> return (indicatorP sr cond)
      PImpossible -> return (impossibleP sr)
      PMeasureDiff d lo w -> do
        vlo <- mkVariable "cdf_lo"
        vhi <- mkVariable "cdf_hi"
        setVariables [ (vlo, distCumulative sr d lo)
                     , (vhi, distCumulative sr d (IROp OpPlus lo (IRUnaryOp OpAbs w))) ]
        return (mass (measureDiffSR sr (IRVar vhi) (IRVar vlo)))
      PSumAll es -> return (mass (sumAllSR sr (map (fromLinearSR sr) es)))
      PImpossibleWhen cond a -> impossibleWhen cond <$> go a
      PProd a b -> prodP sr <$> go a <*> go b
      PGuard conds a -> guardP sr conds <$> go a
      PScaleCoV cum deriv a -> scaleCoV sr cum deriv <$> go a
      PScaleCoVAtom deriv atom a -> scaleCoVAtom sr deriv <$> go atom <*> go a
      PComplement a -> onProb (srComplement sr) <$> go a
      PComplementWhen cond a -> do
        r <- go a
        x <- complementWhen sr cond (unP (rProb r))
        return (mkPResult (sealP x) (rDim r) (rBranches r) (rImposs r))
      PAnySafe x a -> anySafe sr x id <$> go a
      PAnySafeShared x a -> do
        (r, binds) <- nested a
        anySafeShared sr x binds r
      PMix a b -> mix (mixP sr) a b
      PMixSub a b -> mix (mixSubP sr) a b
      PIf cond a b -> zipResult (IRIf cond) <$> go a <*> go b
      PLet v e a -> setVariables [(v, e)] >> go a
      PShare guards a -> do
        (r, binds) <- nested a
        shareResult sr "share" guards binds r
      PEnumSum bc v dom a -> packedOf a >>= enumSumP sr bc id v dom
      PEnumMix bc dd v dom a -> packedOf a >>= enumMixP sr bc id dd v dom
    -- The caller's branch count, as an 'IfThenElse' passes it: both arms'.
    mix f a b = do
      ra <- go a
      rb <- go b
      f (IROp OpPlus (rBranches ra) (rBranches rb)) ra rb

-- | The size of a leaf's operand expressions.
operandSize :: Int
operandSize = 3

genPlan :: SemiringChoice -> Scope -> Int -> G PPlan
genPlan c sc n
  | n <= 0 = leafPlan
  | otherwise = frequency' $
      [ (2, leafPlan)
      , (1, PImpossibleWhen <$> bool <*> sub)
      , (3, PProd <$> half <*> half)
      , (1, do k <- liftG (choose (1, 2)); PGuard <$> replicateM k bool <*> sub)
      , (1, PScaleCoV <$> liftG arbitrary <*> float <*> sub)
      , (1, PScaleCoVAtom <$> float <*> half <*> half)
      , (1, PComplement <$> sub)
      , (1, PComplementWhen <$> bool <*> sub)
      , (1, PAnySafe <$> anySample <*> sub)
      , (1, PAnySafeShared <$> anySample <*> sub)
      , (3, PMix <$> half <*> half)
      , (2, PIf <$> bool <*> half <*> half)
      , (1, do s <- liftG (genType 1)
               v <- fresh "pl"
               e <- genExpr sc s operandSize
               PLet v e <$> genPlan c ((v, s) : sc) (n - 1))
      , (1, do k <- liftG (choose (0, 2)); PShare <$> replicateM k bool <*> sub)
      , (2, enumerated (\v dom body -> do bc <- liftG arbitrary; return (PEnumSum bc v dom body)))
      , (1, enumerated (\v dom body -> do bc <- liftG arbitrary
                                          dd <- liftG (elements [IRConst (VFloat 1), IRConst (VFloat 0)])
                                          dd' <- frequency' [(1, return dd), (1, (\x -> IRIf (IRUnaryOp OpIsAny x) (IRConst (VFloat 0)) (IRConst (VFloat 1))) <$> float)]
                                          return (PEnumMix bc dd' v dom body)))
      ]
      ++ [ (1, PMixSub <$> half <*> half) | not (isMaxProduct c) ]
  where
    sub = genPlan c sc (n - 1)
    half = genPlan c sc (n `div` 2)
    float = genExpr sc ITFloat operandSize
    bool = genExpr sc ITBool operandSize
    frequency' xs = join' (liftG (frequency [ (w, return m) | (w, m) <- xs ]))
    join' m = m >>= id
    -- The sample an ANY guard tests: mostly a marginal hole, else a value.
    anySample = frequency' [ (2, return (IRConst VAny))
                           , (2, do s <- liftG (genType 1); genExpr sc s 1) ]
    -- An enumerated sum's body sees the enumerated variable, over a small
    -- finite domain (no Float slot: a continuous domain has no values).
    enumerated k = do
      s <- liftG (suchThat (genType 1) (\ty -> isJust (domainShape ty) && finiteTy ty))
      dom <- liftG (genDomain s)
      v <- fresh "ev"
      body <- genPlan c ((v, s) : sc) (n `div` 2)
      k v dom body
    finiteTy ty = case ty of
      ITFloat -> False
      ITTuple a b -> finiteTy a && finiteTy b
      ITEither a b -> finiteTy a && finiteTy b
      _ -> True
    leafPlan = frequency' $
      [ (3, PDensity <$> liftG (elements [IRNormal, IRUniform]) <*> float)
      , (1, do k <- liftG (choose (1, 2)); PScaledNormal <$> float <*> replicateM k float)
      , (2, PCdf <$> liftG (elements [IRNormal, IRUniform]) <*> float)
      , (2, PMass <$> probability)
      , (1, PDet <$> probability)
      , (2, PIndicator <$> bool)
      , (1, return PImpossible)
      , (1, PMeasureDiff <$> liftG (elements [IRNormal, IRUniform]) <*> float <*> float)
      , (1, do k <- liftG (choose (2, 3)); PSumAll <$> replicateM k probability)
      ]
    -- A linear probability: mostly a constant in [0, 1], else any float.
    probability = frequency'
      [ (3, IRConst . VFloat <$> liftG (frequency [(3, choose (0, 1)), (1, elements [0, 1, 0.5, 1e-300])]))
      , (1, float) ]

-- | The 'PResult' layout: @(prob, (dim, (branches, impossible)))@, or without
-- the branch count once stripped.
presultType :: Bool -> IRType
presultType stripped
  | stripped = ITTuple ITFloat (ITTuple ITFloat ITBool)
  | otherwise = ITTuple ITFloat (ITTuple ITFloat (ITTuple ITFloat ITBool))

-- | A 'PResult'-body case: a probability or integrate body over zero to two
-- parameters (the first a float, as a sample is), up to two constants.
genPResultCase :: Gen IRCase
genPResultCase = do
  kind <- elements [ProbBody, IntegBody]
  c <- frequency [(4, return SRLinear), (4, return SRLog), (1, return SRMaxLinear), (1, return SRMaxLog)]
  stripped <- arbitrary
  np <- choose (0, 2)
  ptys <- (ITFloat :) <$> vectorOf np (genType 1)
  nc <- frequency [(3, return 0), (1, choose (1, 2))]
  ctys <- vectorOf nc (genType 1)
  cvals <- mapM genValue ctys
  size <- choose (1, 7)
  let params = zip [ "a" ++ show i | i <- [0 :: Int ..] ] ptys
      consts = zip [ "k" ++ show i | i <- [0 :: Int ..] ] cvals
      sc = params ++ zip (map fst consts) ctys
  plan <- evalStateT (genPlan c sc size) 0
  args <- replicateM 4 (mapM genValue ptys)
  let unstripped = IRCase kind (Just (c, stripped)) params (presultType False) consts (buildPlan c plan) args
  return $ if stripped then stripCase unstripped else unstripped

-- | The case with its body's branch count stripped, by the compiler's own
-- pass.
stripCase :: IRCase -> IRCase
stripCase c = case stripBranchCount (irCaseEnv c) of
  IREnv [g] _ _ | Just (f, _) <- (if icKind c == ProbBody then probFun g else integFun g) ->
    c { icBody = dropLambdas (length (icParams c)) f, icResult = presultType True }
  _ -> error "IRFuzz.stripCase: stripBranchCount changed the group's shape"
  where
    dropLambdas :: Int -> IRExpr -> IRExpr
    dropLambdas 0 e = e
    dropLambdas k (IRLambda _ e) = dropLambdas (k - 1) e
    dropLambdas _ e = error ("IRFuzz.stripCase: expected a lambda, got " ++ show e)

-- ---------------------------------------------------------------------------
-- Shrinking: structural on the IR, filtered by the checker

-- | A failing case is first cut to the one argument vector that fails (the
-- caller has no way to say which, so each in turn), then its body is shrunk:
-- a node replaced by one of its children, or a subtree shrunk in place. Only
-- candidates the checker accepts at the drawn type survive, which is what
-- keeps a shrink from replacing a node by a child of another type or
-- orphaning a let-bound variable.
shrinkIRCase :: IRCase -> [IRCase]
shrinkIRCase c =
  [ c { icArgs = [a] } | length (icArgs c) > 1, a <- icArgs c ]
  ++ [ c' | b <- shrinkExpr (icBody c), let c' = c { icBody = b }, either (const False) (const True) (irCaseWellTyped c') ]

shrinkExpr :: IRExpr -> [IRExpr]
shrinkExpr e = children e ++ simpler e ++
  [ replaceChild i c' e | (i, c) <- zip [0 ..] (children e), c' <- shrinkExpr c ]
  where
    simpler (IRConst (VList (ListCont _ xs))) = [IRConst (VList xs)]
    simpler _ = []

children :: IRExpr -> [IRExpr]
children e = reverse (execState (irDescendM (\x -> modify (x :) >> return x) e) [])

replaceChild :: Int -> IRExpr -> IRExpr -> IRExpr
replaceChild i new e = evalState (irDescendM step e) 0
  where
    step :: IRExpr -> State Int IRExpr
    step x = do
      k <- get
      put (k + 1)
      return (if k == i then new else x)

-- ---------------------------------------------------------------------------
-- The oracle

-- | What the interpreter says at one argument vector.
data InterpOutcome = Interpreted IRValue
             | InterpRaise String   -- ^ the program fails, as it means to
             | InterpRefusal String -- ^ the interpreter does not answer
  deriving (Show)

-- | The messages of the interpreter's @raise@ sites: run-time failures of a
-- well-typed program, which the backends raise on too.
raiseMessages :: [String]
raiseMessages = ["head of an empty list", "tail of an empty list", "fromLeft of a Right", "fromRight of a Left"]

interpreterMicros :: Int
interpreterMicros = 2 * 1000 * 1000

interpretIRCase :: IRCase -> [IRValue] -> IO InterpOutcome
interpretIRCase c args = do
  r <- try (timeout interpreterMicros (evaluate (forced (generateDet [] [] (irCaseEnv c) (map IRConst args) (irCaseFunction c)))))
  case r of
    Left (e :: SomeException)
      | Just (SomeAsyncException _) <- fromException e -> throwIO e
      | Just (ErrorCall msg) <- fromException e, "Error during interpretation" `isPrefixOf` msg -> return (InterpRaise msg)
      | otherwise -> return (InterpRefusal ("exception: " ++ firstLine (show e)))
    Right Nothing -> return (InterpRefusal "timed out")
    Right (Just (Left msg))
      | msg `elem` raiseMessages -> return (InterpRaise msg)
      | otherwise -> return (InterpRefusal msg)
    Right (Just (Right v)) -> return (Interpreted v)
  where
    forced x = length (show x) `seq` x
    firstLine = takeWhile (/= '\n')

-- | A refusal's reason with the offending values cut off, for tabulation.
refusalKey :: String -> String
refusalKey = take 90 . trim . takeWhile (`notElem` "(\n")
  where trim = reverse . dropWhile (\ch -> isSpace ch || ch == ':') . reverse

-- | Interpreter refusals on well-typed IR that are filed, by refusal reason
-- ('refusalKey'), with the docs-repo ticket that owns each and a minimal
-- repro (a body and its arguments) that 'irFuzzGeneratorTests' checks still
-- refuses: a fixed bug fails that pin, so the entry cannot outlive it.
-- Tabulated, not failed. A reason not here fails the property, since a
-- refusal on IR the checker accepts is either an interpreter bug or an IR
-- invariant the checker does not state yet.
knownRefusals :: [(String, String, IRCase)]
knownRefusals =
  [ ( "Type error: Neg can only evaluate on a number"
    , "opsign-nan-negative-zero-and-int-results-differ-across-engines"
    , repro [("a0", ITFloat)] ITFloat (IRUnaryOp OpSign (IRVar "a0")) [VFloat (0 / 0)] )
  ]

knownRefusal :: String -> Maybe String
knownRefusal r = case [ t | (r', t, _) <- knownRefusals, r' == r ] of
  (t : _) -> Just t
  [] -> Nothing

-- | A one-query case, for a pin.
repro :: [(String, IRType)] -> IRType -> IRExpr -> [IRValue] -> IRCase
repro params rt body args = IRCase NormalBody Nothing params rt [] body [args]

-- ---------------------------------------------------------------------------
-- Comparing a backend's answer

-- | Two floats agree under 'probAgrees', and two zeros only with the same
-- sign.
floatAgrees :: Double -> Double -> Bool
floatAgrees a b
  | a == 0 && b == 0 = isNegativeZero a == isNegativeZero b
  | otherwise = probAgrees a b

-- | Match the interpreter's value against a backend's sample tokens
-- (@_ser@'s form). 'Right' says whether an int token stood at a float slot
-- (Python's @sign@ and uniform density answer ints; numerically that is the
-- same value, and it is tabulated rather than failed).
valueAgrees :: IRValue -> [String] -> Either String Bool
valueAgrees v0 toks0 = case go v0 toks0 of
  Right (lenient, []) -> Right lenient
  Right (_, rest) -> Left ("tokens left over: " ++ unwords rest)
  Left why -> Left why
  where
    go v toks = case (v, toks) of
      (VFloat x, ('f' : s) : rest) -> case readNum s of
        Just y | floatAgrees x y -> Right (False, rest)
        _ -> Left ("float " ++ show x ++ " against " ++ s)
      (VFloat x, ('i' : s) : rest) -> case readMaybe s :: Maybe Integer of
        -- An int has no signed zero, so only the number is compared.
        Just y | probAgrees x (fromIntegral y) -> Right (True, rest)
        _ -> Left ("float " ++ show x ++ " against int " ++ s)
      (VInt x, ('i' : s) : rest) | readMaybe s == Just (toInteger x) -> Right (False, rest)
      (VBool True, "b1" : rest) -> Right (False, rest)
      (VBool False, "b0" : rest) -> Right (False, rest)
      (VUnit, "u" : rest) -> Right (False, rest)
      (VTuple a b, "t" : rest) -> both a b rest
      (VEither (Left a), "l" : rest) -> go a rest
      (VEither (Right b), "r" : rest) -> go b rest
      (VList EmptyList, "n" : rest) -> Right (False, rest)
      (VList (ListCont x xs), "c" : rest) -> both x (VList xs) rest
      _ -> Left (show v ++ " against " ++ unwords (take 6 toks))
    both a b toks = do
      (l1, r1) <- go a toks
      (l2, r2) <- go b r1
      return (l1 || l2, r2)

data IRDisagreement = IRDisagreement
  { idBackend :: String
  , idCase    :: IRCase
  , idArgs    :: [IRValue]
  , idInterp  :: InterpOutcome
  , idAnswer  :: Answer
  , idWhy     :: String
  , idSource  :: String
  }

renderIRDisagreement :: IRDisagreement -> String
renderIRDisagreement d = unlines
  [ "IR BACKEND DISAGREEMENT (" ++ idBackend d ++ "): " ++ idWhy d
  , "  arguments: " ++ show (idArgs d)
  , "  interpreter: " ++ show (idInterp d)
  , "  " ++ idBackend d ++ ": " ++ show (idAnswer d)
  ] ++ renderIRCase (idCase d) ++ "EMITTED " ++ idBackend d ++ ":\n" ++ idSource d

-- | A filed family of disagreements: the docs-repo ticket that owns it, the
-- backends it occurs on, how to recognise it, and a minimal repro that
-- 'irFuzzGeneratorTests' runs to check the family still reproduces and is
-- still recognised (a fixed bug fails that pin, so an entry cannot outlive
-- it).
--
-- A family is recognised either by the backend's answer alone
-- ('ByAnswer'), or by an /alternative semantics/ ('AsIf'): a rewrite of the
-- case under which the interpreter answers what the backend answered. The
-- second is exact where the first is a heuristic: it says the backend is
-- right about everything except the one construct the ticket is about.
data KnownFamily = KnownFamily
  { kfTicket   :: String
  , kfBackends :: [String]
  , kfMatch    :: FamilyMatch
  , kfRepro    :: IRCase
  }

data FamilyMatch = ByAnswer (IRCase -> InterpOutcome -> Answer -> Bool)
                 | AsIf (String -> IRExpr -> IRExpr)   -- ^ given the backend

knownDisagreements :: [KnownFamily]
knownDisagreements =
  [ KnownFamily "ir-and-or-strict-in-interpreter-short-circuit-in-backends" ["python", "julia"]
      (AsIf (const (irMap shortCircuit)))
      (repro [] ITBool (IROp OpOr (IRConst (VBool True)) (IRDestruct AcHead (IRConst (VList EmptyList)))) [])
  , KnownFamily "opmax-nan-and-signed-zero-differ-across-engines" ["python", "julia"]
      (AsIf (\b -> backendMaxReduce b . irMap (backendMax b)))
      (repro [("a0", ITFloat)] ITFloat (IROp OpMax (IRConst (VFloat 0)) (IRVar "a0")) [VFloat (-0.0)])
  , KnownFamily "opmax-nan-and-signed-zero-differ-across-engines" ["python", "julia"]
      (AsIf (\b -> backendMaxReduce b . irMap (backendMax b)))
      (repro [("a0", ITFloat)] ITFloat
         (IRBuiltin (BReduce ROpMax 0) [IRBuiltin (BTensor [EFixed 3]) [IRConst (VFloat 1), IRVar "a0", IRConst (VFloat 5)]]) [VFloat (0 / 0)])
  , KnownFamily "logsumexp-reduction-nan-and-infinity-differ-across-engines" ["python", "julia"]
      (AsIf (\b -> irMap (backendLogSumExp b)))
      (repro [("a0", ITFloat)] ITFloat
         (IRBuiltin (BReduce ROpLogSumExp 0) [IRBuiltin (BTensor [EFixed 2]) [IRVar "a0", IRConst (VFloat (-1 / 0))]]) [VFloat (1 / 0)])
  , KnownFamily "logsumexp-reduction-nan-and-infinity-differ-across-engines" ["python"]
      (AsIf (\b -> irMap (backendLogSumExp b)))
      (repro [("a0", ITFloat)] ITFloat
         (IRBuiltin (BReduce ROpLogSumExp 0) [IRBuiltin (BTensor [EFixed 2]) [IRConst (VFloat (-1 / 0)), IRVar "a0"]]) [VFloat (0 / 0)])
  , KnownFamily "opsign-nan-negative-zero-and-int-results-differ-across-engines" ["python", "julia"]
      (AsIf (\b -> irMap (backendSign b)))
      (repro [("a0", ITFloat), ("a1", ITFloat)] (ITTuple ITBool ITFloat)
         (IRConstruct TgTuple [IRConformsTo TFloat (IRUnaryOp OpSign (IRVar "a0")), IRUnaryOp OpSign (IRVar "a1")])
         [VFloat 2, VFloat (-0.0)])
  , KnownFamily "python-float-division-by-zero-raises" ["python"]
      (ByAnswer (\_ o a -> isValue o && raisedWith "ZeroDivisionError" a))
      (repro [("a0", ITFloat)] ITFloat (IROp OpDiv (IRConst (VFloat 1)) (IRVar "a0")) [VFloat 0])
  , KnownFamily "python-normal-density-overflows-past-1e154" ["python"]
      (ByAnswer (\c o a -> isValue o && raisedWith "OverflowError" a && hasNormalDensity (icBody c)))
      (repro [("a0", ITFloat)] ITFloat (IRDensity IRNormal Linear (IRVar "a0")) [VFloat 1e300])
  , KnownFamily "python-uniform-density-and-cdf-answer-ints" ["python"]
      (AsIf (const (irMap pythonUniform)))
      (repro [("a0", ITFloat)] ITBool (IRConformsTo TFloat (IRDensity IRUniform Linear (IRVar "a0"))) [VFloat 0.5])
  -- The same ticket, where the int flows on into float arithmetic: the
  -- rewrite above then stops the interpreter (an int meets a float), so the
  -- family is recognised by the construct and a differing value instead.
  -- Looser: it covers any value difference in a body using a linear uniform
  -- density or CDF.
  , KnownFamily "python-uniform-density-and-cdf-answer-ints" ["python"]
      (ByAnswer (\c o a -> isValue o && isSampled a
                           && not (null [ () | x <- universe (icBody c), linearUniform x ])))
      (repro [("a0", ITFloat)] ITBool (IRConformsTo TFloat (IRCumulative IRUniform Linear (IRVar "a0"))) [VFloat 2])
  , KnownFamily "python-empty-list-head-and-tail-answer-none" ["python"]
      (ByAnswer (\_ o a -> case (o, a) of
                  (InterpRaise m, Sampled _) -> m `elem` ["head of an empty list", "tail of an empty list"]
                  _ -> False))
      (repro [] ITBool (IRUnaryOp OpIsAny (IRDestruct AcHead (IRConst (VList (EmptyList :: GenericList IRValue))))) [])
  , KnownFamily "python-ispossible-on-a-tuple-domain-answers-none" ["python"]
      (ByAnswer (\c _ _ -> any tupleDomain [ d | IRIsPossible d _ <- universe (icBody c) ]))
      (repro [] ITBool (IRIsPossible (MultiTuple MultiContinuous MultiContinuous) (IRConst (VTuple (VFloat 1) (VFloat 2)))) [])
  , KnownFamily "ir-conformsto-lowering-gaps-in-text-backends" ["python", "julia"]
      (AsIf (const (irMap conformsUnitUnchecked)))
      (repro [] ITBool (IRConformsTo TUnit (IRConst (VBool True))) [])
  , KnownFamily "ir-conformsto-lowering-gaps-in-text-backends" ["python", "julia"]
      (ByAnswer (\c _ a -> raisedWith "module did not load" a
                           && not (null [ () | IRConformsTo _ x <- universe (icBody c), not (isVar x) ])))
      -- Python cannot parse the walrus a let lowers to inside the
      -- comprehension a list check iterates; Julia cannot parse a field
      -- access on a negative literal (@-1.0.t1@).
      (repro [] (ITTuple ITBool ITBool)
         (IRConstruct TgTuple
            [ IRConformsTo (ListOf TFloat) (IRLetIn "l0" (IRConst (VInt 1)) (IRConst (VList (ListCont (VFloat 1) EmptyList))))
            , IRConformsTo (Tuple TFloat TFloat) (IRConst (VFloat (-1))) ])
         [])
  ]
  where
    isValue (Interpreted _) = True
    isValue _ = False
    raisedWith needle (Raised m) = needle `isInfixOf` m
    raisedWith _ _ = False
    hasNormalDensity e = not (null [ () | IRDensity IRNormal _ _ <- universe e ])
    tupleDomain d = case d of
      MultiTuple _ _ -> True
      MultiEither l r -> tupleDomain l || tupleDomain r
      _ -> False
    isVar (IRVar _) = True
    isVar _ = False
    isSampled (Sampled _) = True
    isSampled _ = False
    linearUniform x = case x of
      IRDensity IRUniform Linear _ -> True
      IRCumulative IRUniform _ _ -> True
      _ -> False

-- | Every subexpression, the expression itself included.
universe :: IRExpr -> [IRExpr]
universe e = e : concatMap universe (getIRSubExprs e)

-- | @a && b@ and @a || b@ as the backends evaluate them: the right operand
-- only when the left does not decide.
shortCircuit :: IRExpr -> IRExpr
shortCircuit e = case e of
  IROp OpAnd a b -> IRIf a b (IRConst (VBool False))
  IROp OpOr a b -> IRIf a (IRConst (VBool True)) b
  _ -> e

-- | @max@ as each backend evaluates it. Python's builtin keeps the first
-- argument unless the second is greater (so a NaN wins only in front, and
-- @max(0.0, -0.0)@ is @0.0@); Julia's is IEEE 754-2019 @maximum@ (a NaN
-- anywhere wins, and -0 is below +0). The interpreter's is Haskell's 'max',
-- @if x <= y then y else x@ (so a NaN wins only in front, and of two equal
-- zeros the second is kept).
--
-- The same ticket covers the max /reduction/ ('BReduce' 'ROpMax', the
-- max-product semiring's enumerated sum), 'backendMaxReduce'.
backendMax :: String -> IRExpr -> IRExpr
backendMax backend e = case e of
  IROp OpMax a b -> IRLetIn "mx_a" a (IRLetIn "mx_b" b (maxPick backend (IRVar "mx_a") (IRVar "mx_b")))
  _ -> e

-- | One step of each backend's @max@, on two cheap (let-bound) operands.
maxPick :: String -> IRExpr -> IRExpr -> IRExpr
maxPick backend x y
  | backend == "python" = IRIf (gtE y x) y x
  | otherwise =
      IRIf (isNaNE x) x $ IRIf (isNaNE y) y $ IRIf (gtE x y) x $ IRIf (gtE y x) y $
        -- Equal: only a pair of zeros of different sign can still differ.
        IRIf (IRConformsTo TFloat x)
             (IRIf (gtE (IROp OpDiv (IRConst (VFloat 1)) x) (IRConst (VFloat 0))) x y)
             x

-- | The max reduction as each backend evaluates it, wherever the reduced
-- tensor's length is statically known (a 'BTensor' literal, a 'BMap' over
-- one, or a variable let-bound to either), as a fold of 'maxPick' over its
-- elements. Python's @max@ of an iterable starts from the first element and
-- keeps it unless a later one is greater (so a NaN wins only in front);
-- Julia's @maximum(xs; init=-Inf)@ folds its IEEE @max@ from -inf (a NaN
-- anywhere wins). The interpreter folds Haskell's 'max' from the right, from
-- -inf, so a NaN wins only in front, and then only over what follows it:
-- @[1, NaN, 5]@ reduces to 1.
backendMaxReduce :: String -> IRExpr -> IRExpr
backendMaxReduce backend = go M.empty
  where
    go env e = case e of
      IRLetIn v x b -> let x' = go env x in IRLetIn v x' (go (bind v (staticLength env x') env) b)
      IRLambda v b -> IRLambda v (go (M.delete v env) b)
      IRBuiltin (BReduce ROpMax 0) [t] ->
        let t' = go env t
        in maybe (IRBuiltin (BReduce ROpMax 0) [t']) (fold t') (staticLength env t')
      _ -> irDescend (go env) e
    bind v = maybe (M.delete v) (M.insert v)
    staticLength env x = case x of
      IRBuiltin (BTensor [EFixed n]) _ -> Just n
      IRBuiltin BMap [_, t] -> staticLength env t
      IRVar v -> M.lookup v env
      IRLetIn v a b -> staticLength (bind v (staticLength env a) env) b
      _ -> Nothing
    el i = IRBuiltin (BIndex 0) [IRVar "rmx_t", IRConst (VInt i)]
    acc = IRVar "rmx_acc"
    step i rest = IRLetIn "rmx_x" (el i) (IRLetIn "rmx_acc" (maxPick backend acc (IRVar "rmx_x")) rest)
    fold t n = IRLetIn "rmx_t" t $
      if backend == "python"
        then if n == 0 then IRError "max() arg is an empty sequence"
             else IRLetIn "rmx_acc" (el 0) (foldr step acc [1 .. n - 1])
        else IRLetIn "rmx_acc" (IRConst (VFloat (-1 / 0))) (foldr step acc [0 .. n - 1])

-- | @sign@ as each backend evaluates it. Python's runtime @sign@ answers the
-- ints -1, 0 and 1 (1 at a NaN); Julia's keeps a zero's sign and a NaN. The
-- interpreter answers a float for a float, the positive zero for either
-- zero, and refuses a NaN.
backendSign :: String -> IRExpr -> IRExpr
backendSign backend e = case e of
  IRUnaryOp OpSign a -> IRLetIn "sg_a" a (IRIf (IRConformsTo TFloat x) (pick (VFloat 0) (VFloat 1)) (pick (VInt 0) (VInt 1)))
  _ -> e
  where
    x = IRVar "sg_a"
    neg v = case v of
      VFloat f -> VFloat (negate f)
      VInt i -> VInt (negate i)
      _ -> v
    pick zero one
      | backend == "python" =
          IRIf (ltE x (IRConst zero)) (IRConst (VInt (-1))) $
            IRIf (IROp OpAnd (IROp OpEq x x) (IRUnaryOp OpNot (gtE x (IRConst zero)))) (IRConst (VInt 0)) (IRConst (VInt 1))
      | otherwise =
          IRIf (isNaNE x) x $ IRIf (gtE x (IRConst zero)) (IRConst one) $
            IRIf (ltE x (IRConst zero)) (IRConst (neg one)) x

-- | Python's uniform density and CDF, which answer ints outside [0, 1] (and
-- the density inside it), and whose CDF is 1 at a NaN (so its log is 0).
pythonUniform :: IRExpr -> IRExpr
pythonUniform e = case e of
  IRDensity IRUniform Linear a -> IRLetIn "un_a" a $
    IRIf (IROp OpAnd (geE x (IRConst (VFloat 0))) (leE x (IRConst (VFloat 1)))) (IRConst (VInt 1)) (IRConst (VInt 0))
  IRCumulative IRUniform Linear a -> IRLetIn "un_a" a $
    IRIf (ltE x (IRConst (VFloat 0))) (IRConst (VInt 0)) (IRIf (leE x (IRConst (VFloat 1))) x (IRConst (VInt 1)))
  IRCumulative IRUniform Log a -> IRLetIn "un_a" a $
    IRIf (ltE x (IRConst (VFloat 0))) (IRConst (VFloat (-1 / 0))) $
      IRIf (leE x (IRConst (VFloat 1)))
           (IRIf (IROp OpEq x (IRConst (VFloat 0))) (IRConst (VFloat (-1 / 0))) (IRUnaryOp OpLog x))
           (IRConst (VFloat 0))
  _ -> e
  where x = IRVar "un_a"

-- | 'IRConformsTo' as both text backends lower it: a unit or theta-tree
-- slot is not checked (any value conforms), where the interpreter checks it.
conformsUnitUnchecked :: IRExpr -> IRExpr
conformsUnitUnchecked e = case e of
  IRConformsTo t a -> IRConformsTo (loosen t) a
  _ -> e
  where
    loosen t = case t of
      TUnit -> TVarR (TV "unchecked")
      TThetaTree -> TVarR (TV "unchecked")
      ListOf a -> ListOf (loosen a)
      Tuple a b -> Tuple (loosen a) (loosen b)
      TEither a b -> TEither (loosen a) (loosen b)
      _ -> t

gtE, ltE, geE, leE :: IRExpr -> IRExpr -> IRExpr
gtE a b = IROp OpGreaterThan a b
ltE a b = IROp OpLessThan a b
geE a b = IROp OpOr (gtE a b) (IROp OpEq a b)
leE a b = IROp OpOr (ltE a b) (IROp OpEq a b)

isNaNE :: IRExpr -> IRExpr
isNaNE x = IRUnaryOp OpNot (IROp OpEq x x)

-- | Whether some element of a rank-1 tensor satisfies the test.
countWhere :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
countWhere test t = gtE (IRBuiltin (BReduce ROpAdd 0)
                           [IRBuiltin BMap [IRLambda "cw_x" (IRIf (test (IRVar "cw_x")) (IRConst (VFloat 1)) (IRConst (VFloat 0))), t]])
                        (IRConst (VFloat 0))

-- | Log-sum-exp as each text backend reduces it: around its @max@ of the
-- terms, so a +inf term makes @exp(inf - inf)@ and the sum NaN (where the
-- interpreter, folding pairwise, answers +inf when no other term is finite).
-- Python's @max@ also skips a NaN that is not in front, so terms that are
-- all -inf or NaN, the first not NaN, give -inf (the interpreter, and
-- Julia, answer NaN).
backendLogSumExp :: String -> IRExpr -> IRExpr
backendLogSumExp backend e = case e of
  IRBuiltin (BReduce ROpLogSumExp 0) [t] ->
    IRLetIn "lse_t" t $ IRLetIn "lse_r" (IRBuiltin (BReduce ROpLogSumExp 0) [IRVar "lse_t"]) $
      (if backend == "python" then IRIf pythonMaxIsNegInf negInf else id) $
        IRIf (countWhere (\x -> IROp OpEq x posInf) (IRVar "lse_t")) (IRConst (VFloat (0 / 0))) (IRVar "lse_r")
  _ -> e
  where
    posInf = IRConst (VFloat (1 / 0))
    negInf = IRConst (VFloat (-1 / 0))
    pythonMaxIsNegInf =
      IROp OpAnd (IRUnaryOp OpNot (isNaNE (IRBuiltin (BIndex 0) [IRVar "lse_t", IRConst (VInt 0)])))
                 (IRUnaryOp OpNot (countWhere (\x -> IROp OpAnd (IROp OpEq x x) (IRUnaryOp OpNot (IROp OpEq x negInf))) (IRVar "lse_t")))

-- | The family a disagreement belongs to, if any: each family alone, then
-- every alternative semantics of its backend at once (a case can hit two).
knownDisagreement :: IRDisagreement -> IO (Maybe String)
knownDisagreement d = do
  singles <- mapM (\kf -> fmap (\ok -> if ok then Just (kfTicket kf) else Nothing) (matches [kf])) applicable
  case [ t | Just t <- singles ] of
    (t : _) -> return (Just t)
    [] -> do
      let rewrites = [ kf | kf@KnownFamily{kfMatch = AsIf _} <- applicable ]
      ok <- if length rewrites > 1 then matches rewrites else return False
      return (if ok then Just (intercalate " + " (map kfTicket rewrites)) else Nothing)
  where
    applicable = [ kf | kf <- knownDisagreements, idBackend d `elem` kfBackends kf ]
    matches kfs = case [ f | KnownFamily{kfMatch = ByAnswer f} <- kfs ] of
      (f : _) -> return (f (idCase d) (idInterp d) (idAnswer d))
      [] -> do
        let rewrite = foldr (.) id [ r (idBackend d) | KnownFamily{kfMatch = AsIf r} <- kfs ]
            c = idCase d
        o <- interpretIRCase c { icBody = rewrite (icBody c) } (idArgs d)
        return $ case o of
          InterpRefusal _ -> False
          _ -> either (const False) (const True) (judge o (idAnswer d))

-- | Judge one query: 'Nothing' if it agrees (with whether the Python
-- int-at-a-float-slot leniency applied), else the reason.
judge :: InterpOutcome -> Answer -> Either String Bool
judge o a = case (o, a) of
  (InterpRefusal _, _) -> Right False
  (InterpRaise _, Raised _) -> Right False
  (InterpRaise m, _) -> Left ("the interpreter raises (" ++ m ++ "), the backend answers")
  (Interpreted _, Raised m) -> Left ("the backend raises: " ++ m)
  (Interpreted v, Sampled toks) -> either (Left . ("values differ: " ++)) Right (valueAgrees v toks)
  (Interpreted _, other) -> Left ("unexpected answer " ++ show other)

-- ---------------------------------------------------------------------------
-- Running a batch of cases through a backend

-- | Per case: its emitted module (or the codegen's exception) and, per
-- argument vector, the interpreter's outcome.
type Prepared = (IRCase, Either String String, [([IRValue], InterpOutcome)])

-- | Run every case through one backend process; return each query's outcome
-- label (for tabulation) and the disagreements.
runCases :: String
         -> (Int -> IRCase -> IO (Either String String))
         -> String
         -> (FilePath -> [(Int, FilePath, IRCase)] -> String)
         -> (FilePath -> IO (String, String))
         -> [(IRCase, [([IRValue], InterpOutcome)])]
         -> IO ([String], [IRDisagreement])
runCases backend emit ext driver run cases = withSystemTempDirectory ("nest-irfuzz-" ++ backend) $ \dir -> do
  projectDir <- getCurrentDirectory
  sources <- sequence [ emit i c | (i, (c, _)) <- zip [0 ..] cases ]
  let prepared :: [Prepared]
      prepared = [ (c, s, qs) | ((c, qs), s) <- zip cases sources ]
      files = [ dir </> ("prog" ++ show i ++ ext) | i <- [0 .. length cases - 1] ]
  sequence_ [ writeFile f s | (f, (_, Right s, _)) <- zip files prepared ]
  let entries = [ (i, f, c) | (i, f, (c, Right _, _)) <- zip3 [0 ..] files prepared ]
      driverPath = dir </> ("driver" ++ ext)
  writeFile driverPath (driver projectDir entries)
  (out, err) <- run driverPath
  let parsed = mapMaybe parseAnswerLine (lines out)
      tailErr = oneLine (reverse (take 400 (reverse err)))
      -- A module that did not load answers every query with that, not with
      -- the error each call then meets.
      answerFor i j = case [ a | (i', Nothing, a) <- parsed, i' == i ] of
        (a : _) -> a
        [] -> case [ a | (i', Just j', a) <- parsed, i' == i, j' == j ] of
          (a : _) -> a
          [] -> Raised ("no answer from the " ++ backend ++ " process; stderr: " ++ tailErr)
      judged = [ (lbl, d)
               | (i, (c, src, qs)) <- zip [0 :: Int ..] prepared
               , (j, (args, o)) <- zip [0 ..] qs
               , let a = either (\e -> Raised ("codegen threw: " ++ e)) (const (answerFor i j)) src
               , let (lbl, d) = case judge o a of
                       Right lenient -> (outcomeLabel o ++ (if lenient then " (int at a float slot)" else ""), Nothing)
                       Left why -> ("disagreement", Just (IRDisagreement backend c args o a why (either id id src)))
               ]
  return (map fst judged, [ d | (_, Just d) <- judged ])
  where
    outcomeLabel o = case o of
      Interpreted _ -> "agrees: value"
      InterpRaise _ -> "agrees: both raise"
      InterpRefusal _ -> "interpreter refused (not compared)"

-- | The text backends emit a module per case; 'irCaseEnv' has no networks.
emitPython :: Int -> IRCase -> IO (Either String String)
emitPython _ c = fmap (fmap stubTorch) (forcedSource (return (Py.generateFunctions True (irCaseEnv c))))
  where stubTorch = unpack . replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") . pack

methodOf :: BodyKind -> String
methodOf NormalBody = "normal_params"
methodOf WriteLogitsBody = "writeLogits"
methodOf ProbBody = "forward"
methodOf IntegBody = "integrate"

pythonIRDriver :: FilePath -> [(Int, FilePath, IRCase)] -> String
pythonIRDriver projectDir entries = unlines $
  [ "import sys, signal"
  , "sys.path.insert(0, " ++ show projectDir ++ ")"
  , "import pythonLib as _pl"
  , "sys.setrecursionlimit(20000)"
  , "class _Timeout(Exception): pass"
  , "def _alarm(signum, frame): raise _Timeout('query exceeded its time limit')"
  , "signal.signal(signal.SIGALRM, _alarm)"
  , "def _out(s):"
  , "    sys.stdout.write(s + '\\n'); sys.stdout.flush()"
  , "def _msg(e):"
  , "    return (type(e).__name__ + ': ' + str(e)).replace('\\n', ' ')[:400]"
  ] ++ pythonSerializer ++ concatMap entry entries
  where
    entry (i, path, c) =
      [ "_ns = {}"
      , "try:"
      , "    exec(compile(open(" ++ show path ++ ").read(), " ++ show path ++ ", 'exec'), _ns)"
      , "    _loaded = True"
      , "except BaseException as _e:"
      , "    _out('L " ++ show i ++ " ' + _msg(_e))"
      , "    _loaded = False"
      , "if _loaded:"
      ] ++ concat (zipWith (query i c) [0 :: Int ..] (icArgs c)) ++ ["    pass"]
    query i c j args =
      [ "    try:"
      , "        signal.setitimer(signal.ITIMER_REAL, 10.0)"
      , "        _r = eval(" ++ show ("main." ++ methodOf (icKind c) ++ "(" ++ intercalate ", " (map Py.pyVal args) ++ ")") ++ ", _ns)"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('S " ++ show i ++ " " ++ show j ++ " ' + _ser(_r, _ns))"
      , "    except BaseException as _e:"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('E " ++ show i ++ " " ++ show j ++ " ' + _msg(_e))"
      ]

juliaIRDriver :: FilePath -> [(Int, FilePath, IRCase)] -> String
juliaIRDriver projectDir entries = unlines $
  [ "include(" ++ show (projectDir </> "juliaLib.jl") ++ ")"
  , "using .JuliaSPPLLib"
  , "_msg(e) = first(replace(sprint(showerror, e), '\\n' => ' '), 400)"
  ] ++ juliaSerializer ++ concatMap entry entries
  where
    entry (i, path, c) =
      [ "try"
      , "  include(" ++ show path ++ ")"
      , "catch e"
      , "  println(\"L " ++ show i ++ " \", _msg(e)); flush(stdout)"
      , "end"
      ] ++ concat [ [ "try"
                    , "  r = Base.invokelatest(" ++ intercalate ", " (("Prog" ++ show i ++ "." ++ fn c) : map Jl.juliaVal args) ++ ")"
                    , "  println(\"S " ++ show i ++ " " ++ show j ++ " \", join(_ser(r, String[]), \" \")); flush(stdout)"
                    , "catch e"
                    , "  println(\"E " ++ show i ++ " " ++ show j ++ " \", _msg(e)); flush(stdout)"
                    , "end" ]
                  | (j, args) <- zip [0 :: Int ..] (icArgs c) ]
    fn c = "main" ++ bodySuffix (icKind c)

-- | Each case carries the interpreter's outcome per argument vector.
runIRCasesPython :: [(IRCase, [([IRValue], InterpOutcome)])] -> IO ([String], [IRDisagreement])
runIRCasesPython = runCases "python" emitPython ".py" pythonIRDriver
  (\f -> (\(_, o, e) -> (o, e)) <$> runBounded "python3" [f])

runIRCasesJulia :: FilePath -> [(IRCase, [([IRValue], InterpOutcome)])] -> IO ([String], [IRDisagreement])
runIRCasesJulia julia cases = runCases "julia" emit ".jl" juliaIRDriver
  (\f -> (\(_, o, e) -> (o, e)) <$> runBounded julia (juliaTestFlags ++ [f])) cases
  where
    emit i c = fmap (fmap (\src -> "module Prog" ++ show i ++ "\nusing ..JuliaSPPLLib\n" ++ src ++ "\nend\n"))
                  (forcedSource (return (Jl.generateFunctions (irCaseEnv c))))

-- ---------------------------------------------------------------------------
-- Coverage

-- | The constructs a case's body reaches ('irConstructs' labels).
checkedIRConstructs :: IRCase -> [String]
checkedIRConstructs = sort . nub . irConstructs . irCaseFunction

-- | Every construct the generator's fixed-seed sample reaches: what
-- 'BackendCoverage' measures the corpus census under every config against.
irGeneratorConstructs :: [String]
irGeneratorConstructs = sort (nub (concatMap checkedIRConstructs fixedSample))

-- | Constructs of 'irConstructs'' inventory with no production yet, and
-- why. Later milestones own most of them.
noProduction :: [(String, String)]
noProduction =
  [ ("IRExpr:IRSample", "random draws: generate bodies are M4")
  , ("Builtin:BIndex, BListIndex, BMapList, BZip", "builtins and tensors are M3; M2's PResult bodies reach only the enumerated sum's BTensor, BMap and BReduce")
  , ("ConTag:ADT", "ADT values are built by implicit constructor functions; function groups are M3")
  , ("Symbol constants", "neither text backend can render a VSymbol constant (pyVal/juliaVal have no case); symbols reach the backends only as network inputs")
  ]

-- ---------------------------------------------------------------------------
-- Default-tier checks on the generator itself (pure and fast: no backend)

-- | Every 'Operand', 'UnaryOperand' and 'Accessor', as 'irConstructs' labels
-- them. The cases below are complete matches, so a new constructor is a
-- compile error here until it is listed (and given a production).
operandLabels, unaryLabels, accessorLabels :: [String]
operandLabels = map (\op -> "Operand:" ++ show (op `asTypeOf` operandWitness op))
  [OpPlus, OpMult, OpGreaterThan, OpLessThan, OpDiv, OpSub, OpOr, OpAnd, OpEq, OpApprox, OpMax, OpIntDiv, OpMod]
  where operandWitness op = case op of
          OpPlus -> op; OpMult -> op; OpGreaterThan -> op; OpLessThan -> op; OpDiv -> op; OpSub -> op
          OpOr -> op; OpAnd -> op; OpEq -> op; OpApprox -> op; OpMax -> op; OpIntDiv -> op; OpMod -> op
unaryLabels = map (\op -> "UnaryOperand:" ++ show (op `asTypeOf` unaryWitness op))
  [OpNeg, OpSign, OpAbs, OpNot, OpExp, OpLog, OpIsAny]
  where unaryWitness op = case op of
          OpNeg -> op; OpSign -> op; OpAbs -> op; OpNot -> op; OpExp -> op; OpLog -> op; OpIsAny -> op
accessorLabels = map (\a -> "Accessor:" ++ takeWhile (/= ' ') (show (accessorWitness a)))
  [AcFst, AcSnd, AcHead, AcTail, AcFromLeft, AcFromRight, AcIsLeft, AcIsRight, AcTheta 0, AcSubtree 0]
  where accessorWitness a = case a of
          AcFst -> a; AcSnd -> a; AcHead -> a; AcTail -> a; AcFromLeft -> a; AcFromRight -> a
          AcIsLeft -> a; AcIsRight -> a; AcTheta _ -> a; AcSubtree _ -> a

-- | The 'IRExpr' constructors with a production: all but 'IRSample'
-- ('noProduction'). 'IRBuiltin' only through M2's enumerated sums.
exprLabels :: [String]
exprLabels = map ("IRExpr:" ++)
  [ "IRIf", "IRSelect", "IROp", "IRUnaryOp", "IRConst", "IRConstruct", "IRDestruct", "IRDensity"
  , "IRCumulative", "IRLetIn", "IRVar", "IRLambda", "IRApply", "IRIsPossible", "IRError", "IRConformsTo"
  , "IRBuiltin" ]

-- | A fixed-seed sample of plans per semiring, as the plan coverage check
-- reads it.
fixedPlans :: SemiringChoice -> [PPlan]
fixedPlans c = unGen (vectorOf 300 drawPlan) (mkQCGen (20261013 + fromEnum c)) 30
  where drawPlan = choose (1, 7) >>= \size -> evalStateT (genPlan c [("a0", ITFloat)] size) 0

-- | A fixed-seed sample of cases, as the coverage check reads it.
fixedSample :: [IRCase]
fixedSample = unGen (vectorOf 400 genIRCase) (mkQCGen 20261013) 30

irFuzzGeneratorTests :: TestTree
irFuzzGeneratorTests = testGroup "IR fuzz generator"
  [ testProperty "a drawn case type-checks at the type it was drawn at" $
      withMaxSuccess 300 $ forAll genIRCase $ \c ->
        either (\e -> counterexample (renderIRCase c ++ e) False) (const (property True)) (irCaseWellTyped c)
  , testProperty "every shrink candidate type-checks" $
      withMaxSuccess 30 $ forAll genIRCase $ \c ->
        conjoin [ either (\e -> counterexample (renderIRCase c' ++ e) False) (const (property True)) (irCaseWellTyped c')
                | c' <- take 40 (shrinkIRCase c) ]
  , testCase "a fixed-seed sample reaches every Operand, UnaryOperand, Accessor and drawn IRExpr" $ do
      let reached = nub (concatMap checkedIRConstructs fixedSample)
      assertEqual "unreached" [] (filter (`notElem` reached) (operandLabels ++ unaryLabels ++ accessorLabels ++ exprLabels))
  , testCase "every filed interpreter refusal still refuses, with its reason" $
      mapM_ (\(why, ticket, c) -> do
               o <- interpretIRCase c (head (icArgs c))
               case o of
                 InterpRefusal r -> assertEqual ticket why (refusalKey r)
                 other -> assertFailure (ticket ++ ": the repro no longer refuses (" ++ show other
                                         ++ "); if the bug is fixed, drop its knownRefusals entry"))
            knownRefusals
  , testCaseInfo "every filed disagreement family still reproduces, on its backends only" $ do
      let prepared c = (\o -> (c, [(head (icArgs c), o)])) <$> interpretIRCase c (head (icArgs c))
      cases <- mapM (prepared . kfRepro) knownDisagreements
      (_, pyD) <- runIRCasesPython cases
      julia <- findExecutable "julia"
      jlD <- maybe (return []) (\j -> snd <$> runIRCasesJulia j cases) julia
      let backends = "python" : maybe [] (const ["julia"]) julia
      sequence_
        [ do let ds = [ d | d <- pyD ++ jlD, idBackend d == b, show (idCase d) == show (kfRepro kf) ]
             if b `elem` kfBackends kf
               then case ds of
                 [d] -> do t <- knownDisagreement d
                           assertEqual (kfTicket kf ++ " on " ++ b ++ ": recognised as") (Just (kfTicket kf)) t
                 [] -> assertFailure (kfTicket kf ++ ": the repro no longer disagrees on " ++ b
                                     ++ "; if the bug is fixed, drop (or narrow) its knownDisagreements entry")
                 _ -> assertFailure (kfTicket kf ++ ": two entries share this repro; give each its own")
               else assertEqual (kfTicket kf ++ ": the repro disagrees on " ++ b ++ ", which the entry does not list")
                                [] (map idWhy ds)
        | kf <- knownDisagreements, b <- backends ]
      return (maybe "no julia on the PATH: the Julia arm was skipped" (const "") julia)
  , testCase "a fixed-seed sample of plans reaches every PResult combinator, in every semiring" $
      assertEqual "unreached (semiring, combinator)" []
        [ (c, l) | c <- [minBound .. maxBound], let reached = nub (concatMap planNodes (fixedPlans c))
                 , l <- planLabels c, l `notElem` reached ]
  , testCase "a fixed-seed sample reaches both PResult bodies, both layouts, and every semiring's reductions" $ do
      let shapes = nub [ (icKind c, sh) | c <- fixedSample, Just sh <- [icShape c] ]
          reached = nub (concatMap checkedIRConstructs fixedSample)
      assertEqual "unreached (body, (semiring, stripped))" []
        [ k | k <- [ (b, (c, st)) | b <- [ProbBody, IntegBody], c <- [minBound .. maxBound], st <- [False, True] ]
            , k `notElem` shapes ]
      assertEqual "unreached" [] (filter (`notElem` reached)
        [ "Builtin:BReduce ROpAdd", "Builtin:BReduce ROpLogSumExp", "Builtin:BReduce ROpMax", "Builtin:BMap", "Builtin:BTensor" ])
  , testCase "a fixed-seed sample reaches both densities and cumulatives in both spaces" $ do
      let reached = nub (concatMap checkedIRConstructs fixedSample)
          wanted = [ k ++ ":" ++ d ++ " " ++ ls | k <- ["Density", "Cumulative"], d <- ["IRNormal", "IRUniform"], ls <- ["Linear", "Log"] ]
      assertEqual "unreached" [] (filter (`notElem` reached) wanted)
  ]
