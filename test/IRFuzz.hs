{-# LANGUAGE ScopedTypeVariables #-}

-- | The IR fuzz generator (docs-repo design @ir-fuzz-generator@), milestones
-- M1 (deterministic-value IR), M2 ('PResult' bodies in every semiring, see
-- "PResult bodies" below), M3 (builtins, tensors, ADTs and function groups,
-- see "Function groups" below) and M4 (generate bodies judged by replaying
-- the backends' draws, see "Generate bodies"; and the batched arm, see "The
-- batched arm") on the scalar Python and Julia backends and the batched
-- PyTorch one, with the interpreter as the oracle.
--
-- 'prop_Fuzz_BackendsAgree' reaches the backends only through what the SPLL
-- compiler emits from programs its generator can draw. This module draws
-- 'IREnv's directly instead, within the IR's type contract
-- ('SPLL.IRTypeCheck'), so a construct is exercised because it has a
-- production here, not because some SPLL program happens to compile to it.
--
-- One drawn case is one function group @main@ whose normal-parameter body (or
-- writeLogits body: same calling convention, different method) is a plain
-- value expression over its parameters and a few top-level constants, next to
-- up to three helper groups it may call and one ADT declaration. It
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
  , Helper(..)
  , HelperShape(..)
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
  , BatchedIRCase(..)
  , prepareBatchedIRCase
  , runIRCasesBatched
  , checkedIRConstructs
  , caseFeatures
  , irGeneratorConstructs
  , noProduction
  , valueAgrees
  , irFuzzGeneratorTests
  ) where

import Control.Exception (SomeException, SomeAsyncException(..), ErrorCall(..), try, evaluate, fromException, throwIO)
import Control.Monad (replicateM)
import Control.Monad.State.Strict (StateT, evalStateT, get, gets, put, lift, State, execState, evalState, modify)
import Data.Char (isSpace, toLower)
import Data.List (intercalate, isPrefixOf, isInfixOf, isSuffixOf, nub, sort)
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import System.Directory (getCurrentDirectory, findExecutable)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Timeout (timeout)
import System.IO (Handle, hPutStrLn, hFlush, hGetLine, hIsEOF, hSetBuffering, BufferMode(..), openFile, IOMode(..))
import System.IO.Unsafe (unsafePerformIO)
import System.Process (createProcess, proc, CreateProcess(std_in, std_out, std_err), StdStream(..), ProcessHandle, terminateProcess)
import Control.Concurrent.MVar (MVar, newMVar, modifyMVar)
import Data.IORef (newIORef, readIORef, modifyIORef')
import Test.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertEqual, assertFailure, assertBool)
import Text.Read (readMaybe)
import Data.Text (pack, unpack, replace)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.IRTypeCheck (IRType(..), checkIREnv, showIRType, showIRTypeError, irTypeOfRType)
import SPLL.Semiring
import SPLL.IRCompiler (stripBranchCount)
import Control.Monad.Writer.Lazy (runWriterT)
import SPLL.Typing.RType (RType(..), TVarR(..), shapeNumel)
import IRInterpreter (generateDet, generateReplay)
import qualified SPLL.CodeGenPyTorch as Py
import qualified SPLL.CodeGenJulia as Jl
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import SPLL.IRSelectPass (selectPassEnv)
import BackendAgreement (Answer(..), parseAnswerLine, pythonSerializer, juliaSerializer, batchedRefusalReason,
                         readNum, runBounded, forcedSource, oneLine, probAgrees, irConstructs)
import End2EndTesting (juliaTestFlags, qualifyConstructors, findTorchPython, noTorch)
import Data.Either (rights)

-- ---------------------------------------------------------------------------
-- Cases

-- | Which deterministic body of @main@ the expression is: its normal-parameter
-- function, its writeLogits function, or (a 'PResult'-shaped body, M2) its
-- probability or integrate function. All are plain functions of the group's
-- parameters; they differ in the method name each backend emits.
--
-- A generate body (M4, 'GenBody') is a value expression that may draw
-- ('IRSample'). It is judged by replaying the backend's draws through the
-- interpreter ('icDraws'): see "Generate bodies" below.
data BodyKind = NormalBody | WriteLogitsBody | ProbBody | IntegBody | GenBody deriving (Show, Eq)

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
  , icHelpers :: [Helper]             -- ^ the other function groups (M3), in definition order
  , icADTs   :: [ADTDecl]             -- ^ the env's ADT declarations (M3)
  , icDraws  :: ([Double], [Double])
    -- ^ a generate body's random stream (M4): what each backend's @rand()@
    -- and @randn()@ return, in call order, and what the interpreter's draws
    -- take ('interpretIRCase'). Empty for a deterministic body.
  } deriving (Show)

-- | A helper function group (M3): a normal-parameter function @main@ (and
-- later helpers) may call as @<name>_normal@.
data Helper = Helper
  { hName   :: String
  , hParams :: [(String, IRType)]
  , hResult :: IRType
  , hBody   :: IRExpr                 -- ^ under the parameter lambdas
  , hShape  :: HelperShape
  , hGen    :: Bool                   -- ^ a generate function (M4): called as @<name>_gen@, and may draw
  } deriving (Show)

-- | How a helper was drawn: a plain body, or one of the recursion shapes,
-- each recursing on a decreasing measure.
data HelperShape
  = HPlain      -- ^ any body over its parameters and the earlier helpers
  | HCountdown  -- ^ recursion on an Int measure, bounded both ways
  | HListRec    -- ^ structural recursion on a list's tail
  | HMutual     -- ^ one of a pair of functions recursing into each other on an Int measure
  deriving (Show, Eq, Enum, Bounded)

-- | The name a helper is called by.
helperRef :: Helper -> String
helperRef h = hName h ++ helperSuffix (hGen h)

-- | The suffix a helper is called by: a generate function's, or a normal
-- function's.
helperSuffix :: Bool -> String
helperSuffix gen = if gen then "_gen" else "_normal"

helperType :: Helper -> IRType
helperType h = foldr (ITArrow . snd) (hResult h) (hParams h)

-- | The body with its parameter lambdas.
irCaseFunction :: IRCase -> IRExpr
irCaseFunction c = foldr IRLambda (icBody c) (map fst (icParams c))

-- | Every body of the case: @main@'s, then each helper's (unwrapped).
caseBodies :: IRCase -> [IRExpr]
caseBodies c = icBody c : map hBody (icHelpers c)

-- | The case with one rewrite applied to every body.
onBodies :: (IRExpr -> IRExpr) -> IRCase -> IRCase
onBodies f c = c { icBody = f (icBody c), icHelpers = [ h { hBody = f (hBody h) } | h <- icHelpers c ] }

irCaseEnv :: IRCase -> IREnv
irCaseEnv c = IREnv (map helperGroup (icHelpers c) ++ [group]) (icADTs c) (icConsts c)
  where
    helperGroup h = let hdecl = Just (foldr IRLambda (hBody h) (map fst (hParams h)), "") in IRFunGroup
      { groupName = hName h, genFun = if hGen h then hdecl else Nothing, writeLogitsFun = Nothing
      , normalFun = if hGen h then Nothing else hdecl
      , probFun = Nothing, integFun = Nothing
      , groupDoc = "", refusedVariants = [], sampleDomain = Nothing, maskVariantOf = Nothing }
    decl = Just (irCaseFunction c, "")
    group = IRFunGroup
      { groupName = "main", genFun = if icKind c == GenBody then decl else Nothing
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
  GenBody -> "_gen"

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
  tys <- either (Left . showIRTypeError) Right (checkIREnv (irCaseEnv c))
  mapM_ (\h -> case lookup (helperRef h) tys of
                  Nothing -> Left ("no type for " ++ helperRef h)
                  Just th | isJust (instanceOf th (helperType h) IM.empty) -> Right ()
                          | otherwise -> Left (helperRef h ++ " drawn at " ++ showIRType (helperType h)
                                               ++ ", checked as " ++ showIRType th))
        (icHelpers c)

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
  ++ [ "  data " ++ show d | d <- icADTs c ]
  ++ concat [ [ "  helper " ++ helperRef h ++ " (" ++ show (hShape h) ++ ") :: " ++ showIRType (helperType h)
              , "    params " ++ unwords (map fst (hParams h))
              , "    body " ++ show (hBody h) ]
            | h <- icHelpers c ]
  ++ [ "  const " ++ n ++ " = " ++ show v | (n, v) <- icConsts c ]
  ++ [ "  params " ++ unwords (map fst (icParams c))
     , "  body " ++ show (icBody c) ]

-- ---------------------------------------------------------------------------
-- The generator

-- | A drawn name is fresh: one counter runs over the whole case (helpers
-- included), so every binder is distinct and no case exercises shadowing (a
-- property of the source language, not of the IR the compiler emits). The
-- state also carries the case's ADT declarations, which types and values are
-- drawn over.
--
-- 'gsDraws' says whether the body being drawn may draw ('IRSample'): a
-- generate body or a generate helper's (M4), not a deterministic one.
data GS = GS { gsNext :: !Int, gsADTs :: [ADTDecl], gsDraws :: Bool }

type G = StateT GS Gen

runG :: [ADTDecl] -> G a -> Gen a
runG ds m = evalStateT m (GS 0 ds False)

-- | Run a generator with draws allowed or not, restoring the setting after.
withDraws :: Bool -> G a -> G a
withDraws d m = do
  old <- gets gsDraws
  modify (\st -> st { gsDraws = d })
  r <- m
  modify (\st -> st { gsDraws = old })
  return r

fresh :: String -> G String
fresh pre = do
  s <- get
  put s { gsNext = gsNext s + 1 }
  return (pre ++ show (gsNext s))

liftG :: Gen a -> G a
liftG = lift

adtsG :: G [ADTDecl]
adtsG = gets gsADTs

frequencyG :: [(Int, G a)] -> G a
frequencyG xs = liftG (frequency [ (w, return m) | (w, m) <- xs ]) >>= id

-- | What a drawn type may hold beyond scalars, lists, tuples, 'Either' and
-- rank-1 tensors: function types, and the case's ADTs. Function types are not
-- drawn where a backend's caller passes or reads the value (@main@'s
-- parameters and result, the constants): no text backend renders a closure
-- argument, nor serialises one.
--
-- 'ITThetaTree' only appears where a theta accessor consumes it (a theta tree
-- is a Python tuple of lists and has no token form to compare), and
-- 'ITSymbol' not at all (no text backend can render a symbol constant).
-- Tensors are rank 1 only: neither text backend emits a higher rank
-- ('noProduction').
data TyOpts = TyOpts { tyArrows :: Bool, tyADTs :: [String] }

genTypeWith :: TyOpts -> Int -> Gen IRType
genTypeWith o d
  | d <= 0 = scalar
  | otherwise = frequency $
      [ (6, scalar)
      , (1, ITList <$> sub)
      , (1, ITTuple <$> sub <*> sub)
      , (1, ITEither <$> sub <*> sub)
      , (1, (\k a -> ITTensor [EFixed k] a) <$> choose (0, 3) <*> sub)
      ] ++ [ (1, ITArrow <$> sub <*> sub) | tyArrows o ]
  where
    sub = genTypeWith o (d - 1)
    scalar = frequency $ [(3, return ITFloat), (2, return ITInt), (2, return ITBool), (1, return ITUnit)]
                         ++ [ (2, elements (map ITADT (tyADTs o))) | not (null (tyADTs o)) ]

-- | A type for a value a backend's caller passes or reads: no functions.
genValueType :: [ADTDecl] -> Int -> Gen IRType
genValueType ds = genTypeWith (TyOpts False (map dataName ds))

-- | A type inside a body: functions too.
genTy :: Int -> G IRType
genTy d = genTySuchThat d (const True)

genTySuchThat :: Int -> (IRType -> Bool) -> G IRType
genTySuchThat d ok = do
  ds <- adtsG
  liftG (genTypeWith (TyOpts True (map dataName ds)) d `suchThat` ok)

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
  ITArrow _ _ -> False
  ITTensor _ _ -> False
  ITList a -> isEquatable a
  ITTuple a b -> isEquatable a && isEquatable b
  ITEither a b -> isEquatable a && isEquatable b
  _ -> True

hasArrow :: IRType -> Bool
hasArrow t = case t of
  ITArrow _ _ -> True
  ITList a -> hasArrow a
  ITTuple a b -> hasArrow a || hasArrow b
  ITEither a b -> hasArrow a || hasArrow b
  ITTensor _ a -> hasArrow a
  _ -> False

isArrow :: IRType -> Bool
isArrow (ITArrow _ _) = True
isArrow _ = False

-- | What 'IRConformsTo' is drawn at: the shapes of a query value, so no
-- functions and no tensors.
isConformable :: IRType -> Bool
isConformable t = not (hasArrow t) && noTensor t
  where
    noTensor x = case x of
      ITTensor _ _ -> False
      ITList a -> noTensor a
      ITTuple a b -> noTensor a && noTensor b
      ITEither a b -> noTensor a && noTensor b
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

-- | A value of a function-free type, over the case's ADTs.
genValue :: [ADTDecl] -> IRType -> Gen IRValue
genValue ds t = case t of
  ITBool -> VBool <$> arbitrary
  ITInt -> VInt <$> genInt
  ITFloat -> VFloat <$> genFloat
  ITUnit -> return VUnit
  ITThetaTree -> VThetaTree <$> genTheta thetaDepth
  ITList a -> do
    n <- frequency [(2, return 0), (3, choose (1, 3))]
    xs <- vectorOf n (genValue ds a)
    return (VList (foldr ListCont EmptyList xs))
  ITTuple a b -> VTuple <$> genValue ds a <*> genValue ds b
  ITEither a b -> oneof [VEither . Left <$> genValue ds a, VEither . Right <$> genValue ds b]
  ITTensor sh a -> VTensor sh <$> vectorOf (shapeNumel sh) (genValue ds a)
  ITADT n | (cs@(_ : _)) <- adtCtors ds n -> do
    (c, fts) <- elements cs
    VADT c <$> mapM (genValue ds) fts
  _ -> error ("IRFuzz.genValue: no values drawn at " ++ show t)

-- ---------------------------------------------------------------------------
-- ADTs (M3)

-- | The case's ADT: none in three cases of four, else one type @Qt@ of one to
-- three constructors with zero to two scalar fields each. The names are
-- fixed (none is reserved or mangled in either backend), the field names
-- unique. Values of it are built by its implicit constructor functions, read
-- by its field accessors (guarded by its constructor tests: an accessor
-- applied to another constructor is a Haskell 'error' in the interpreter)
-- and compared by equality; constants and arguments of it are drawn too.
genADTs :: Gen [ADTDecl]
genADTs = frequency [(3, return []), (1, (: []) <$> one)]
  where
    one = do
      k <- choose (1, 3)
      ctors <- mapM ctor (take k ["Qa", "Qb", "Qc"])
      return (ADTDecl "Qt" ctors Nothing)
    ctor c = do
      nf <- choose (0, 2)
      tys <- vectorOf nf (elements [TFloat, TInt, TBool])
      return (c, [ (map toLower c ++ show i, rt) | (i, rt) <- zip [0 :: Int ..] tys ])

-- | The constructors of an ADT, with their field types.
adtCtors :: [ADTDecl] -> String -> [(String, [IRType])]
adtCtors ds n = [ (c, map (fieldTy . snd) fs) | d <- ds, dataName d == n, (c, fs) <- constructors d ]

-- | Every field: its ADT, constructor, accessor and type.
adtFields :: [ADTDecl] -> [(String, String, String, IRType)]
adtFields ds = [ (dataName d, c, f, fieldTy rt) | d <- ds, (c, fs) <- constructors d, (f, rt) <- fs ]

fieldTy :: RType -> IRType
fieldTy rt = fromMaybe (error ("IRFuzz.fieldTy: " ++ show rt)) (irTypeOfRType rt)

-- ---------------------------------------------------------------------------
-- Expressions

applyAll :: IRExpr -> [IRExpr] -> IRExpr
applyAll = foldl IRApply

intE :: Int -> IRExpr
intE = IRConst . VInt

floatE :: Double -> IRExpr
floatE = IRConst . VFloat

consE :: IRExpr -> IRExpr -> IRExpr
consE h t = IRConstruct TgCons [h, t]

type Scope = [(String, IRType)]

-- | An expression of type @t@ over the variables in scope, of roughly the
-- given size. Function-typed variables in scope (helpers, parameters,
-- let-bound closures) are called.
genExpr :: Scope -> IRType -> Int -> G IRExpr
genExpr sc t n
  | n <= 0 = leaf sc t
  | otherwise = do
      ds <- adtsG
      draws <- gets gsDraws
      frequencyG (general ++ calls ++ anyBuiltins ++ adtAccessors ds ++ specific ds ++ sampling draws)
  where
    -- A draw (M4), only where the body may draw: a float, transformed by
    -- whatever the context makes of it.
    sampling draws = [ (6, drawG) | draws, t == ITFloat ]
                  -- a coin flip, the shape a Bernoulli draw compiles to
                  ++ [ (4, ltE (IRSample IRUniform) <$> genExpr sc ITFloat (n - 1)) | draws, t == ITBool ]
    half = n `div` 2
    third = n `div` 3
    general =
      [ (2, leaf sc t)
      , (3, IRIf <$> genExpr sc ITBool third <*> genExpr sc t third <*> genExpr sc t third)
      , (1, IRSelect <$> genExpr sc ITBool third <*> genExpr sc t third <*> genExpr sc t third)
      , (3, letIn)
      , (1, do s <- genTy 1; IRDestruct AcFst <$> genExpr sc (ITTuple t s) (n - 1))
      , (1, do s <- genTy 1; IRDestruct AcSnd <$> genExpr sc (ITTuple s t) (n - 1))
      , (1, guardedHead)
      , (1, guardedFromEither True)
      , (1, guardedFromEither False)
      , (1, betaRedex)
      ]
      ++ [ (1, IRIf <$> genExpr sc ITBool half <*> genExpr sc t half <*> return (IRError "drawn IRError")) | n > 4 ]
    letIn = do
      s <- genTy 1
      v <- fresh "l"
      IRLetIn v <$> genExpr sc s half <*> genExpr ((v, s) : sc) t half
    betaRedex = do
      s <- genTy 1
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
      s <- genTy 1
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
    -- A call of a function in scope (a helper, a parameter, a let-bound
    -- closure) whose result after some of its arguments is @t@. Fewer
    -- arguments than it takes is a partial application, a closure.
    calls = [ (4, do (f, as) <- liftG (elements cands)
                     let k = max 1 (n `div` (length as + 1))
                     applyAll (IRVar f) <$> mapM (\a -> genExpr sc a k) as)
            | not (null cands) ]
    cands = [ (v, as) | (v, ty) <- sc, as <- argPrefixes ty ]
    argPrefixes ty = case ty of
      ITArrow a b -> [ [a] | b == t ] ++ map (a :) (argPrefixes b)
      _ -> []
    -- Reads at any element type: a tensor at a key in range (a constant, or
    -- a drawn Int guarded by the tensor's static extent), a list at a
    -- constant index inside a cons prefix of known length. An index out of
    -- range is a value precondition, as 'OpIntDiv''s divisor is: the
    -- interpreter refuses it, Python reads from the end at a negative key.
    anyBuiltins = [ (1, tensorIndex), (1, listIndex) ]
    tensorIndex = do
      k <- liftG (choose (1, 3))
      te <- genExpr sc (ITTensor [EFixed k] t) half
      guarded <- liftG arbitrary
      if guarded
        then do
          v <- fresh "ix"
          key <- genExpr sc ITInt half
          dflt <- genExpr sc t half
          let x = IRVar v
          return (IRLetIn v key (IRIf (ltE x (intE 0)) dflt (IRIf (ltE x (intE k)) (IRBuiltin (BIndex 0) [te, x]) dflt)))
        else do
          i <- liftG (choose (0, k - 1))
          return (IRBuiltin (BIndex 0) [te, intE i])
    listIndex = do
      m <- liftG (choose (1, 2))
      pre <- replicateM m (genExpr sc t third)
      rest <- genExpr sc (ITList t) third
      i <- liftG (choose (0, m - 1))
      return (IRBuiltin BListIndex [foldr consE rest pre, intE i])
    -- A field of type @t@, read under its constructor's test.
    adtAccessors ds =
      [ (2, do (tyName, c, f, _) <- liftG (elements fs)
               e <- genExpr sc (ITADT tyName) half
               v <- fresh "d"
               dflt <- genExpr sc t half
               return (IRLetIn v e (IRIf (IRApply (IRVar ("is" ++ c)) (IRVar v)) (IRApply (IRVar f) (IRVar v)) dflt)))
      | let fs = [ x | x@(_, _, _, ft) <- adtFields ds, ft == t ], not (null fs) ]
    -- A function from @s@ to @a@: mostly a lambda (a closure over the
    -- scope), else any expression of the function type.
    funcOf s a = frequencyG
      [ (3, do v <- fresh "m"; IRLambda v <$> genExpr ((v, s) : sc) a half)
      , (1, genExpr sc (ITArrow s a) half) ]
    bin op ty = IROp op <$> genExpr sc ty half <*> genExpr sc ty half
    un op ty = IRUnaryOp op <$> genExpr sc ty (n - 1)
    specific ds = case t of
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
        , (1, do op <- liftG (elements [ROpAdd, ROpLogSumExp, ROpMax])
                 k <- liftG (choose (0, 3))
                 IRBuiltin (BReduce op 0) . (: []) <$> genExpr sc (ITTensor [EFixed k] ITFloat) (n - 1))
        , (1, IRApply (IRVar "listProd") <$> genExpr sc (ITList ITFloat) (n - 1))
        ]
      ITInt ->
        [ (2, bin OpPlus ITInt), (2, bin OpMult ITInt), (2, bin OpSub ITInt), (1, bin OpMax ITInt)
        , (1, un OpNeg ITInt), (1, un OpSign ITInt), (1, un OpAbs ITInt)
        , (2, exactDivision)
        , (1, categorical)
        , (1, do s <- genTySuchThat 1 isEquatable
                 x <- genExpr sc s half
                 xs <- genExpr sc (ITList s) half
                 return (applyAll (IRVar "indexOf") [x, xs]))
        ]
      ITBool ->
        [ (2, do s <- genTySuchThat 1 isOrderedTy
                 op <- liftG (elements [OpLessThan, OpGreaterThan])
                 bin op s)
        , (3, do s <- genTySuchThat 2 isEquatable; bin OpEq s)
        , (1, bin OpApprox ITFloat)
        , (2, bin OpAnd ITBool), (2, bin OpOr ITBool), (2, un OpNot ITBool)
        , (1, do s <- genTy 1
                 e <- frequencyG [(3, genExpr sc s (n - 1)), (1, return (IRConst VAny))]
                 return (IRUnaryOp OpIsAny e))
        , (1, do a <- genTy 1; b <- genTy 1
                 acc <- liftG (elements [AcIsLeft, AcIsRight])
                 IRDestruct acc <$> genExpr sc (ITEither a b) (n - 1))
        , (1, do s <- genTySuchThat 1 isConformable
                 rt <- frequencyG [(3, return (rTypeOf s)), (1, rTypeOf <$> genTySuchThat 1 isConformable)]
                 IRConformsTo rt <$> genExpr sc s (n - 1))
        , (1, do s <- genTySuchThat 1 (isJust . domainShape)
                 dom <- liftG (genDomain s)
                 IRIsPossible dom <$> genExpr sc s (n - 1))
        ] ++
        [ (1, do (c, _) <- liftG (elements (adtCtors ds (dataName d)))
                 IRApply (IRVar ("is" ++ c)) <$> genExpr sc (ITADT (dataName d)) (n - 1))
        | d <- ds ]
      ITList a ->
        [ (3, IRConstruct TgCons <$> sequence [genExpr sc a half, genExpr sc t half])
        , (1, guardedTail a)
        , (2, do s <- genTy 1
                 f <- funcOf s a
                 IRBuiltin BMapList . (\xs -> [f, xs]) <$> genExpr sc (ITList s) half)
        ] ++
        -- The standard library compares its list to @[]@, so its element
        -- type must have equality.
        [ (1, applyAll (IRVar "listConcat") <$> sequence [genExpr sc t half, genExpr sc t half]) | isEquatable a ]
      ITTuple a b -> [ (4, IRConstruct TgTuple <$> sequence [genExpr sc a half, genExpr sc b half]) ]
      ITEither a b ->
        [ (2, IRConstruct TgLeft . (: []) <$> genExpr sc a (n - 1))
        , (2, IRConstruct TgRight . (: []) <$> genExpr sc b (n - 1)) ]
      ITThetaTree ->
        [ (1, do i <- liftG (choose (0, 1)); IRDestruct (AcSubtree i) <$> genExpr sc ITThetaTree (n - 1)) ]
      ITTensor sh a ->
        [ (3, IRBuiltin (BTensor sh) <$> replicateM (shapeNumel sh) (genExpr sc a (n `div` (shapeNumel sh + 1))))
        , (3, do s <- genTy 1
                 f <- funcOf s a
                 IRBuiltin BMap . (\te -> [f, te]) <$> genExpr sc (ITTensor sh s) half)
        ] ++
        [ (3, do (op, operandTy) <- liftG (elements zs)
                 s <- operandTy
                 IRBuiltin (BZip op) <$> sequence [genExpr sc (ITTensor sh s) half, genExpr sc (ITTensor sh s) half])
        | let zs = zipOps a, not (null zs) ]
      ITArrow a b ->
        [ (4, do v <- fresh "f"; IRLambda v <$> genExpr ((v, a) : sc) b (n - 1)) ]
      ITADT name ->
        [ (4, do (c, fts) <- liftG (elements (adtCtors ds name))
                 applyAll (IRVar c) <$> mapM (\ft -> genExpr sc ft (n `div` (length fts + 1))) fts) ]
      _ -> []
    -- The operators 'BZip' is drawn with at element type @a@, each with its
    -- operands' element type. Not 'OpIntDiv'/'OpMod': their value
    -- precondition (an exact, nonzero divisor) is not drawable elementwise.
    zipOps a = case a of
      ITFloat -> [ (op, return ITFloat) | op <- [OpPlus, OpMult, OpSub, OpDiv, OpMax] ]
      ITInt -> [ (op, return ITInt) | op <- [OpPlus, OpMult, OpSub, OpMax] ]
      ITBool -> [ (OpAnd, return ITBool), (OpOr, return ITBool), (OpApprox, return ITFloat)
                , (OpLessThan, genTySuchThat 1 isOrderedTy), (OpGreaterThan, genTySuchThat 1 isOrderedTy)
                , (OpEq, genTySuchThat 1 isEquatable) ]
      _ -> []
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
    -- An inverse-CDF index within its contract: a uniform in [0, 1) (a
    -- constant, or a drawn float clamped into it, NaN to 0.5) and finite
    -- non-negative weights (constants, or drawn floats clamped into [0, 1e6],
    -- NaN to 0), read as a tensor or out of a cons list whose prefix holds
    -- them.
    categorical = do
      m <- liftG (choose (1, 4))
      start <- liftG (choose (0, m - 1))
      cnt <- liftG (choose (1, m - start))
      ws <- replicateM m weight
      asTensor <- liftG arbitrary
      w <- if asTensor then return (IRBuiltin (BTensor [EFixed m]) ws)
           else (\rest -> foldr consE rest ws) <$> genExpr sc (ITList ITFloat) third
      draws <- gets gsDraws
      u <- frequencyG $
        -- the shape the neural categorical sampler emits ('SPLL.AutoNeural')
        [ (3, return (IRSample IRUniform)) | draws ] ++
        [ (2, floatE <$> liftG (frequency [(3, choose (0, 0.999)), (1, elements [0, 0.5, 0.999999])]))
        , (1, do v <- fresh "u"
                 e <- genExpr sc ITFloat third
                 let x = IRVar v
                 return (IRLetIn v e (IRIf (ltE x (floatE 0)) (floatE 0) (IRIf (ltE x (floatE 1)) x (floatE 0.5))))) ]
      return (IRBuiltin (BCategoricalIndex start cnt) [u, w])
    weight = frequencyG
      [ (3, floatE <$> liftG (choose (0, 3)))
      , (1, return (floatE 0))
      , (2, do v <- fresh "w"
               e <- genExpr sc ITFloat third
               let x = IRVar v
               return (IRLetIn v e (IRIf (gtE x (floatE 0)) (IRIf (ltE x (floatE 1e6)) x (floatE 1e6)) (floatE 0)))) ]

-- | A leaf: a variable of the type in scope, or a constant (a closure for a
-- function type, a structure of leaves for a type holding one).
leaf :: Scope -> IRType -> G IRExpr
leaf sc t = do
  draws <- gets gsDraws
  let drawn = [ (4, drawG) | draws, t == ITFloat ]
  case [ v | (v, t') <- sc, t' == t ] of
    [] -> frequencyG ((2, build) : drawn)
    vs -> frequencyG ([(3, IRVar <$> liftG (elements vs)), (1, build)] ++ drawn)
  where
    build = case t of
      ITArrow a b -> do
        v <- fresh "f"
        IRLambda v <$> leaf ((v, a) : sc) b
      ITTuple a b | hasArrow t -> (\x y -> IRConstruct TgTuple [x, y]) <$> leaf sc a <*> leaf sc b
      ITEither a b | hasArrow t -> do
        l <- liftG arbitrary
        if l then IRConstruct TgLeft . (: []) <$> leaf sc a else IRConstruct TgRight . (: []) <$> leaf sc b
      ITList _ | hasArrow t -> return (IRConst (VList EmptyList))
      ITTensor sh a | hasArrow t -> IRBuiltin (BTensor sh) <$> replicateM (shapeNumel sh) (leaf sc a)
      _ -> do
        ds <- adtsG
        IRConst <$> liftG (genValue ds t)

-- | A random draw: a uniform or a standard normal.
drawG :: G IRExpr
drawG = IRSample <$> liftG (frequency [(3, return IRUniform), (2, return IRNormal)])

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
  ITADT n -> TADT n
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

-- ---------------------------------------------------------------------------
-- Function groups (M3)
--
-- A case draws zero to three helper groups before its body, each a normal
-- function @<name>_normal@ that the body and every later helper may call
-- (cross-function calls; the calls production of 'genExpr'). A helper's
-- parameters and result may be function types, so closures are passed (a
-- lambda over the caller's scope, a helper reference, a partial application)
-- and returned. A nullary helper is referenced as a value. Recursion comes in
-- three shapes, each on a measure that strictly decreases: an Int countdown
-- (bounded by 'recursionCap' at both ends, so a drawn argument cannot make
-- it deep), a list's tail, and a mutually recursive pair on an Int. A
-- recursive helper is not in its own body's scope: its only self-call is the
-- one on the decreased measure.

recursionCap :: Int
recursionCap = 6

helperScope :: [Helper] -> Scope
helperScope hs = [ (helperRef h, helperType h) | h <- hs ]

genHelpers :: G [Helper]
genHelpers = do
  k <- liftG (frequency [(4, return 0), (3, return 1), (2, return 2), (1, return 3)])
  go k []
  where
    go :: Int -> [Helper] -> G [Helper]
    go 0 acc = return acc
    go i acc = do
      shape <- liftG (frequency [(5, return HPlain), (2, return HCountdown), (2, return HListRec), (1, return HMutual)])
      new <- genHelper shape (helperScope acc)
      go (i - 1) (acc ++ new)

genHelper :: HelperShape -> Scope -> G [Helper]
genHelper shape sc0 = do
  -- Where draws are allowed (a generate case), half the helpers are generate
  -- functions, which may draw. A normal helper may not, and so may not call
  -- a generate helper either.
  draws <- gets gsDraws
  gen <- if draws then liftG arbitrary else return False
  let sc = if gen then sc0 else [ b | b@(v, _) <- sc0, not ("_gen" `isSuffixOf` v) ]
  withDraws gen (genHelperOf gen shape sc)

genHelperOf :: Bool -> HelperShape -> Scope -> G [Helper]
genHelperOf gen shape sc = case shape of
  HPlain -> do
    name <- fresh "hf"
    np <- liftG (choose (0, 2))
    ps <- replicateM np ((,) <$> fresh "hp" <*> genTy 2)
    rt <- genTy 2
    size <- liftG (choose (1, 8))
    body <- genExpr (ps ++ sc) rt size
    return [Helper name ps rt body HPlain gen]
  HCountdown -> do
    name <- fresh "hf"
    s <- genTy 1
    t <- genTy 1
    nv <- fresh "hn"
    xv <- fresh "hx"
    rv <- fresh "hr"
    body <- countdownBody sc (IRVar (name ++ helperSuffix gen)) nv xv rv s t
    return [Helper name [(nv, ITInt), (xv, s)] t body HCountdown gen]
  HListRec -> do
    name <- fresh "hf"
    a <- genTySuchThat 1 isEquatable
    t <- genTy 1
    xs <- fresh "hl"
    hd <- fresh "hh"
    rv <- fresh "hr"
    let xsV = IRVar xs
    base <- genExpr sc t 3
    step <- genExpr ((hd, a) : (rv, t) : (xs, ITList a) : sc) t 4
    let body = IRIf (IROp OpEq xsV (IRConst (VList EmptyList))) base
                 (IRLetIn hd (IRDestruct AcHead xsV)
                   (IRLetIn rv (IRApply (IRVar (name ++ helperSuffix gen)) (IRDestruct AcTail xsV)) step))
    return [Helper name [(xs, ITList a)] t body HListRec gen]
  HMutual -> do
    f <- fresh "hf"
    g <- fresh "hf"
    s <- genTy 1
    t <- genTy 1
    n1 <- fresh "hn"
    x1 <- fresh "hx"
    r1 <- fresh "hr"
    n2 <- fresh "hn"
    x2 <- fresh "hx"
    r2 <- fresh "hr"
    bf <- countdownBody sc (IRVar (g ++ helperSuffix gen)) n1 x1 r1 s t
    bg <- countdownBody sc (IRVar (f ++ helperSuffix gen)) n2 x2 r2 s t
    return [ Helper f [(n1, ITInt), (x1, s)] t bf HMutual gen
           , Helper g [(n2, ITInt), (x2, s)] t bg HMutual gen ]

-- | @if n < 1 then base else if n > recursionCap then base' else let r =
-- callee (n - 1) x' in step@.
countdownBody :: Scope -> IRExpr -> String -> String -> String -> IRType -> IRType -> G IRExpr
countdownBody sc callee nv xv rv s t = do
  let n = IRVar nv
      inner = (xv, s) : (nv, ITInt) : sc
  base <- genExpr inner t 3
  base' <- genExpr inner t 2
  x' <- genExpr inner s 2
  step <- genExpr ((rv, t) : inner) t 4
  return (IRIf (ltE n (intE 1)) base
            (IRIf (gtE n (intE recursionCap)) base'
              (IRLetIn rv (applyAll callee [IROp OpSub n (intE 1), x']) step)))

-- | The size bodies are drawn at.
caseSize :: Int
caseSize = 14

-- | A case: a value body (M1), a 'PResult' body (M2) or a generate body
-- (M4), in parts 2:2:1. All draw the case's ADTs and helpers (M3) first.
genIRCase :: Gen IRCase
genIRCase = frequency [(2, genValueCase), (2, genPResultCase), (1, genGenCase)]

-- | A value-body case: zero to three parameters, up to two top-level
-- constants, a body and four argument vectors.
genValueCase :: Gen IRCase
genValueCase = frequency [(3, return NormalBody), (1, return WriteLogitsBody)] >>= genBodyCase

-- ---------------------------------------------------------------------------
-- Generate bodies (M4)
--
-- A generate body is a value body that may draw: 'IRSample' is a float
-- production wherever the body is drawn (leaves included), so draws are
-- let-bound and read twice, sit in 'IRIf' arms, in lambdas a 'BMap' applies
-- per element, in recursive helpers and in the uniform of a categorical index.
-- Half the case's helpers are generate functions (@<name>_gen@), which may
-- draw too; a normal helper may not.
--
-- The check is by support, with a witness. Each backend's @rand()@ and
-- @randn()@ are replaced, in the driver, by reads of a fixed stream
-- ('icDraws'), and the backend reports its sample with how many draws it
-- took. The interpreter replays the same stream ('IRInterpreter.generateReplay')
-- and must answer the same sample and the same count: the backend's draws are
-- then a witness that its sample lies in the body's support (every stream
-- value lies in its primitive's support). A body that re-evaluates a let-bound
-- draw, or evaluates a draw the interpreter does not (or in another order),
-- answers a different sample or count. That is stricter than support (an
-- evaluation order that differs but samples the same distribution
-- disagrees), and it makes a generate body comparable exactly like a
-- deterministic one, known families' as-if rewrites included.

-- | How many values of each primitive a case's stream holds. A body that
-- draws more raises "draw stream exhausted" on every engine.
drawStreamLength :: Int
drawStreamLength = 64

genGenCase :: Gen IRCase
genGenCase = do
  c <- genBodyCase GenBody
  us <- vectorOf drawStreamLength (choose (0, 0.9999999))
  ns <- vectorOf drawStreamLength (frequency [(6, choose (-3, 3)), (1, choose (-8, 8))])
  return c { icDraws = (us, ns) }

genBodyCase :: BodyKind -> Gen IRCase
genBodyCase kind = do
  ds <- genADTs
  np <- choose (0, 3)
  ptys <- vectorOf np (genValueType ds 2)
  nc <- frequency [(3, return 0), (1, choose (1, 2))]
  ctys <- vectorOf nc (genValueType ds 1)
  cvals <- mapM (genValue ds) ctys
  -- A generate body's result leans to holding a float, where draws are
  -- produced.
  rt <- if kind == GenBody
          then frequency [ (2, return ITFloat), (1, ITTuple ITFloat <$> genValueType ds 1)
                         , (1, ITList <$> elements [ITFloat, ITBool]), (3, genValueType ds 2) ]
          else genValueType ds 2
  size <- choose (2, caseSize)
  let params = zip [ "a" ++ show i | i <- [0 :: Int ..] ] ptys
      consts = zip [ "k" ++ show i | i <- [0 :: Int ..] ] cvals
      sc = params ++ zip (map fst consts) ctys
  (helpers, body) <- runG ds $ withDraws (kind == GenBody) $ do
    hs <- genHelpers
    b <- genExpr (sc ++ helperScope hs) rt size
    return (hs, b)
  args <- replicateM 4 (mapM (genValue ds) ptys)
  return (IRCase kind Nothing params rt consts body args helpers ds ([], []))

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
      , (1, do s <- genTy 1
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
                           , (2, do s <- genTy 1; genExpr sc s 1) ]
    -- An enumerated sum's body sees the enumerated variable, over a small
    -- finite domain (no Float slot: a continuous domain has no values).
    enumerated k = do
      s <- genTySuchThat 1 (\ty -> isJust (domainShape ty) && finiteTy ty)
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
  ds <- genADTs
  ptys <- (ITFloat :) <$> vectorOf np (genValueType ds 1)
  nc <- frequency [(3, return 0), (1, choose (1, 2))]
  ctys <- vectorOf nc (genValueType ds 1)
  cvals <- mapM (genValue ds) ctys
  size <- choose (1, 7)
  let params = zip [ "a" ++ show i | i <- [0 :: Int ..] ] ptys
      consts = zip [ "k" ++ show i | i <- [0 :: Int ..] ] cvals
      sc = params ++ zip (map fst consts) ctys
  (helpers, plan) <- runG ds $ do
    hs <- genHelpers
    pl <- genPlan c (sc ++ helperScope hs) size
    return (hs, pl)
  args <- replicateM 4 (mapM (genValue ds) ptys)
  let unstripped = IRCase kind (Just (c, stripped)) params (presultType False) consts (buildPlan c plan) args helpers ds ([], [])
  return $ if stripped then stripCase unstripped else unstripped

-- | The case with its body's branch count stripped, by the compiler's own
-- pass.
stripCase :: IRCase -> IRCase
stripCase c = case stripBranchCount (irCaseEnv c) of
  IREnv gs _ _ | [g] <- [ g' | g' <- gs, groupName g' == "main" ]
               , Just (f, _) <- (if icKind c == ProbBody then probFun g else integFun g) ->
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
  ++ [ c' | i <- [0 .. length (icHelpers c) - 1]
          , let c' = c { icHelpers = [ h | (j, h) <- zip [0 :: Int ..] (icHelpers c), j /= i ] }
          , either (const False) (const True) (irCaseWellTyped c') ]
  ++ [ c' | b <- shrinkExpr (icBody c), let c' = c { icBody = b }, either (const False) (const True) (irCaseWellTyped c') ]
  ++ [ c' | (i, h) <- zip [0 :: Int ..] (icHelpers c), b <- shrinkExpr (hBody h)
          , let c' = c { icHelpers = [ if j == i then h { hBody = b } else h' | (j, h') <- zip [0 ..] (icHelpers c) ] }
          , either (const False) (const True) (irCaseWellTyped c') ]

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
raiseMessages = ["head of an empty list", "tail of an empty list", "fromLeft of a Right", "fromRight of a Left", "draw stream exhausted"]

interpreterMicros :: Int
interpreterMicros = 2 * 1000 * 1000

interpretIRCase :: IRCase -> [IRValue] -> IO InterpOutcome
interpretIRCase c args = do
  r <- try (timeout interpreterMicros (evaluate (forced (run (irCaseEnv c) (map IRConst args) (irCaseFunction c)))))
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
    -- A generate body answers its sample with how many draws it took, as
    -- the drivers report a backend's ('VTuple' of the count and the sample).
    run env as f
      | icKind c == GenBody = (\(v, k) -> VTuple (VInt k) v) <$> generateReplay [] [] env (icDraws c) as f
      | otherwise = generateDet [] [] env as f

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
repro params rt body args = IRCase NormalBody Nothing params rt [] body [args] [] [] ([], [])

-- | A one-query probability case for a batched pin: @main a0@ answers the
-- given probability, dimension 0, possible.
batchedRepro :: IRExpr -> IRValue -> IRCase
batchedRepro p a0 = (repro [("a0", ITFloat)] (presultType True)
                       (IRConstruct TgTuple [p, IRConstruct TgTuple [IRConst (VFloat 0), IRConst (VBool False)]]) [a0])
                    { icKind = ProbBody, icShape = Just (SRLinear, True) }

-- | A one-query generate case over no arguments, with a short stream, for a
-- pin.
genRepro :: [(String, IRType)] -> IRType -> IRExpr -> IRCase
genRepro params rt body = (repro params rt body []) { icKind = GenBody, icDraws = ([0.25, 0.5, 0.75], [0.5, -1.5, 2.5]) }

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
valueAgrees = valueAgreesWith floatAgrees

-- | 'valueAgrees' with the given float comparison.
valueAgreesWith :: (Double -> Double -> Bool) -> IRValue -> [String] -> Either String Bool
valueAgreesWith floatEq v0 toks0 = case go v0 toks0 of
  Right (lenient, []) -> Right lenient
  Right (_, rest) -> Left ("tokens left over: " ++ unwords rest)
  Left why -> Left why
  where
    go v toks = case (v, toks) of
      (VFloat x, ('f' : s) : rest) -> case readNum s of
        Just y | floatEq x y -> Right (False, rest)
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
      -- A rank-1 tensor is a Python list or a Julia Vector.
      (VTensor _ xs, ('v' : k) : rest) | readMaybe k == Just (length xs) -> many xs rest
      (VADT ctor fs, ('a' : name) : k : rest) | name == ctor, readMaybe k == Just (length fs) -> many fs rest
      _ -> Left (show v ++ " against " ++ unwords (take 6 toks))
    both a b toks = do
      (l1, r1) <- go a toks
      (l2, r2) <- go b r1
      return (l1 || l2, r2)
    many [] toks = Right (False, toks)
    many (x : xs) toks = do
      (l1, r1) <- go x toks
      (l2, r2) <- many xs r1
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
  -- The same ticket, where Python's int sign meets an operator the
  -- interpreter takes floats only for (found in M4): the rewrite above then
  -- stops the interpreter, so the family is recognised by the construct and
  -- a differing value instead, as Python's uniform functions are below.
  , KnownFamily "opsign-nan-negative-zero-and-int-results-differ-across-engines" ["python"]
      (ByAnswer (\c o a -> isValue o && isSampled a && not (null [ () | IRUnaryOp OpSign _ <- caseUniverse c ])))
      (repro [("a0", ITFloat)] ITBool
         (IRLetIn "s" (IRUnaryOp OpSign (IRVar "a0"))
            (IRConformsTo TFloat (IRIf (IROp OpApprox (IRVar "s") (IRConst (VFloat 1))) (IRVar "s") (IRConst (VFloat 0)))))
         [VFloat 2])
  , KnownFamily "python-float-division-by-zero-raises" ["python"]
      (ByAnswer (\_ o a -> isValue o && raisedWith "ZeroDivisionError" a))
      (repro [("a0", ITFloat)] ITFloat (IROp OpDiv (IRConst (VFloat 1)) (IRVar "a0")) [VFloat 0])
  , KnownFamily "python-normal-density-overflows-past-1e154" ["python"]
      (ByAnswer (\c o a -> isValue o && raisedWith "OverflowError" a && any hasNormalDensity (caseBodies c)))
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
                           && not (null [ () | x <- caseUniverse c, linearUniform x ])))
      (repro [("a0", ITFloat)] ITBool (IRConformsTo TFloat (IRCumulative IRUniform Linear (IRVar "a0"))) [VFloat 2])
  , KnownFamily "python-empty-list-head-and-tail-answer-none" ["python"]
      (ByAnswer (\_ o a -> case (o, a) of
                  (InterpRaise m, Sampled _) -> m `elem` ["head of an empty list", "tail of an empty list"]
                  _ -> False))
      (repro [] ITBool (IRUnaryOp OpIsAny (IRDestruct AcHead (IRConst (VList (EmptyList :: GenericList IRValue))))) [])
  , KnownFamily "python-ispossible-on-a-tuple-domain-answers-none" ["python"]
      (ByAnswer (\c _ _ -> any tupleDomain [ d | IRIsPossible d _ <- caseUniverse c ]))
      (repro [] ITBool (IRIsPossible (MultiTuple MultiContinuous MultiContinuous) (IRConst (VTuple (VFloat 1) (VFloat 2)))) [])
  , KnownFamily "ir-conformsto-lowering-gaps-in-text-backends" ["python", "julia"]
      (AsIf (const (irMap conformsUnitUnchecked)))
      (repro [] ITBool (IRConformsTo TUnit (IRConst (VBool True))) [])
  , KnownFamily "ir-conformsto-lowering-gaps-in-text-backends" ["python", "julia"]
      (AsIf (const (irMap conformsUnitUnchecked)))
      ((repro [] ITBool (IRConformsTo (TADT "Qt") (IRConst (VBool True))) []) { icADTs = [ADTDecl "Qt" [("Qa", [])] Nothing] })
  , KnownFamily "ir-conformsto-lowering-gaps-in-text-backends" ["python", "julia"]
      (ByAnswer (\c _ a -> raisedWith "module did not load" a
                           && not (null [ () | IRConformsTo _ x <- caseUniverse c, not (isVar x) ])))
      -- Python cannot parse the walrus a let lowers to inside the
      -- comprehension a list check iterates; Julia cannot parse a field
      -- access on a negative literal (@-1.0.t1@).
      (repro [] (ITTuple ITBool ITBool)
         (IRConstruct TgTuple
            [ IRConformsTo (ListOf TFloat) (IRLetIn "l0" (IRConst (VInt 1)) (IRConst (VList (ListCont (VFloat 1) EmptyList))))
            , IRConformsTo (Tuple TFloat TFloat) (IRConst (VFloat (-1))) ])
         [])
  -- M3 (builtins, tensors and function groups).
  , KnownFamily "julia-listprod-of-an-empty-list-raises" ["julia"]
      (ByAnswer (\_ o a -> isValue o && raisedWith "one(::Type{Any})" a))
      (repro [] ITFloat (IRApply (IRVar "listProd") (IRConst (VList EmptyList))) [])
  -- The same ticket (found in M4): Julia's @prod@ multiplies left to right,
  -- the standard library right to left, which differs where an underflow
  -- meets an infinity.
  , KnownFamily "julia-listprod-of-an-empty-list-raises" ["julia"]
      (ByAnswer (\c o a -> isValue o && isSampled a && not (null [ () | IRVar "listProd" <- caseUniverse c ])))
      (repro [] ITFloat (IRApply (IRVar "listProd")
         (IRConst (VList (ListCont (VFloat (-1 / 0)) (ListCont (VFloat 1e300) (ListCont (VFloat (-0.29)) (ListCont (VFloat 5e-324) EmptyList))))))) [])
  -- The same ticket, Python's side (found in M4): its empty product is the
  -- int 1, which only a type-tag check tells from 1.0. Julia raises as above.
  , KnownFamily "julia-listprod-of-an-empty-list-raises" ["python", "julia"]
      (ByAnswer (\c o a -> isValue o && isSampled a
                           && not (null [ () | IRConformsTo _ x <- caseUniverse c, IRVar "listProd" <- universe x ])))
      (repro [] ITBool (IRConformsTo TFloat (IRApply (IRVar "listProd") (IRConst (VList EmptyList)))) [])
  -- After the ConformsTo entry above, whose repro fails to parse the same way.
  , KnownFamily "python-let-in-a-comprehension-iterable-fails-to-parse" ["python"]
      (ByAnswer (\_ _ a -> raisedWith "assignment expression cannot be used in a comprehension iterable expression" a))
      (repro [] (ITTensor [EFixed 1] ITFloat)
         (IRBuiltin BMap [IRLambda "m" (IRVar "m"), IRLetIn "l" (IRConst (VFloat 1)) (IRBuiltin (BTensor [EFixed 1]) [IRVar "l"])]) [])
  , KnownFamily "bzip-max-and-approx-have-no-text-lowering" ["python", "julia"]
      (ByAnswer (\_ _ a -> raisedWith "codegen threw" a && (raisedWith "OpMax" a || raisedWith "OpApprox" a)))
      (repro [] (ITTensor [EFixed 1] ITFloat)
         (IRBuiltin (BZip OpMax) [IRBuiltin (BTensor [EFixed 1]) [IRConst (VFloat 1)], IRBuiltin (BTensor [EFixed 1]) [IRConst (VFloat 2)]]) [])
  , KnownFamily "interpreter-bmap-evaluates-its-function-operand-per-element" ["python", "julia"]
      (AsIf (const (irMap functionOperandFirst)))
      (repro [] (ITTensor [EFixed 0] ITFloat)
         (IRBuiltin BMap [IRError "the function operand raises", IRBuiltin (BTensor [EFixed 0]) []]) [])
  -- Both text backends render nested lambdas as one lambda of several
  -- parameters and an application chain as one call, so only an application
  -- saturating its function's syntactic lambdas exactly works: a partial
  -- application, or a call through a closure a function returns, raises.
  , KnownFamily "text-backends-uncurry-lambdas-and-application-chains" ["python", "julia"]
      (ByAnswer (\_ o a -> isValue o && (  (raisedWith "TypeError" a && raisedWith "positional argument" a)
                                        || (raisedWith "MethodError: no method matching" a
                                            && (raisedWith "var\"#" a || raisedWith "_normal(" a || raisedWith "_gen(" a)))))
      (repro [] ITFloat
         (IRLetIn "g" (IRApply (IRLambda "x" (IRLambda "y" (IROp OpPlus (IRVar "x") (IRVar "y")))) (IRConst (VFloat 1)))
            (IRApply (IRVar "g") (IRConst (VFloat 2)))) [])
  -- M4 (generate bodies, judged by replaying the backend's draws).
  --
  -- Both text backends lower a type-tag check by repeating its operand
  -- (@isAny(x) or isinstance(x, float)@), so an operand that draws draws
  -- again. Recognised by the construct: a generate body whose check has an
  -- operand with an effect ('isPure'), answering a sample.
  , KnownFamily "text-backends-conformsto-reevaluates-its-operand" ["python", "julia"]
      (ByAnswer (\c o a -> icKind c == GenBody && isValue o && isSampled a
                           && not (null [ () | IRConformsTo _ x <- caseUniverse c, not (isPure x) ])))
      (genRepro [] ITBool (IRConformsTo TFloat (IRSample IRUniform)))
  -- The interpreter evaluates a cons's tail before its head; both text
  -- backends evaluate the head first. Only the order of the draws differs.
  , KnownFamily "interpreter-cons-evaluates-its-tail-before-its-head" ["python", "julia"]
      (AsIf (const (irMap consHeadFirst)))
      (genRepro [] (ITList ITFloat)
         (IRConstruct TgCons [IRSample IRUniform, IRConstruct TgCons [IRSample IRUniform, IRConst (VList EmptyList)]]))
  -- Python's codegen floats a let-binding, or an 'IRIf' it spills, nested in
  -- an expression out to a statement before it, so its draws come before the
  -- draws of whatever precedes it in the expression. Only the order of the
  -- draws differs, but that can steer a branch elsewhere. Recognised by the
  -- construct alone (a reorder can shift every later draw, so any answer
  -- can follow): a generate body with a drawing let or if under another
  -- node.
  , KnownFamily "python-let-hoisting-reorders-draws" ["python"]
      (ByAnswer (\c _ _ -> icKind c == GenBody
                           && not (null [ () | x <- caseUniverse c, d <- hoistedEffects x, not (isPure d) ])))
      (genRepro [] ITFloat (IROp OpSub (IRSample IRUniform) (IRLetIn "l" (IRSample IRUniform) (IRVar "l"))))
  -- Python's empty sum is the int 0, which has no negative zero: the IR's
  -- @-(sum [])@ is -0.0 (found in M4). Recognised by the construct (a case
  -- summing a tensor of static length 0) and a differing value.
  , KnownFamily "python-empty-sum-answers-an-int" ["python"]
      (ByAnswer (\c o a -> isValue o && isSampled a
                           && not (null [ () | IRBuiltin (BReduce ROpAdd 0) [IRBuiltin (BTensor [EFixed 0]) []] <- caseUniverse c ])))
      (repro [] ITFloat (IROp OpDiv (IRUnaryOp OpNeg (IRBuiltin (BReduce ROpAdd 0) [IRBuiltin (BTensor [EFixed 0]) []])) (IRConst (VFloat 2))) [])
  -- M4, the batched arm (PResult bodies through the select pass and the
  -- batched backend).
  --
  -- The batched backend lowers a list index as a tensor slot read
  -- (@xs[..., k]@), which a cons list does not take.
  , KnownFamily "batched-blistindex-reads-a-cons-list-as-a-tensor" ["batched"]
      (ByAnswer (\c _ a -> raisedWith "not supported between instances of 'tuple' and 'int'" a
                         && not (null [ () | IRBuiltin BListIndex _ <- caseUniverse c ])))
      (batchedRepro (IRBuiltin BListIndex [IRConstruct TgCons [IRConst (VFloat 0.5), IRConst (VList EmptyList)], IRConst (VInt 0)]) (VFloat 1))
  -- The batched runtime defines none of the list functions of the standard
  -- library the backend calls.
  , KnownFamily "batched-runtime-lacks-the-list-standard-library" ["batched"]
      (ByAnswer (\_ _ a -> any (\f -> raisedWith ("NameError: name '" ++ f ++ "' is not defined") a) ["listProd", "indexOf", "listConcat"]))
      (batchedRepro (IRApply (IRVar "listProd") (IRConstruct TgCons [IRConst (VFloat 0.5), IRConst (VList EmptyList)])) (VFloat 1))
  -- The batched @isclose@ scales its tolerance by the operands' magnitude, so
  -- an infinity is close to every number.
  , KnownFamily "batched-isclose-holds-at-an-infinity" ["batched"]
      (AsIf (const (irMap batchedApprox)))
      (batchedRepro (IRIf (IROp OpApprox (IRVar "a0") (IRConst (VFloat 1))) (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat (-1 / 0)))
  -- The batched runtime's tuple has no order.
  , KnownFamily "batched-tuple-comparison-has-no-order" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "not supported between instances of 'T' and 'T'" a))
      (batchedRepro (IRIf (IROp OpLessThan (IRConst (VTuple (VFloat 1) (VInt 1))) (IRConst (VTuple (VFloat 2) (VInt 0))))
                          (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat 1))
  -- The batched runtime's densities take a tensor: of a plain Python number,
  -- the uniform one is a bool (which has no @.to@) and the normal one calls
  -- @torch.exp@ on a float.
  , KnownFamily "batched-math-on-a-constant-operand-fails" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "'bool' object has no attribute 'to'" a || raisedWith "must be Tensor, not float" a))
      (batchedRepro (IRDensity IRUniform Linear (IRConst (VFloat 0.5))) (VFloat 1))
  -- The batched backend divides by @safe_div@, a NaN at a zero divisor where
  -- the IR's division answers an infinity (Python raises there,
  -- 'python-float-division-by-zero-raises'), and takes logs by @safe_log@,
  -- minus infinity at a negative or NaN operand where the IR's log is a NaN.
  , KnownFamily "batched-safe-div-and-safe-log-differ-off-domain" ["batched"]
      (AsIf (const (irMap (batchedSign . batchedLog . batchedDivision))))
      (batchedRepro (IROp OpDiv (IRConst (VFloat 1)) (IRVar "a0")) (VFloat 0))
  , KnownFamily "batched-safe-div-and-safe-log-differ-off-domain" ["batched"]
      (AsIf (const (irMap (batchedSign . batchedLog . batchedDivision))))
      (batchedRepro (IRUnaryOp OpLog (IRVar "a0")) (VFloat (-1)))
  -- The NaN of a zero divisor shows through a sign: torch's sign of a NaN is
  -- 0 (the interpreter refuses one, 'knownRefusals'), so the rewrite gives
  -- the sign that too.
  , KnownFamily "batched-safe-div-and-safe-log-differ-off-domain" ["batched"]
      (AsIf (const (irMap (batchedSign . batchedLog . batchedDivision))))
      (batchedRepro (IRIf (IROp OpEq (IRUnaryOp OpSign (IROp OpDiv (IRConst (VFloat 1)) (IRVar "a0"))) (IRConst (VFloat 0)))
                          (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat 0))
  -- torch's logsumexp is +inf when a term is +inf, where the interpreter's
  -- pairwise fold makes it NaN next to a finite term.
  , KnownFamily "logsumexp-reduction-nan-and-infinity-differ-across-engines" ["batched"]
      (AsIf (const (irMap batchedLogSumExp)))
      (batchedRepro (IRBuiltin (BReduce ROpLogSumExp 0) [IRBuiltin (BTensor [EFixed 2]) [IRVar "a0", IRDensity IRNormal Linear (IRVar "a0")]]) (VFloat (1 / 0)))
  -- A rank-1 tensor's elements are read as floats: a tensor of booleans is
  -- built as a float tensor (so an element read out of it is no condition
  -- for @torch.where@), and one of tuples fails.
  , KnownFamily "batched-tensor-elements-are-read-as-floats" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "where expected condition to be a boolean tensor" a
                         || raisedWith "float() argument must be a string or a real number, not '" a))
      (batchedRepro (IRIf (IRBuiltin (BIndex 0) [IRBuiltin (BTensor [EFixed 1]) [IRConst (VBool False)], IRConst (VInt 0)])
                          (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat 1))
  , KnownFamily "batched-tensor-elements-are-read-as-floats" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "where expected condition to be a boolean tensor" a
                         || raisedWith "float() argument must be a string or a real number, not '" a))
      (batchedRepro (IRDestruct AcFst (IRBuiltin (BIndex 0) [IRBuiltin (BTensor [EFixed 1]) [IRConst (VTuple (VFloat 0.25) (VBool True))], IRConst (VInt 0)])) (VFloat 1))
  -- The batched sum of one element is that element, where the IR's sum
  -- adds it to 0.0, which turns a negative zero into 0.0. Recognised by the
  -- answer agreeing once zeros are compared without their sign.
  , KnownFamily "batched-sum-of-one-element-keeps-a-negative-zero" ["batched"]
      (ByAnswer (\_ o a -> case (o, a) of
                  (Interpreted v, Sampled toks) -> either (const False) (const True) (valueAgreesWith probAgrees v toks)
                  _ -> False))
      (batchedRepro (IRBuiltin (BReduce ROpAdd 0) [IRBuiltin (BTensor [EFixed 1]) [IRConst (VFloat (-0.0))]]) (VFloat 1))
  -- The batched type-tag check of a number literal renders a method call on
  -- it (@0.is_floating_point()@), which Python cannot parse.
  , KnownFamily "batched-conformsto-of-a-literal-fails-to-parse" ["batched"]
      (ByAnswer (\c _ a -> raisedWith "module did not load" a && raisedWith "SyntaxError" a
                         && not (null [ () | IRConformsTo _ (IRConst _) <- caseUniverse c ])))
      (batchedRepro (IRIf (IRConformsTo TFloat (IRConst (VInt 0))) (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat 1))
  -- A reduction stacks its elements, which fails when a constant (a 0-d
  -- tensor) sits next to a batched ([B]) one.
  , KnownFamily "batched-reduction-over-constant-and-batched-elements-fails" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "stack expects each tensor to be equal size" a))
      (batchedRepro (IRBuiltin (BReduce ROpAdd 0) [IRBuiltin (BTensor [EFixed 2]) [IRUnaryOp OpLog (IRConst (VFloat 0.25)), IRVar "a0"]]) (VFloat 0.5))
  -- A select over two tuples is one torch.where over two T's.
  , KnownFamily "batched-guarded-select-over-tuple-result" ["batched"]
      (ByAnswer (\_ _ a -> raisedWith "got (Tensor, T, T)" a))
      (batchedRepro (IRDestruct AcSnd (IRSelect (IROp OpLessThan (IRVar "a0") (IRConst (VFloat 0.5)))
                                         (IRConst (VTuple (VFloat 0.1) (VFloat 0.2))) (IRConst (VTuple (VFloat 0.3) (VFloat 0.4))))) (VFloat 1))
  -- The batched categorical index reads its weights as a tensor, so a list
  -- of batched weights is indexed by a tuple.
  , KnownFamily "batched-categorical-index-over-batched-weights-fails" ["batched"]
      (ByAnswer (\c _ a -> (raisedWith "list indices must be integers or slices, not tuple" a
                            || raisedWith "not supported between instances of 'tuple' and 'int'" a)
                         && not (null [ () | IRBuiltin (BCategoricalIndex _ _) _ <- caseUniverse c ])))
      (batchedRepro (IRIf (IROp OpEq (IRBuiltin (BCategoricalIndex 0 2) [IRConst (VFloat 0.5), IRBuiltin (BTensor [EFixed 2]) [IRVar "a0", IRConst (VFloat 1)]])
                                     (IRConst (VInt 0)))
                          (IRConst (VFloat 0.25)) (IRConst (VFloat 0.75))) (VFloat 1))
  -- The batched backend evaluates both arms of a conditional it lowers to a
  -- @torch.where@, so a partial destructor in the arm not taken raises.
  , KnownFamily "batched-conditional-evaluates-a-partial-arm" ["batched"]
      (ByAnswer (\c _ a -> any (`raisedWith` a) ["IndexError", "fromLeft", "fromRight", "Item is not a Left", "Item is not a Right"]
                         && not (null [ () | x <- caseUniverse c, arms <- conditionalArms x, any partialExpr arms ])))
      (batchedRepro (IRIf (IROp OpLessThan (IRVar "a0") (IRConst (VFloat 2))) (IRConst (VFloat 0.5))
                          (IRUnaryOp OpAbs (IRLetIn "l" (IRDestruct AcHead (IRConst (VList EmptyList))) (IRVar "a0")))) (VFloat 1))
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
    -- The draw counts agree (the first token after the tuple's).
    -- What Python floats out of an expression to statements before it: a
    -- let-spine or a conditional under a node that is not itself a statement
    -- (a let or an if).
    hoistedEffects x
      | isStatement x = []
      | otherwise = [ y | y <- getIRSubExprs x, isStatement y ]
    isStatement y = case y of
      IRLetIn{} -> True
      IRIf{} -> True
      _ -> False
    conditionalArms x = case x of
      IRIf _ a b -> [[a, b]]
      IRSelect _ a b -> [[a, b]]
      _ -> []
    isSampled (Sampled _) = True
    isSampled _ = False
    linearUniform x = case x of
      IRDensity IRUniform Linear _ -> True
      IRCumulative IRUniform _ _ -> True
      _ -> False

-- | Every subexpression, the expression itself included.
universe :: IRExpr -> [IRExpr]
universe e = e : concatMap universe (getIRSubExprs e)

-- | Every subexpression of every body of the case.
caseUniverse :: IRCase -> [IRExpr]
caseUniverse = concatMap universe . caseBodies

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
        in maybe (unknownLength t') (fold t') (staticLength env t')
      _ -> irDescend (go env) e
    bind v = maybe (M.delete v) (M.insert v)
    -- Where the length is not static, the NaN orders are told apart at run
    -- time instead of by a fold (signed zeros are not): Julia's NaN wins
    -- anywhere; Python's raises on an empty tensor, wins only in front, and
    -- is skipped elsewhere.
    unknownLength t =
      IRLetIn "rmx_t" t $
        if backend == "python"
          then IRIf (IROp OpEq (IRBuiltin (BReduce ROpAdd 0) [IRBuiltin BMap [IRLambda "rmx_e" (IRConst (VFloat 1)), IRVar "rmx_t"]]) (IRConst (VFloat 0)))
                    (IRError "max() arg is an empty sequence")
                    (IRIf (isNaNE (IRBuiltin (BIndex 0) [IRVar "rmx_t", IRConst (VInt 0)]))
                          (IRConst (VFloat (0 / 0)))
                          (IRBuiltin (BReduce ROpMax 0) [IRBuiltin BMap [IRLambda "rmx_e" (IRIf (isNaNE (IRVar "rmx_e")) (IRConst (VFloat (-1 / 0))) (IRVar "rmx_e")), IRVar "rmx_t"]]))
          else IRIf (countWhere isNaNE (IRVar "rmx_t")) (IRConst (VFloat (0 / 0))) (IRBuiltin (BReduce ROpMax 0) [IRVar "rmx_t"])
    staticLength env x = case x of
      IRBuiltin (BTensor [EFixed n]) _ -> Just n
      IRConst (VTensor [EFixed n] _) -> Just n
      IRBuiltin BMap [_, t] -> staticLength env t
      IRBuiltin (BZip _) [t, _] -> staticLength env t
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

-- | 'BMap' and 'BMapList' as both text backends evaluate them: the function
-- operand once, before the collection. The interpreter evaluates it per
-- element, after the collection (so not at all over an empty one).
functionOperandFirst :: IRExpr -> IRExpr
functionOperandFirst e = case e of
  IRBuiltin b [f, xs] | b == BMap || b == BMapList, not (isLambda' f) ->
    IRLetIn "bm_f" f (IRBuiltin b [IRVar "bm_f", xs])
  _ -> e
  where
    isLambda' (IRLambda _ _) = True
    isLambda' _ = False

-- | 'OpApprox' as the batched backend's @isclose@ answers it: also true when
-- either operand is infinite and neither is a NaN.
batchedApprox :: IRExpr -> IRExpr
batchedApprox e = case e of
  IROp OpApprox a b ->
    IRLetIn "ap_a" a (IRLetIn "ap_b" b
      (IROp OpOr (IROp OpApprox x y)
         (IROp OpAnd (IROp OpOr (isInf x) (isInf y)) (IROp OpAnd (IROp OpEq x x) (IROp OpEq y y)))))
  _ -> e
  where
    x = IRVar "ap_a"
    y = IRVar "ap_b"
    isInf v = IROp OpOr (IROp OpEq v (floatE (1 / 0))) (IROp OpEq v (floatE (-1 / 0)))

-- | Whether an expression holds a partial destructor or index: one that
-- raises outside its domain.
partialExpr :: IRExpr -> Bool
partialExpr x = not (null [ () | y <- universe x, isPartial y ])
  where
    isPartial y = case y of
      IRDestruct ac _ -> ac `elem` [AcHead, AcTail, AcFromLeft, AcFromRight]
      IRBuiltin (BIndex _) _ -> True
      IRBuiltin BListIndex _ -> True
      _ -> False

-- | 'OpDiv' as the batched backend's @safe_div@ answers it: a NaN at a zero
-- divisor.
batchedDivision :: IRExpr -> IRExpr
batchedDivision e = case e of
  IROp OpDiv a b ->
    IRLetIn "dv_a" a (IRLetIn "dv_b" b
      (IRIf (IROp OpEq (IRVar "dv_b") (floatE 0)) (floatE (0 / 0)) (IROp OpDiv (IRVar "dv_a") (IRVar "dv_b"))))
  _ -> e

-- | 'OpSign' as torch answers it at a NaN: 0.
batchedSign :: IRExpr -> IRExpr
batchedSign e = case e of
  IRUnaryOp OpSign a -> IRLetIn "bs_a" a (IRIf (isNaNE (IRVar "bs_a")) (floatE 0) (IRUnaryOp OpSign (IRVar "bs_a")))
  _ -> e

-- | Log-sum-exp as torch reduces it: +inf when a term is +inf and none is a
-- NaN.
batchedLogSumExp :: IRExpr -> IRExpr
batchedLogSumExp e = case e of
  IRBuiltin (BReduce ROpLogSumExp 0) [t] ->
    IRLetIn "blse_t" t $
      IRIf (IROp OpAnd (countWhere (\x -> IROp OpEq x (floatE (1 / 0))) (IRVar "blse_t"))
                       (IRUnaryOp OpNot (countWhere isNaNE (IRVar "blse_t"))))
           (floatE (1 / 0)) (IRBuiltin (BReduce ROpLogSumExp 0) [IRVar "blse_t"])
  _ -> e

-- | 'OpLog' as the batched backend's @safe_log@ answers it: minus infinity
-- at a non-positive or NaN operand.
batchedLog :: IRExpr -> IRExpr
batchedLog e = case e of
  IRUnaryOp OpLog a ->
    IRLetIn "lg_a" a (IRIf (IROp OpGreaterThan (IRVar "lg_a") (floatE 0)) (IRUnaryOp OpLog (IRVar "lg_a")) (floatE (-1 / 0)))
  _ -> e

-- | A cons as both text backends evaluate it: the head first, then the tail.
-- The interpreter evaluates the tail first.
consHeadFirst :: IRExpr -> IRExpr
consHeadFirst e = case e of
  IRConstruct TgCons [hd, tl] | not (isPure hd) -> IRLetIn "cons_hd" hd (IRConstruct TgCons [IRVar "cons_hd", tl])
  _ -> e

-- | 'IRConformsTo' as both text backends lower it: a unit, theta-tree or
-- ADT slot is not checked (any value conforms), where the interpreter checks
-- it.
conformsUnitUnchecked :: IRExpr -> IRExpr
conformsUnitUnchecked e = case e of
  IRConformsTo t a -> IRConformsTo (loosen t) a
  _ -> e
  where
    loosen t = case t of
      TUnit -> TVarR (TV "unchecked")
      TThetaTree -> TVarR (TV "unchecked")
      TADT _ -> TVarR (TV "unchecked")
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
        IRIf (countWhere (\x -> IROp OpEq x posInf) (IRVar "lse_t")) (IRConst (VFloat (0 / 0)))
             -- @m + log(...)@ is never a negative zero; the interpreter's
             -- fold answers a lone -0 term as itself.
             (IROp OpPlus (IRVar "lse_r") (IRConst (VFloat 0)))
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
        o <- interpretIRCase (onBodies rewrite c) (idArgs d)
        return $ case o of
          InterpRefusal _ -> False
          _ -> either (const False) (const True) (judgeOn (idBackend d) o (idAnswer d))

-- | 'judge', for the given backend: on the batched arm, a NaN result raises
-- by design (every return goes through @check_result@), so that raise agrees
-- with an interpreter answer holding a NaN.
judgeOn :: String -> InterpOutcome -> Answer -> Either String Bool
judgeOn backend o a = case (o, a) of
  (Interpreted v, Raised m) | backend == "batched", "result is NaN" `isInfixOf` m, valueHasNaN v -> Right False
  _ -> judge o a

valueHasNaN :: IRValue -> Bool
valueHasNaN v = case v of
  VFloat x -> isNaN x
  VTuple a b -> valueHasNaN a || valueHasNaN b
  _ -> False

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
                       Right lenient -> (outcomeLabel c o ++ (if lenient then " (int at a float slot)" else ""), Nothing)
                       Left why -> ("disagreement", Just (IRDisagreement backend c args o a why (either id id src)))
               ]
  return (map fst judged, [ d | (_, Just d) <- judged ])
  where
    outcomeLabel c o = case o of
      Interpreted (VTuple (VInt k) _) | icKind c == GenBody -> "agrees: generate sample, " ++ drawBucket k
      InterpRaise "draw stream exhausted" -> "agrees: both exhaust the draw stream"
      Interpreted _ -> "agrees: value"
      InterpRaise _ -> "agrees: both raise"
      InterpRefusal _ -> "interpreter refused (not compared)"
    drawBucket k
      | k == 0 = "no draw"
      | k == 1 = "1 draw"
      | k <= 4 = "2-4 draws"
      | otherwise = "5+ draws"

-- | The text backends emit a module per case; 'irCaseEnv' has no networks.
emitPython :: Int -> IRCase -> IO (Either String String)
emitPython _ c = fmap (fmap stubTorch) (forcedSource (return (Py.generateFunctions True (irCaseEnv c))))
  where stubTorch = unpack . replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n") . pack

methodOf :: BodyKind -> String
methodOf NormalBody = "normal_params"
methodOf WriteLogitsBody = "writeLogits"
methodOf ProbBody = "forward"
methodOf IntegBody = "integrate"
methodOf GenBody = "generate"

-- | A stream as a list literal both Python and Julia read.
streamLiteral :: [Double] -> String
streamLiteral xs = "[" ++ intercalate ", " (map show xs) ++ "]"

-- | How the Python driver prefixes a generate body's sample: with the draw
-- count, so the tokens read as the interpreter's @(count, sample)@ tuple.
pyCountPrefix :: IRCase -> String
pyCountPrefix c = if icKind c == GenBody then "'t i' + str(_D['k']) + ' ' + " else ""

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
  -- A generate body's draws come from the case's stream ('icDraws').
  , "_D = {'u': [], 'n': [], 'iu': 0, 'in': 0, 'k': 0}"
  , "def _draw(which):"
  , "    i = 'i' + which"
  , "    if _D[i] >= len(_D[which]): raise Exception('draw stream exhausted')"
  , "    x = _D[which][_D[i]]; _D[i] += 1; _D['k'] += 1"
  , "    return x"
  , "def _rand(): return _draw('u')"
  , "def _randn(): return _draw('n')"
  ] ++ pythonSerializer ++ concatMap entry entries
  where
    entry (i, path, c) =
      [ "_ns = {}"
      , "try:"
      , "    exec(compile(open(" ++ show path ++ ").read(), " ++ show path ++ ", 'exec'), _ns)"
      , "    _ns['rand'] = _rand; _ns['randn'] = _randn"
      , "    _D['u'] = " ++ streamLiteral (fst (icDraws c)) ++ "; _D['n'] = " ++ streamLiteral (snd (icDraws c))
      , "    _loaded = True"
      , "except BaseException as _e:"
      , "    _out('L " ++ show i ++ " ' + _msg(_e))"
      , "    _loaded = False"
      , "if _loaded:"
      ] ++ concat (zipWith (query i c) [0 :: Int ..] (icArgs c)) ++ ["    pass"]
    query i c j args =
      [ "    try:"
      , "        _D['iu'] = 0; _D['in'] = 0; _D['k'] = 0"
      , "        signal.setitimer(signal.ITIMER_REAL, 10.0)"
      , "        _r = eval(" ++ show ("main." ++ methodOf (icKind c) ++ "(" ++ intercalate ", " (map Py.pyVal args) ++ ")") ++ ", _ns)"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('S " ++ show i ++ " " ++ show j ++ " ' + " ++ pyCountPrefix c ++ "_ser(_r, _ns))"
      , "    except BaseException as _e:"
      , "        signal.setitimer(signal.ITIMER_REAL, 0)"
      , "        _out('E " ++ show i ++ " " ++ show j ++ " ' + _msg(_e))"
      ]

juliaIRDriver :: FilePath -> [(Int, FilePath, IRCase)] -> String
juliaIRDriver projectDir entries = unlines $
  [ "include(" ++ show (projectDir </> "juliaLib.jl") ++ ")"
  , "using .JuliaSPPLLib"
  , "_msg(e) = first(replace(sprint(showerror, e), '\\n' => ' '), 400)"
  -- A generate body's draws come from the case's stream ('icDraws'); each
  -- program module defines its own rand() and randn() as these.
  , "const _DU = Float64[]"
  , "const _DN = Float64[]"
  , "const _DI = [0, 0, 0]"
  , "function _jdraw(xs, k)"
  , "  _DI[k] >= length(xs) && error(\"draw stream exhausted\")"
  , "  _DI[k] += 1; _DI[3] += 1"
  , "  return xs[_DI[k]]"
  , "end"
  , "_jrand() = _jdraw(_DU, 1)"
  , "_jrandn() = _jdraw(_DN, 2)"
  ] ++ juliaSerializer ++ concatMap entry entries
  where
    entry (i, path, c) =
      [ "try"
      , "  include(" ++ show path ++ ")"
      , "catch e"
      , "  println(\"L " ++ show i ++ " \", _msg(e)); flush(stdout)"
      , "end"
      , "empty!(_DU); append!(_DU, Float64" ++ streamLiteral (fst (icDraws c)) ++ ")"
      , "empty!(_DN); append!(_DN, Float64" ++ streamLiteral (snd (icDraws c)) ++ ")"
      ] ++ concat [ [ "try"
                    , "  _DI .= 0"
                    , "  r = Base.invokelatest(" ++ intercalate ", " (("Prog" ++ show i ++ "." ++ fn c) : map (Jl.juliaVal . qualifyConstructors ("Prog" ++ show i)) args) ++ ")"
                    , "  println(\"S " ++ show i ++ " " ++ show j ++ " \", " ++ jlCountPrefix c ++ "join(_ser(r, String[]), \" \")); flush(stdout)"
                    , "catch e"
                    , "  println(\"E " ++ show i ++ " " ++ show j ++ " \", _msg(e)); flush(stdout)"
                    , "end" ]
                  | (j, args) <- zip [0 :: Int ..] (icArgs c) ]
    fn c = "main" ++ bodySuffix (icKind c)
    jlCountPrefix c = if icKind c == GenBody then "\"t i\", _DI[3], \" \", " else ""

-- | Each case carries the interpreter's outcome per argument vector.
runIRCasesPython :: [(IRCase, [([IRValue], InterpOutcome)])] -> IO ([String], [IRDisagreement])
runIRCasesPython = runCases "python" emitPython ".py" pythonIRDriver
  (\f -> (\(_, o, e) -> (o, e)) <$> runBounded "python3" [f])

runIRCasesJulia :: FilePath -> [(IRCase, [([IRValue], InterpOutcome)])] -> IO ([String], [IRDisagreement])
runIRCasesJulia julia cases = runCases "julia" emit ".jl" juliaIRDriver
  (\f -> (\(_, o, e) -> (o, e)) <$> runBounded julia (juliaTestFlags ++ [f])) cases
  where
    emit i c = fmap (fmap (\src -> "module Prog" ++ show i ++ "\nusing ..JuliaSPPLLib\n"
                                  ++ "rand() = Main._jrand()\nrandn() = Main._jrandn()\n" ++ src ++ "\nend\n"))
                  (forcedSource (return (Jl.generateFunctions (irCaseEnv c))))

-- ---------------------------------------------------------------------------
-- The batched arm (M4)
--
-- A 'PResult' case's probability or integrate body is put through the batched
-- PyTorch backend the way batched mode compiles one: the select pass
-- ('selectPassEnv', so @IRIf@s over the tensor fragment become 'IRSelect's)
-- and then 'generateFunctionsBatched', so the batched backend sees
-- select-shaped IR without the compiler's batched admission. Drawn
-- 'IRSelect's (a production since M1) reach it directly too.
--
-- The batch is over the first parameter, a float as a sample is: one point per
-- argument vector, the other parameters taken from the first vector and
-- broadcast. The batch literal is float64, so no point is rounded. Every
-- point the interpreter answers with a value is compared, value against
-- value. Every batched return goes through @check_result@, which raises on a
-- NaN by design: such a raise agrees with an interpreter answer holding a NaN
-- ('judgeOn'), and when the whole batch raises each point is called alone, so
-- one point's NaN does not take the others with it. A case the batched
-- backend refuses is tabulated by reason ('batchedRefusalReason'), not
-- failed, as the typed fuzzer's batched arm does. Value and generate bodies
-- have no batched counterpart compared here: the batched backend emits no
-- @normal_params@ or @writeLogits@, and its generate draws a whole batch with
-- torch's own randomness, which the replay of 'icDraws' does not reach.

-- | A case the batched backend took: the emitted module, and the compared
-- points with the interpreter's answers.
data BatchedIRCase = BatchedIRCase
  { bicCase    :: IRCase
  , bicEnv     :: IREnv                    -- ^ after the select pass
  , bicSource  :: String
  , bicRest    :: [IRValue]                -- ^ the broadcast parameters
  , bicPoints  :: [(IRValue, IRValue)]     -- ^ (first parameter, interpreter's answer)
  }

-- | 'Left' is why the case is not compared on the batched arm.
prepareBatchedIRCase :: IRCase -> IO (Either String BatchedIRCase)
prepareBatchedIRCase c
  | icKind c `notElem` [ProbBody, IntegBody] = return (Left "not a PResult body")
  | null (icParams c) || null (icArgs c) = return (Left "no sample parameter")
  | otherwise = do
      let rest = drop 1 (head (icArgs c))
          firsts = nub' [ a | (a : _) <- icArgs c ]
      answered <- mapM (\a -> (,) a <$> interpretIRCase c (a : rest)) firsts
      let points = [ (a, v) | (a, Interpreted v) <- answered ]
          env = selectPassEnv (irCaseEnv c)
      if null points then return (Left "no point the interpreter answers with a value")
      else if partialSelect then return (Left "a drawn select has a partial arm (outside the select's precondition)")
      else do
        emitted <- try (evaluate (forceEither (generateFunctionsBatched True env)))
        return $ case emitted of
          Left (e :: SomeException) -> Left ("batched codegen crashed: " ++ batchedRefusalReason (show e))
          Right (Left err) -> Left ("refused: " ++ batchedRefusalReason (show err))
          Right (Right src) -> Right (BatchedIRCase c env (intercalate "\n" src) rest points)
  where
    forceEither r = length (show r) `seq` r
    -- A drawn select whose arm may raise is outside the IR contract's select
    -- precondition ('SPLL.IRTypeCheck.inferExpr'): the batched backend
    -- evaluates both arms.
    partialSelect = not (null [ () | IRSelect _ a b <- caseUniverse c, partialExpr a || partialExpr b ])
    -- Points compare by their printed form, so two NaN arguments are one.
    nub' xs = foldr (\x acc -> if show x `elem` map show acc then acc else x : acc) [] (reverse xs)

-- | The batched driver: every case in one torch process, each module in its
-- own namespace, each case one call under a 20 s alarm. A point's answer is
-- printed as 'pythonSerializer''s tokens, read off the batched result at the
-- point's index.
batchedIRDriver :: FilePath -> [BatchedIRCase] -> String
batchedIRDriver projectDir cases = unlines $
  [ "import sys, signal"
  , "sys.path.insert(0, " ++ show projectDir ++ ")"
  , "import torch"
  , "import pythonLibBatched as _plb"
  , "sys.setrecursionlimit(20000)"
  , "class _Timeout(Exception): pass"
  , "def _alarm(signum, frame): raise _Timeout('batch exceeded its time limit')"
  , "signal.signal(signal.SIGALRM, _alarm)"
  , "def _out(s):"
  , "    sys.stdout.write(s + '\\n'); sys.stdout.flush()"
  , "def _msg(e):"
  , "    return (type(e).__name__ + ': ' + str(e)).replace('\\n', ' ')[:400]"
  , "def _bser(v, k):"
  , "    out = []"
  , "    def go(v):"
  , "        if isinstance(v, _plb.T): out.append('t'); go(v.t1); go(v.t2)"
  , "        elif torch.is_tensor(v): go((v[k] if v.dim() > 0 else v).item())"
  , "        elif isinstance(v, bool): out.append('b1' if v else 'b0')"
  , "        elif isinstance(v, int): out.append('i' + repr(v))"
  , "        elif isinstance(v, float): out.append('f' + repr(v))"
  , "        else: out.append('?' + type(v).__name__)"
  , "    go(v)"
  , "    return ' '.join(out)"
  ] ++ concat (zipWith entry [0 :: Int ..] cases)
  where
    entry i bc =
      let c = bicCase bc
          n = length (bicPoints bc)
          lit ps = "torch.tensor([" ++ intercalate ", " (map Py.pyVal ps) ++ "], dtype=torch.float64)"
          call ps = "main." ++ methodOf (icKind c) ++ "(" ++ intercalate ", " (lit ps : map Py.pyVal (bicRest bc)) ++ ")"
          points = map fst (bicPoints bc)
      -- The whole batch in one call; if that raises (one point's NaN fails
      -- the whole return), each point alone, so the raise is the point's.
      in [ "_ns = {}"
         , "try:"
         , "    exec(compile(" ++ show (bicSource bc) ++ ", " ++ show ("prog" ++ show i) ++ ", 'exec'), _ns)"
         , "    _loaded = True"
         , "except BaseException as _e:"
         , "    _loaded = False"
         , "    for _k in range(" ++ show n ++ "):"
         , "        _out('E " ++ show i ++ " ' + str(_k) + ' module did not load: ' + _msg(_e))"
         , "if _loaded:"
         , "  try:"
         , "    signal.setitimer(signal.ITIMER_REAL, 20.0)"
         , "    _r = eval(" ++ show (call points) ++ ", _ns)"
         , "    signal.setitimer(signal.ITIMER_REAL, 0)"
         , "    for _k in range(" ++ show n ++ "):"
         , "        try:"
         , "            _out('S " ++ show i ++ " ' + str(_k) + ' ' + _bser(_r, _k))"
         , "        except BaseException as _e:"
         , "            _out('E " ++ show i ++ " ' + str(_k) + ' ' + _msg(_e))"
         , "  except BaseException as _e:"
         , "    signal.setitimer(signal.ITIMER_REAL, 0)"
         ] ++ concat
         [ [ "    try:"
           , "        signal.setitimer(signal.ITIMER_REAL, 20.0)"
           , "        _r = eval(" ++ show (call [p]) ++ ", _ns)"
           , "        signal.setitimer(signal.ITIMER_REAL, 0)"
           , "        _out('S " ++ show i ++ " " ++ show k ++ " ' + _bser(_r, 0))"
           , "    except BaseException as _e:"
           , "        signal.setitimer(signal.ITIMER_REAL, 0)"
           , "        _out('E " ++ show i ++ " " ++ show k ++ " ' + _msg(_e))" ]
         | (k, p) <- zip [0 :: Int ..] points ]

-- | Run every batched case through one torch-enabled Python process; return
-- each point's outcome label and the disagreements (backend @batched@).
runIRCasesBatched :: FilePath -> [BatchedIRCase] -> IO ([String], [IRDisagreement])
runIRCasesBatched py cases = withSystemTempDirectory "nest-irfuzz-batched" $ \dir -> do
  projectDir <- getCurrentDirectory
  let driverPath = dir </> "driver.py"
  writeFile driverPath (batchedIRDriver projectDir cases)
  (out, err) <- runOnTorchWorker py projectDir driverPath
  let parsed = mapMaybe parseAnswerLine (lines out)
      tailErr = oneLine (unwords (err : [ l | l <- lines out, "W " `isPrefixOf` l ]))
      answerFor i j = case [ a | (i', Just j', a) <- parsed, i' == i, j' == j ] of
        (a : _) -> a
        [] -> case [ a | (i', Nothing, a) <- parsed, i' == i ] of
          (a : _) -> a
          [] -> Raised ("no answer from the batched process; stderr: " ++ tailErr)
      judged = [ case judgeOn "batched" (Interpreted v) a of
                   Right lenient -> ((if valueHasNaN v then "agrees: NaN" else "agrees: value") ++ (if lenient then " (int at a float slot)" else ""), Nothing)
                   Left why -> ("disagreement", Just (IRDisagreement "batched" (bicCase bc) (p : bicRest bc) (Interpreted v) a why (bicSource bc)))
               | (i, bc) <- zip [0 :: Int ..] cases
               , (j, (p, v)) <- zip [0 ..] (bicPoints bc)
               , let a = answerFor i j ]
  return (map fst judged, [ d | (_, Just d) <- judged ])

-- | One long-lived torch process runs every batched driver of the test
-- process, so torch is imported once rather than once per property batch (it
-- takes ~2 s, which twenty batches would add to the property's budget). The
-- worker reads a driver path per line, runs it in a fresh namespace and ends
-- its output with @\@\@DONE@. A worker that dies or overruns
-- 'workerTimeoutMicros' is killed, and the next call starts a fresh one.
data TorchWorker = TorchWorker Handle Handle ProcessHandle

{-# NOINLINE torchWorker #-}
torchWorker :: MVar (Maybe (FilePath, TorchWorker))
torchWorker = unsafePerformIO (newMVar Nothing)

workerTimeoutMicros :: Int
workerTimeoutMicros = 300 * 1000 * 1000

-- | The driver's output and, when the worker failed, why.
runOnTorchWorker :: FilePath -> FilePath -> FilePath -> IO (String, String)
runOnTorchWorker py projectDir driverPath = modifyMVar torchWorker $ \cur -> do
  w@(TorchWorker hin hout _) <- case cur of
    Just (py', w) | py' == py -> return w
    _ -> do
      mapM_ (stopWorker . snd) cur
      startWorker
  acc <- newIORef []
  let readUntilDone = do
        eof <- hIsEOF hout
        if eof then return False else do
          l <- hGetLine hout
          if l == "@@DONE" then return True else modifyIORef' acc (l :) >> readUntilDone
  r <- try (timeout workerTimeoutMicros (hPutStrLn hin driverPath >> hFlush hin >> readUntilDone))
  out <- unlines . reverse <$> readIORef acc
  case r of
    Right (Just True) -> return (Just (py, w), (out, ""))
    Right (Just False) -> stopWorker w >> return (Nothing, (out, "the torch worker exited"))
    Right Nothing -> stopWorker w >> return (Nothing, (out, "the torch worker exceeded " ++ show workerTimeoutMicros ++ "us"))
    Left (e :: SomeException) -> stopWorker w >> return (Nothing, (out, "the torch worker failed: " ++ show e))
  where
    startWorker = do
      devNull <- openFile "/dev/null" WriteMode
      (Just hin, Just hout, _, ph) <- createProcess (proc py ["-u", "-c", workerScript])
        { std_in = CreatePipe, std_out = CreatePipe, std_err = UseHandle devNull }
      hSetBuffering hin LineBuffering
      return (TorchWorker hin hout ph)
    stopWorker (TorchWorker _ _ ph) = terminateProcess ph
    workerScript = unlines
      [ "import sys"
      , "sys.path.insert(0, " ++ show projectDir ++ ")"
      , "import torch, pythonLibBatched"
      , "for _line in sys.stdin:"
      , "    _path = _line.rstrip('\\n')"
      , "    try:"
      , "        exec(compile(open(_path).read(), _path, 'exec'), {'__name__': '__irfuzz_batch__'})"
      , "    except BaseException as _e:"
      , "        sys.stdout.write('W ' + (type(_e).__name__ + ': ' + str(_e)).replace('\\n', ' ')[:400] + '\\n')"
      , "    sys.stdout.write('@@DONE\\n'); sys.stdout.flush()"
      ]

-- ---------------------------------------------------------------------------
-- Coverage

-- | The constructs a case's body reaches ('irConstructs' labels).
checkedIRConstructs :: IRCase -> [String]
checkedIRConstructs c = sort (nub (concatMap irConstructs (irCaseFunction c : map helperFunction (icHelpers c))))
  where helperFunction h = foldr IRLambda (hBody h) (map fst (hParams h))

-- | Every construct the generator's fixed-seed sample reaches: what
-- 'BackendCoverage' measures the corpus census under every config against.
irGeneratorConstructs :: [String]
irGeneratorConstructs = sort (nub (concatMap checkedIRConstructs fixedSample))

-- | Constructs of 'irConstructs'' inventory, or shapes of them, with no
-- production, and why.
noProduction :: [(String, String)]
noProduction =
  [ ("Builtin:BTensor/BReduce/BIndex at rank > 1 or axis > 0",
     "neither text backend emits them (CodeGenPyTorch/CodeGenJulia refuse with rankUnsupported/axisUnsupported); the interpreter is their only consumer, and the compiler emits rank 1, axis 0")
  , ("Builtin:BZip OpIntDiv, BZip OpMod",
     "the value precondition of OpIntDiv/OpMod (an exact, nonzero divisor; IRTypeCheck.inferExpr) cannot be drawn elementwise; the compiler never zips them")
  , ("ITSymbol values", "neither text backend can render a VSymbol constant (pyVal/juliaVal have no case); symbols reach the backends only as network inputs")
  , ("generate bodies on the batched arm",
     "the batched backend draws a whole batch with torch's own rand(n)/randn(n), which the replayed stream (icDraws) does not reach; generate bodies are compared on the text backends")
  , ("function-typed parameters, results and constants of main",
     "the driver has no way to pass a closure to a backend or serialise one back; function types are drawn inside bodies and at helpers' parameters and results")
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

-- | Every 'Builtin', as 'irConstructs' labels it, at every operator it is
-- drawn with. A complete match, as above.
builtinLabels :: [String]
builtinLabels = map ("Builtin:" ++) $
  [ "BTensor", "BMap", "BIndex", "BMapList", "BListIndex", "BCategoricalIndex" ]
  ++ [ "BReduce " ++ show op | op <- [ROpAdd, ROpLogSumExp, ROpMax] ]
  ++ [ "BZip " ++ show op | op <- [OpPlus, OpMult, OpSub, OpDiv, OpMax, OpAnd, OpOr, OpApprox, OpLessThan, OpGreaterThan, OpEq] ]
  where
    _complete b = case b of
      BTensor _ -> (); BMap -> (); BReduce _ _ -> (); BIndex _ -> (); BZip _ -> ()
      BMapList -> (); BListIndex -> (); BCategoricalIndex _ _ -> ()

-- | The function-group and ADT shapes a case reaches (M3), for the coverage
-- check.
caseFeatures :: IRCase -> [String]
caseFeatures c = nub $
  [ "helper " ++ show (hShape h) | h <- icHelpers c ]
  ++ [ "helper call" | any (`elem` map helperRef (icHelpers c)) vars ]
  ++ [ "closure passed (function-typed helper parameter)" | h <- icHelpers c, any (isArrow . snd) (hParams h) ]
  ++ [ "closure returned (function-typed helper result)" | h <- icHelpers c, isArrow (hResult h) ]
  ++ [ "nullary helper" | h <- icHelpers c, null (hParams h) ]
  ++ [ "ADT constructor" | any (`elem` ctors) vars ]
  ++ [ "ADT test" | any (`elem` map ("is" ++) ctors) vars ]
  ++ [ "ADT field accessor" | any (`elem` [ f | (_, _, f, _) <- adtFields (icADTs c) ]) vars ]
  ++ [ "ADT parameter" | any (isADT . snd) (icParams c) ]
  ++ [ "ADT result" | isADT (icResult c) ]
  ++ [ "tensor parameter" | any (isTensor . snd) (icParams c) ]
  ++ [ "tensor result" | isTensor (icResult c) ]
  ++ [ "standard library " ++ f | f <- ["indexOf", "listProd", "listConcat"], f `elem` vars ]
  -- M4: where the draws of a generate body sit.
  ++ [ "generate helper" | h <- icHelpers c, hGen h ]
  ++ [ "draw let-bound and read twice" | IRLetIn v d b <- caseUniverse c, hasDraw d, length (filter (== v) (varsOf b)) > 1 ]
  ++ [ "draw inside a lambda" | IRLambda _ b <- caseUniverse c, hasDraw b ]
  ++ [ "draw in a map's function" | IRBuiltin bi [f, _] <- caseUniverse c, bi `elem` [BMap, BMapList], hasDraw f ]
  ++ [ "draw in an if arm" | IRIf _ a b <- caseUniverse c, hasDraw a || hasDraw b ]
  ++ [ "draw in a recursive generate helper" | h <- icHelpers c, hGen h, hShape h /= HPlain, hasDraw (hBody h) ]
  ++ [ "drawn categorical index" | IRBuiltin (BCategoricalIndex _ _) (IRSample _ : _) <- caseUniverse c ]
  where
    varsOf e = [ v | IRVar v <- universe e ]
    hasDraw e = not (null [ () | IRSample _ <- universe e ])
    vars = [ v | IRVar v <- caseUniverse c ]
    ctors = [ k | d <- icADTs c, (k, _) <- constructors d ]
    isADT t = case t of { ITADT _ -> True; _ -> False }
    isTensor t = case t of { ITTensor _ _ -> True; _ -> False }

featureLabels :: [String]
featureLabels =
  [ "helper " ++ show s | s <- [minBound .. maxBound :: HelperShape] ] ++
  [ "helper call", "closure passed (function-typed helper parameter)", "closure returned (function-typed helper result)"
  , "nullary helper", "ADT constructor", "ADT test", "ADT field accessor", "ADT parameter", "ADT result"
  , "tensor parameter", "tensor result", "standard library indexOf", "standard library listProd", "standard library listConcat"
  , "generate helper", "draw let-bound and read twice", "draw inside a lambda"
  , "draw in a map's function", "draw in an if arm", "draw in a recursive generate helper", "drawn categorical index" ]

-- | Every 'IRExpr' constructor (all have a production since M4) and both
-- sampling primitives.
exprLabels :: [String]
exprLabels = map ("IRExpr:" ++)
  [ "IRIf", "IRSelect", "IROp", "IRUnaryOp", "IRConst", "IRConstruct", "IRDestruct", "IRDensity"
  , "IRCumulative", "IRLetIn", "IRVar", "IRLambda", "IRApply", "IRIsPossible", "IRError", "IRConformsTo"
  , "IRBuiltin", "IRSample" ]
  ++ [ "Sample:IRUniform", "Sample:IRNormal" ]
  where
    _complete e = case e of
      IRIf{} -> (); IRSelect{} -> (); IROp{} -> (); IRUnaryOp{} -> (); IRConst{} -> (); IRConstruct{} -> ()
      IRDestruct{} -> (); IRDensity{} -> (); IRCumulative{} -> (); IRLetIn{} -> (); IRVar{} -> ()
      IRLambda{} -> (); IRApply{} -> (); IRIsPossible{} -> (); IRError{} -> (); IRConformsTo{} -> ()
      IRBuiltin{} -> (); IRSample{} -> ()

-- | A fixed-seed sample of plans per semiring, as the plan coverage check
-- reads it.
fixedPlans :: SemiringChoice -> [PPlan]
fixedPlans c = unGen (vectorOf 300 drawPlan) (mkQCGen (20261013 + fromEnum c)) 30
  where drawPlan = choose (1, 7) >>= \size -> runG [] (genPlan c [("a0", ITFloat)] size)

-- | A fixed-seed sample of cases, as the coverage check reads it.
fixedSample :: [IRCase]
fixedSample = unGen (vectorOf 600 genIRCase) (mkQCGen 20261013) 30

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
      -- The batched arm needs torch: missing it fails, unless
      -- NEST_SKIP_TORCH=1 skips the arm.
      torch <- findTorchPython
      bD <- case torch of
        Just py -> do
          bcases <- rights <$> mapM (prepareBatchedIRCase . kfRepro) knownDisagreements
          if null bcases then return [] else snd <$> runIRCasesBatched py bcases
        Nothing -> noTorch "IR fuzz generator batched pins" >>= maybe (return []) assertFailure
      let backends = "python" : maybe [] (const ["julia"]) julia ++ maybe [] (const ["batched"]) torch
      sequence_
        [ do let ds = [ d | d <- pyD ++ jlD ++ bD, idBackend d == b, show (idCase d) == show (kfRepro kf) ]
             if b `elem` kfBackends kf
               then case ds of
                 [d] -> do t <- knownDisagreement d
                           assertEqual (kfTicket kf ++ " on " ++ b ++ ": recognised as") (Just (kfTicket kf)) t
                 [] -> assertFailure (kfTicket kf ++ ": the repro no longer disagrees on " ++ b
                                     ++ "; if the bug is fixed, drop (or narrow) its knownDisagreements entry")
                 _ -> assertFailure (kfTicket kf ++ ": two entries share this repro; give each its own")
               -- Elsewhere a repro may disagree only as another filed
               -- family: a batched NaN at a zero divisor cannot be shown
               -- without Python's division raising there.
               else do
                 others <- mapM knownDisagreement ds
                 assertEqual (kfTicket kf ++ ": the repro disagrees on " ++ b ++ ", which the entry does not list, and not as another filed family")
                             [] [ idWhy d | (d, t) <- zip ds others, maybe True (== kfTicket kf) t ]
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
  , testCase "a fixed-seed sample reaches every Builtin, at every operator it is drawn with" $ do
      let reached = nub (concatMap checkedIRConstructs fixedSample)
      assertEqual "unreached" [] (filter (`notElem` reached) builtinLabels)
  , testCase "a fixed-seed sample reaches every helper shape, closures both ways, and ADTs" $ do
      let reached = nub (concatMap caseFeatures fixedSample)
      assertEqual "unreached" [] (filter (`notElem` reached) featureLabels)
  -- The design's consequence 3: nesting the compiler reaches only by chance
  -- (a builtin over lists or tensors inside a log-space PResult body) is
  -- drawn by construction, since a PResult body's operands are value
  -- expressions with every production.
  , testCase "a fixed-seed sample reaches the list and tensor builtins inside PResult bodies of every semiring" $ do
      let inside sr = nub [ l | c <- fixedSample, Just (sr', _) <- [icShape c], sr' == sr, l <- checkedIRConstructs c ]
          wanted = [ "Builtin:BMapList", "Builtin:BIndex", "Builtin:BListIndex" ]
      assertEqual "unreached (semiring, builtin)" []
        [ (sr, l) | sr <- [minBound .. maxBound], let r = inside sr, l <- wanted, l `notElem` r ]
  -- M4: the batched arm sees select-shaped IR: selects the generator drew,
  -- and selects the select pass made out of drawn ifs, in bodies the batched
  -- backend emits.
  , testCase "a fixed-seed sample puts drawn and select-pass selects through the batched backend" $ do
      let emitted = [ (c, env) | c <- fixedSample, icKind c `elem` [ProbBody, IntegBody]
                               , let env = selectPassEnv (irCaseEnv c)
                               , either (const False) (const True) (generateFunctionsBatched True env) ]
          selects e = length [ () | IRSelect{} <- universe e ]
          drawn = [ c | (c, _) <- emitted, any ((> 0) . selects) (caseBodies c) ]
          made = [ c | (c, IREnv gs _ _) <- emitted
                     , sum [ selects b | g <- gs, Just (b, _) <- [probFun g, integFun g] ] > sum (map selects (caseBodies c)) ]
      assertBool ("batched-emitted PResult cases with a drawn select: " ++ show (length drawn)) (length drawn >= 5)
      assertBool ("batched-emitted PResult cases with a select the pass made: " ++ show (length made)) (length made >= 5)
  , testCase "a fixed-seed sample reaches both densities and cumulatives in both spaces" $ do
      let reached = nub (concatMap checkedIRConstructs fixedSample)
          wanted = [ k ++ ":" ++ d ++ " " ++ ls | k <- ["Density", "Cumulative"], d <- ["IRNormal", "IRUniform"], ls <- ["Linear", "Log"] ]
      assertEqual "unreached" [] (filter (`notElem` reached) wanted)
  ]
