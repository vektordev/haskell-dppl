-- Aspirational test suite for AutoNeural writeLogits.
--
-- OUT OF SCOPE (intentional — not tested here):
--   § 3.1  collapse operator itself (moment-matching) for non-Gaussian closures (task 07).
--          The *error path* — rejecting a non-Gaussian continuous slot that lacks a
--          collapse — IS covered (writeLogitsError_continuousMixtureRequiresCollapse).
--   § 3.5  sigma=0 / sigma=epsilon floor for hardened / observed values
--
-- Everything else in the design is covered:
--   § 1.1  Output dimension == getSize plan             (writeLogitsInvariant_outputDimMatchesPlan)
--   § 1.2  Per-slot validity: sigma>0, softmax sums to 1, flags in [0,1]
--                                                       (writeLogitsInvariant_*, writeLogitsProps_either*)
--   § 2.2  Gaussian linear ops: +c, *c, -(c), x+y      (writeLogitsProps_gaussian*)
--   § 2.3  Discrete finite-domain maps                  (discrete_manytoonemap test case files)
--   § 2.4  Discrete if-mixture (flag tracks P(Left))    (writeLogitsProps_eitherFlag*)
--   § 2.5  Either/ADT non-identity: exact flag + conditional field slots, incl. composite
--          (nested enum ADT) arms                      (sumTypeNonIdentity group)
--   § 2.6  Tuple = concatenation                        (writeLogitsInvariant_outputDimMatchesPlan)
--   § 3.3  Sample freely allowed                        (implicit in Gaussian programs)
--   § 3.4  Noised void fill on constructor change: dead-arm slots are finite, on-manifold
--          noise; live slots exact; tiny-probability arms stay live    (deadArm group)
--   § 3.7  Cross-slot correlations silently marginalised (no test — not observable)

module TestWriteLogitsProperties
  ( writeLogitsTests
  , writeLogitsRoundtripTests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual, assertFailure)
import Control.Monad (forM_, replicateM)
import Control.Monad.Random (evalRand)
import System.Random (mkStdGen)
import Data.Foldable (toList)
import Data.List (find, isInfixOf, nub, sort)
import Data.Maybe (isJust)

import SPLL.Prelude (runWriteLogits, compile, runWriteLogitsC, runWriteLogitsRandC, runProbNamedC, runGenNamedC)
import SPLL.Parser (tryParseProgram)
import SPLL.Lang.Types
import SPLL.Lang.Lang (constructVList)
import SPLL.AutoNeural (makeAutoNeural, makePartitionPlan, makeProb, getSize, planLayoutString, PartitionPlan(..), adtFlagSlots, stripDeadSlotFills)
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType (RType(..))
import IRInterpreter (generateDet)
import MockNN (evaluateMockNN)
import TestCaseParser (TestCase(..), Backend(..))
import TestTolerances (probTolerance)
import CorpusSweep
import End2EndTesting (writeLogitsArgsFor, endpointPlan, shapeNeuralParams, envelopesShapeable)

------------------------------------------------------------------------
-- Internal helpers

parseOrFail :: String -> IO Program
parseOrFail src =
  case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p

-- The writeLogits bridge lives on the value-producing function, not on a neural declaration.
-- Each test program here writes logits for its `main` output, so "main" is the target.
mainTarget :: String
mainTarget = "main"

-- Run writeLogits and return the flat list of slot values, asserting success.
writeLogitsSlots :: Program -> [IRValue] -> IO [Double]
writeLogitsSlots prog args =
  case runWriteLogits defaultCompilerConfig prog mainTarget args of
    Left err        -> assertFailure ("runWriteLogits failed: " ++ err ++ "\n" ++ show prog) >> return []
    Right (VList l) -> return [x | VFloat x <- toList l]
    Right other     -> assertFailure ("writeLogits returned non-list: " ++ show other) >> return []

checkSlot :: String -> [Double] -> Int -> Double -> Double -> IO ()
checkSlot label slots i expected tol =
  assertBool (label ++ ": slot " ++ show i
              ++ " expected " ++ show expected
              ++ ", got " ++ show (slots !! i)
              ++ " (tol=" ++ show tol ++ ")")
             (abs (slots !! i - expected) < tol)

-- Closed-form writeLogits: no outer NN arguments.
closedWriteLogits :: String -> IO [Double]
closedWriteLogits src = parseOrFail src >>= (`writeLogitsSlots` [])

-- Mock sym: random mode, fixed seed.
mockSeeded :: Int -> IRValue
mockSeeded seed = VTuple (VInt 0) (VInt seed)

-- Mock sym: spike mode — concentrates the NN distribution on one value.
mockSpiked :: IRValue -> IRValue
mockSpiked v = VTuple (VInt 1) (VTuple v (VInt 0))

------------------------------------------------------------------------
-- § 2.2  Gaussian linear ops — exact parameter recovery (closed-form programs)
--
-- These programs use 'Normal' directly (no NN sym arg).  The writeLogits
-- function calls main_normal() analytically and must recover exact
-- (mu, sigma) pairs.  Tolerance is 1e-6 (no sampling, pure arithmetic).

-- 3.0 * Normal  →  mu = 0.0, sigma = 3.0
writeLogitsProps_gaussianScale :: TestTree
writeLogitsProps_gaussianScale = testCase "gaussianScale" $ do
  slots <- closedWriteLogits $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = 3.0 * Normal"
    ]
  assertEqual "writeLogits length" 2 (length slots)
  checkSlot "gaussian_scale" slots 0   0.0  1e-6  -- mu
  checkSlot "gaussian_scale" slots 1   3.0  1e-6  -- sigma

-- (-2.0) * Normal + 1.0  →  mu = 1.0, sigma = |-2| = 2.0
-- Key invariant: sigma = |c|, not c itself.
writeLogitsProps_gaussianNegScale :: TestTree
writeLogitsProps_gaussianNegScale = testCase "gaussianNegScale" $ do
  slots <- closedWriteLogits $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = (-2.0) * Normal + 1.0"
    ]
  assertEqual "writeLogits length" 2 (length slots)
  checkSlot "gaussian_negscale" slots 0   1.0  1e-6  -- mu
  checkSlot "gaussian_negscale" slots 1   2.0  1e-6  -- sigma = |-2| = 2, not -2

-- (Normal + 2.0) + (1.5 * Normal + (-0.5))
-- Each Normal is an independent sample; § 2.2 sum rule applies:
--   mu    = 2.0 + (-0.5) = 1.5
--   sigma = sqrt(1.0^2 + 1.5^2) = sqrt(3.25)
writeLogitsProps_gaussianSum :: TestTree
writeLogitsProps_gaussianSum = testCase "gaussianSum" $ do
  slots <- closedWriteLogits $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = (Normal + 2.0) + (1.5 * Normal + (-0.5))"
    ]
  assertEqual "writeLogits length" 2 (length slots)
  checkSlot "gaussian_sum" slots 0   1.5          1e-6
  checkSlot "gaussian_sum" slots 1   (sqrt 3.25)  1e-6  -- sqrt(1^2 + 1.5^2)

-- Normal - 3.0  →  mu = -3.0, sigma = 1.0
writeLogitsProps_gaussianSub :: TestTree
writeLogitsProps_gaussianSub = testCase "gaussianSub" $ do
  slots <- closedWriteLogits $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = Normal - 3.0"
    ]
  assertEqual "writeLogits length" 2 (length slots)
  checkSlot "gaussian_sub" slots 0 (-3.0) 1e-6  -- mu
  checkSlot "gaussian_sub" slots 1   1.0  1e-6  -- sigma

------------------------------------------------------------------------
-- § 1.2 / § 2.4  Either: flag slot tracks P(Left)
--
-- Plan layout: [flag, P(Left v0|Left), ..., P(Right v0|Right), ...]
-- Flag (slot 0) = P(main = Left VAny).

eitherSrc :: String
eitherSrc = unlines
  [ "neural eitherNN :: (Symbol -> Either Int Bool) of ([0, 1, 2] | [True, False])"
  , "main sym = eitherNN sym"
  ]

-- § 1.2 EitherPlan constructor flag: must lie in [0, 1].
writeLogitsProps_eitherFlagInUnitInterval :: TestTree
writeLogitsProps_eitherFlagInUnitInterval = testCase "eitherFlagInUnitInterval" $ do
  prog <- parseOrFail eitherSrc
  forM_
    [ mockSpiked (VEither (Left  (VInt 0)))
    , mockSpiked (VEither (Right (VBool True)))
    , mockSeeded 42
    , mockSeeded 99
    ] $ \sym -> do
      slots <- writeLogitsSlots prog [sym]
      assertBool ("Either flag out of [0,1]: " ++ show (head slots))
                 (head slots >= 0 && head slots <= 1)

-- When spiked toward Left, flag > 0.5; toward Right, flag < 0.5.
writeLogitsProps_eitherFlagSignMatchesSide :: TestTree
writeLogitsProps_eitherFlagSignMatchesSide = testCase "eitherFlagSignMatchesSide" $ do
  prog    <- parseOrFail eitherSrc
  slotsL  <- writeLogitsSlots prog [mockSpiked (VEither (Left  (VInt 0)))]
  slotsR  <- writeLogitsSlots prog [mockSpiked (VEither (Right (VBool True)))]
  assertBool ("spiked Left:  flag should be > 0.5, got " ++ show (head slotsL))
             (head slotsL > 0.5)
  assertBool ("spiked Right: flag should be < 0.5, got " ++ show (head slotsR))
             (head slotsR < 0.5)

-- § 2.4  Either if-mixture: `if cond then Left .. else Right ..` (non-identity).
-- The flag slot is f = P(cond), realised automatically by the query-based writeLogits
-- (writeLogits = main_prob(Left VAny), and IfThenElse prob compilation mixes the branches).
-- condNN drives the flag; spiking it at 0 makes the condition true (flag > 0.5),
-- spiking it at 1 makes it false (flag < 0.5).  writeLogits is queried on `main`, whose
-- Either Int Bool output type resolves to the EitherPlan via the registry.
eitherIfMixtureSrc :: String
eitherIfMixtureSrc = unlines
  [ "neural outNN  :: (Symbol -> Either Int Bool) of ([0, 1, 2] | [True, False])"
  , "neural condNN :: (Symbol -> Int) of [0, 1]"
  , "main sym = if condNN sym == 0 then left 1 else right True"
  ]

writeLogitsProps_eitherIfMixtureFlag :: TestTree
writeLogitsProps_eitherIfMixtureFlag = testCase "eitherIfMixtureFlag" $ do
  prog   <- parseOrFail eitherIfMixtureSrc
  slotsT <- writeLogitsSlots prog [mockSpiked (VInt 0)]   -- condNN == 0 likely  → flag high
  slotsF <- writeLogitsSlots prog [mockSpiked (VInt 1)]   -- condNN == 1 likely  → flag low
  assertBool ("if-mixture flag must be in [0,1], got " ++ show (head slotsT))
             (head slotsT >= 0 && head slotsT <= 1)
  assertBool ("cond true-spiked: flag should be > 0.5, got " ++ show (head slotsT))
             (head slotsT > 0.5)
  assertBool ("cond false-spiked: flag should be < 0.5, got " ++ show (head slotsF))
             (head slotsF < 0.5)

------------------------------------------------------------------------
-- § 1.2  ADT: constructor flags sum to 1; a single constructor has no flag slot.

adtSrc :: String
adtSrc = unlines
  [ "data MyADT = A i1 :: Int, i2 :: Int"
  , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
  , "main sym = adtNN sym"
  ]

-- With one constructor there is no flag slot at all (task
-- plan-emits-vacuous-single-constructor-flags): a width-1 softmax is identically 1.0,
-- so the layout is just the two field enums, [P(i1=0..2) | P(i2=3..5)], each a
-- distribution of its own. The old layout led with a flag slot pinned at 1.0.
writeLogitsProps_adtSingleConstrHasNoFlagSlot :: TestTree
writeLogitsProps_adtSingleConstrHasNoFlagSlot = testCase "adtSingleConstrHasNoFlagSlot" $ do
  prog <- parseOrFail adtSrc
  forM_ [0, 1, 42, 999 :: Int] $ \seed -> do
    slots <- writeLogitsSlots prog [mockSeeded seed]
    assertEqual ("ADT 1-constructor layout is the two 3-value field enums (seed="
                 ++ show seed ++ ")") 6 (length slots)
    forM_ [("i1", take 3 slots), ("i2", drop 3 slots)] $ \(field, group) ->
      assertBool ("field " ++ field ++ " slots must sum to 1 (seed=" ++ show seed
                  ++ "), got " ++ show group)
                 (abs (sum group - 1.0) < 1e-6)

-- The ticket's repro: nested single-constructor products over Floats. Two vacuous flags
-- (Wrapper's, Position's) used to lead a 6-logit layout.
singleCtorNestedSrc :: String
singleCtorNestedSrc = unlines
  [ "data Position = Position x::Float, y::Float"
  , "data Wrapper = Wrapper pos::Position"
  , "neural extract :: (Symbol -> Wrapper)"
  , "main symbol = extract symbol"
  ]

-- The plan carries no flag slot for either lone constructor: 4 logits, two Gaussians.
readLogitsProps_singleCtorNestedPlan :: TestTree
readLogitsProps_singleCtorNestedPlan = testCase "singleCtorNestedPlanHasNoFlags" $ do
  prog <- parseOrFail singleCtorNestedSrc
  let plan = readLogitsPlan prog
  assertEqual "getSize of nested single-constructor plan" 4 (getSize plan)
  assertBool ("layout must have no constructor-flag row:\n" ++ planLayoutString plan)
             (not ("ctor flags" `isInfixOf` planLayoutString plan))

-- The prob reader must not multiply anything by a bare logit read. In a plan of Gaussian
-- leaves the only reads are mu (subtracted) and sigma (divided by); a bare-read factor
-- is a flag being multiplied in -- which, in the dim channel, multiplied a dimension
-- count by a network output (correct only because the vacuous flag was always 1.0).
readLogitsProps_singleCtorNestedNoFlagFactor :: TestTree
readLogitsProps_singleCtorNestedNoFlagFactor = testCase "singleCtorNestedNoFlagFactor" $ do
  prog <- parseOrFail singleCtorNestedSrc
  case probFun (readLogitsGroup prog) of
    Nothing         -> assertFailure "read-logits network has no prob function"
    Just (probE, _) ->
      assertEqual "multiplications by a bare logit read in the prob reader" []
        [ op | op@(IROp OpMult a b) <- irUniverse probE, isVecRead a || isVecRead b ]
  where
    isVecRead (IRBuiltin BListIndex (IRVar v : _)) = v == vectorOut
    isVecRead _                                    = False

------------------------------------------------------------------------
-- § 2.5  Sum types, non-identity: exact slot values
-- (design 00_bidirectional-autoNeural, "Sum types" / "Design Note: Encode Function
-- Signature").
--
-- The corpus passthroughs (`main sym = nn sym`) pin the Either/ADT layout through
-- LogitIdentity, but an identity program cannot tell a correct conditional encoding from
-- one that merely copies the mock's vector. These programs transform the distribution, and
-- every expected vector below is derived by hand from the program alone, using the design's
-- contract for an Either/ADT region: one flag slot per constructor holding P(ctor) (a single
-- P(Left) for an Either), then each constructor's field slots holding the field's marginal
-- *conditional on that constructor*, P(field = v | ctor) -- the categorical-times-conditional
-- factorisation the plan's readers multiply back out. Nested enum ADTs lay out the same way
-- recursively; Bool enumerates [True, False].

-- Check a whole written vector, slot by slot, against a hand-derived one.
checkVector :: String -> [Double] -> [Double] -> IO ()
checkVector label expected slots = do
  assertEqual (label ++ ": vector length") (length expected) (length slots)
  forM_ (zip [0 ..] expected) $ \(i, e) -> checkSlot label slots i e 1e-9

-- Mock sym: literal mode -- the read-logits network returns exactly this vector.
mockLiteral :: [Double] -> IRValue
mockLiteral xs = VTuple (VInt 2) (constructVList (map VFloat xs))

-- Nested enum ADT field, closed form.
--   P(Nil) = 0.2, P(Obj) = 0.8; given Obj: Red 0.25, Green 0, Blue 0.75.
-- Layout: [P(Nil), P(Obj), P(Red|Obj), P(Green|Obj), P(Blue|Obj)].
writeLogitsProps_adtNestedFieldClosed :: TestTree
writeLogitsProps_adtNestedFieldClosed = testCase "adtNestedFieldClosed" $ do
  slots <- closedWriteLogits $ unlines
    [ "data Color = Red | Green | Blue"
    , "data Object = Nil | Obj color::Color"
    , "main = if Uniform < 0.2 then Nil else (if Uniform < 0.25 then Obj Red else Obj Blue)"
    ]
  checkVector "adtNestedFieldClosed" [0.2, 0.8, 0.25, 0.0, 0.75] slots

-- Nested enum ADT field, through a read-logits network and a remapping that moves mass
-- *between constructors* (Nil -> Obj Red, Obj Red -> Nil) -- the non-identity case the
-- design's Risks section asks for. The network is fed the literal vector
--   [P(Nil)=0.3, P(Obj)=0.7, P(Red|Obj)=0.5, P(Green|Obj)=0.2, P(Blue|Obj)=0.3],
-- so the input joint is Nil 0.3, Obj Red 0.35, Obj Green 0.14, Obj Blue 0.21, and main's
-- output joint is Obj Red 0.3, Nil 0.35, Obj Green 0.14, Obj Blue 0.21:
--   P(Nil) = 0.35, P(Obj) = 0.65, and given Obj: Red 0.3/0.65, Green 0.14/0.65, Blue 0.21/0.65.
adtRemapSrc :: String
adtRemapSrc = unlines
  [ "data Color = Red | Green | Blue"
  , "data Object = Nil | Obj color::Color"
  , "neural readObj :: (Symbol -> Object) of _"
  , "main sym = draw o = readObj sym in if isNil o then Obj Red else (if isRed (color o) then Nil else o)"
  ]

writeLogitsProps_adtRemapThroughNetwork :: TestTree
writeLogitsProps_adtRemapThroughNetwork = testCase "adtRemapThroughNetwork" $ do
  prog  <- parseOrFail adtRemapSrc
  slots <- writeLogitsSlots prog [mockLiteral [0.3, 0.7, 0.5, 0.2, 0.3]]
  checkVector "adtRemapThroughNetwork"
    [0.35, 0.65, 0.3 / 0.65, 0.14 / 0.65, 0.21 / 0.65] slots

-- Two fields under one constructor, correlated with each other within it: the field slots
-- are each field's own conditional marginal (the plan cannot represent the within-ctor
-- correlation; design "Independence is non-representable" -- product of marginals).
--   P(None) = 0.5, P(P) = 0.5. Given P: 0.4 -> (True, False), 0.6 -> (Bernoulli 0.25, True),
--   so P(a=True | P) = 0.4 + 0.6*0.25 = 0.55 and P(b=True | P) = 0.6.
-- Layout: [P(None), P(P), P(a=T|P), P(a=F|P), P(b=T|P), P(b=F|P)].
writeLogitsProps_adtTwoFieldConditionalMarginals :: TestTree
writeLogitsProps_adtTwoFieldConditionalMarginals = testCase "adtTwoFieldConditionalMarginals" $ do
  slots <- closedWriteLogits $ unlines
    [ "data Pt = None | P a::Bool, b::Bool"
    , "main = if Uniform < 0.5 then None else (if Uniform < 0.4 then P True False else P (Uniform < 0.25) True)"
    ]
  checkVector "adtTwoFieldConditionalMarginals" [0.5, 0.5, 0.55, 0.45, 0.6, 0.4] slots

-- An Either whose Left arm is a composite (enum ADT) plan, through a read-logits network and
-- a remapping that moves mass across the Either (Right True -> Left Red). The network is fed
--   [P(Left)=0.4, P(Red|Left)=0.25, P(Green|Left)=0.75, P(True|Right)=0.5, P(False|Right)=0.5],
-- so the input joint is Left Red 0.1, Left Green 0.3, Right True 0.3, Right False 0.3, and the
-- output joint is Left Red 0.4, Left Green 0.3, Right False 0.3:
--   P(Left) = 0.7; given Left: Red 4/7, Green 3/7; given Right: True 0, False 1.
-- Layout: [P(Left), P(Red|Left), P(Green|Left), P(True|Right), P(False|Right)].
-- (Spelled so both `if` arms carry the network's full Either tag: an arm that is a bare
-- `left <ADT literal>` against a `right ..` arm crashes enum annotation in
-- `unionMultiValues`, docs task fuzz-neural-plan-bugs item 2, independent of writeLogits.)
eitherRemapSrc :: String
eitherRemapSrc = unlines
  [ "data Color = Red | Green"
  , "neural readE :: (Symbol -> Either Color Bool) of _"
  , "main sym = draw e = readE sym in if e == right True then left Red else e"
  ]

writeLogitsProps_eitherCompositeArmRemap :: TestTree
writeLogitsProps_eitherCompositeArmRemap = testCase "eitherCompositeArmRemap" $ do
  prog  <- parseOrFail eitherRemapSrc
  slots <- writeLogitsSlots prog [mockLiteral [0.4, 0.25, 0.75, 0.5, 0.5]]
  checkVector "eitherCompositeArmRemap" [0.7, 4 / 7, 3 / 7, 0.0, 1.0] slots

------------------------------------------------------------------------
-- Cross-program invariants
--
-- Each list below enumerates (label, SPLL source, #outer-args).
-- The invariant tests iterate over the list so coverage expands
-- automatically when new programs are added.

type ProgramSpec = (String, String, Int)

gaussianPrograms :: [ProgramSpec]
gaussianPrograms =
  [ ( "gaussian_identity"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main sym = gaussNN sym" ]
    , 1 )
  , ( "gaussian_scale"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main = 3.0 * Normal" ]
    , 0 )
  , ( "gaussian_negscale"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main = (-2.0) * Normal + 1.0" ]
    , 0 )
  , ( "gaussian_sum"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main = (Normal + 2.0) + (1.5 * Normal + (-0.5))" ]
    , 0 )
  , ( "gaussian_sub"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main = Normal - 3.0" ]
    , 0 )
  , ( "gaussian_nonidentity"
    , unlines [ "neural gaussNN :: (Symbol -> Float)"
              , "main sym = gaussNN sym + 3.0" ]
    , 1 )
  ]

discretePrograms :: [ProgramSpec]
discretePrograms =
  [ ( "discrete_identity"
    , unlines [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2]"
              , "main sym = discreteNN sym" ]
    , 1 )
  , ( "discrete_nonidentity"
    , unlines [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2]"
              , "main sym = if discreteNN sym == 0 then 2 else 0" ]
    , 1 )
  , ( "discrete_manytoonemap"
    , unlines [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2, 3]"
              , "main sym = if discreteNN sym == 2 then 0 else if discreteNN sym == 3 then 1 else discreteNN sym" ]
    , 1 )
  ]

-- All programs used for the dimension-invariant test.
allPrograms :: [ProgramSpec]
allPrograms = gaussianPrograms ++ discretePrograms ++
  [ ( "either_identity"
    , unlines [ "neural eitherNN :: (Symbol -> Either Int Bool) of ([0, 1, 2] | [True, False])"
              , "main sym = eitherNN sym" ]
    , 1 )
  , ( "adt_identity"
    , unlines [ "data MyADT = A i1 :: Int, i2 :: Int"
              , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
              , "main sym = adtNN sym" ]
    , 1 )
  , ( "tuple_discrete"
    , unlines [ "neural tupleNN :: (Symbol -> (Int, Bool)) of ([0, 1, 2], [True, False])"
              , "main sym = tupleNN sym" ]
    , 1 )
  , ( "tuple_gaussian"
    , unlines [ "neural tupleNN :: (Symbol -> (Float, Float))"
              , "main = (1.5 * Normal + 2.0, 0.5 * Normal + (-1.0))" ]
    , 0 )
  ]

defaultArgs :: Int -> [IRValue]
defaultArgs n = replicate n (mockSeeded 42)

-- § 1.2  Continuous sigma slot: must be strictly positive.
-- For a Continuous plan, writeLogits = [mu, sigma]; sigma is slot 1.
writeLogitsInvariant_sigmaPositive :: TestTree
writeLogitsInvariant_sigmaPositive = testGroup "sigmaPositive"
  [ testCase name $ do
      prog  <- parseOrFail src
      slots <- writeLogitsSlots prog (defaultArgs n)
      assertBool ("sigma must be > 0 for " ++ name ++ ", got "
                  ++ show (if length slots >= 2 then slots !! 1 else -1))
                 (length slots >= 2 && slots !! 1 > 0)
  | (name, src, n) <- gaussianPrograms
  ]

-- § 1.2  Discrete softmax slots: every entry ≥ 0.
writeLogitsInvariant_discreteNonNegative :: TestTree
writeLogitsInvariant_discreteNonNegative = testGroup "discreteNonNegative"
  [ testCase name $ do
      prog  <- parseOrFail src
      slots <- writeLogitsSlots prog (defaultArgs n)
      forM_ (zip [0 :: Int ..] slots) $ \(i, v) ->
        assertBool ("slot " ++ show i ++ " must be >= 0 for " ++ name
                    ++ ", got " ++ show v)
                   (v >= 0)
  | (name, src, n) <- discretePrograms
  ]

-- § 1.2  Discrete softmax slots: sum to approximately 1.
-- Checked over several mock seeds to cover different NN configurations.
writeLogitsInvariant_discreteSumsToOne :: TestTree
writeLogitsInvariant_discreteSumsToOne = testGroup "discreteSumsToOne"
  [ testCase name $
      forM_ [1, 7, 42 :: Int] $ \seed -> do
        prog  <- parseOrFail src
        slots <- writeLogitsSlots prog (replicate n (mockSeeded seed))
        let total = sum slots
        assertBool ("writeLogits probs must sum to ~1.0 for " ++ name
                    ++ " (seed=" ++ show seed ++ "), got " ++ show total)
                   (abs (total - 1.0) < 1.0e-4)
  | (name, src, n) <- discretePrograms
  ]

-- § 1.1  Output dimension == getSize plan.
-- The plan is derived from the neural declaration's type; it is the
-- contract that writeLogits output must honour regardless of program content.
writeLogitsInvariant_outputDimMatchesPlan :: TestTree
writeLogitsInvariant_outputDimMatchesPlan = testGroup "outputDimMatchesPlan"
  [ testCase name $ do
      prog <- parseOrFail src
      let (target, nnTag) = firstNeuralTarget prog
          plan        = makePartitionPlan (adts prog) target nnTag
          expectedLen = getSize plan
      slots <- writeLogitsSlots prog (defaultArgs n)
      assertEqual ("output dim == getSize plan for " ++ name)
                  expectedLen (length slots)
  | (name, src, n) <- allPrograms
  ]

------------------------------------------------------------------------
-- § 2.4 / § 3.1  A non-Gaussian continuous output must be rejected by writeLogits.
--
-- `if .. then Normal + 2.0 else Normal + 5.0` is a mixture of two Gaussians, which is not
-- Gaussian-closed.  PInfer degrades its PType to Integrate, so no normal-parameter function
-- is generated for the continuous slot.  Encoding it must fail cleanly (a Left
-- CompilerError naming the non-Gaussian continuous output), not dangle on a missing
-- function reference.
writeLogitsError_continuousMixtureRequiresCollapse :: TestTree
writeLogitsError_continuousMixtureRequiresCollapse = testCase "continuousMixtureRequiresCollapse" $ do
  prog <- parseOrFail $ unlines
    [ "neural mixNN :: (Symbol -> Float)"
    , "main = if Uniform < 0.5 then Normal + 2.0 else Normal + 5.0"
    ]
  case runWriteLogits defaultCompilerConfig prog mainTarget [] of
    Left err ->
      assertBool ("error should report a non-Gaussian continuous output, got: " ++ err)
                 ("not Gaussian" `isInfixOf` err)
    Right v  ->
      assertFailure ("expected a compile error for a non-Gaussian continuous output, got: "
                     ++ show v)

------------------------------------------------------------------------
-- Read-logits network logit-index liveness.
--
-- AutoNeural lays a read-logits network's output into a flat logit vector of `getSize plan`
-- slots.
-- The generated `generate` (sampler) and `forward` (probability) readers must index only
-- live slots [0 .. size-1]; furthermore the sampler must reference *every* slot exactly
-- once across the whole layout.  A missing slot (sampled field never reads its logits) or
-- an aliased slot (a field overlapping the constructor flags) means it is sampling from
-- the wrong logits.  This is the regression guard for the `makeGenADTConstr` field-offset
-- bug: an ADT constructor's fields were laid out from index 0 rather than from the
-- constructor's own base index, so for `data Object = NoObj | Object shape, color` the
-- generated sampler read the Shape field off the constructor-flag slots and never touched
-- the last Color slot.

vectorOut :: String
vectorOut = "l_x_neural_out"

-- Every node of an IR expression (the AutoNeural readers contain no binders that shadow the
-- vector, so a flat universe walk is sufficient).
irUniverse :: IRExpr -> [IRExpr]
irUniverse e = e : concatMap irUniverse (getIRSubExprs e)

-- The literal logit indices an expression reads from the neural output vector.  `generate`
-- uses constant indices throughout; `forward` adds a constant base offset to a dynamic
-- indexOf(...) for discrete leaves, so we also take the constant operand of a `+`.
-- A categorical leaf's draw is one 'BCategoricalIndex' over its whole slot window
-- (task neural-categorical-sampler-nests-v-deep), which reads every slot in it.
vectorIndices :: IRExpr -> [Int]
vectorIndices root =
  [ i | IRBuiltin BListIndex [IRVar v, idx] <- irUniverse root, v == vectorOut, i <- idxConsts idx ] ++
  [ i | IRBuiltin (BCategoricalIndex start n) [_, IRVar v] <- irUniverse root, v == vectorOut
      , i <- [start .. start + n - 1] ]
  where
    idxConsts (IRConst (VInt i)) = [i]
    idxConsts (IROp OpPlus a b)  = constOperand a ++ constOperand b
    idxConsts _                  = []
    constOperand (IRConst (VInt i)) = [i]
    constOperand _                  = []

readLogitsGroup :: Program -> IRFunGroup
readLogitsGroup prog =
  makeAutoNeural (adts prog) defaultCompilerConfig [] (head (neurals prog))

-- | Output type and annotation of a program's first neural declaration. Every
-- read-logits fixture is declared as `Symbol -> <output>`; any other shape is a
-- malformed fixture rather than a test failure.
firstNeuralTarget :: Program -> (RType, Maybe MultiValue)
firstNeuralTarget prog = case neurals prog of
  (_, TArrow _ target, tag) : _ -> (target, tag)
  other -> error ("expected a `Symbol -> out` neural declaration, got " ++ show other)

readLogitsPlan :: Program -> PartitionPlan
readLogitsPlan prog =
  let (target, tag) = firstNeuralTarget prog
  in makePartitionPlan (adts prog) target tag

-- Read-logits programs exercising ADT-with-field layouts, plus reuse of the cross-program list.
readLogitsPrograms :: [ProgramSpec]
readLogitsPrograms =
  [ ( "adt_twofield"
    , unlines [ "data MyADT = A i1 :: Int, i2 :: Int"
              , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
              , "main sym = adtNN sym" ]
    , 1 )
  , ( "single_ctor_nested"  -- nested lone constructors: no flag slots, fields start at the region base
    , singleCtorNestedSrc
    , 1 )
  , ( "clevr_reduced"  -- reduced from the CLEVR scene read-logits network; field-carrying + nested ADTs
    , unlines [ "data Object = NoObj | Object shape :: Shape, color :: Color"
              , "data Shape = Cube | Sphere"
              , "data Color = Red | Blue"
              , "neural extractCLEVR :: (Symbol -> Object)"
              , "main sym = extractCLEVR sym" ]
    , 1 )
  ] ++ allPrograms

-- generate must reference every logit slot exactly once across [0 .. size-1].
writeLogitsInvariant_generateCoversAllSlots :: TestTree
writeLogitsInvariant_generateCoversAllSlots = testGroup "generateCoversAllSlots"
  [ testCase name $ do
      prog <- parseOrFail src
      let size = getSize (readLogitsPlan prog)
      case genFun (readLogitsGroup prog) of
        Nothing        -> assertFailure (name ++ ": read-logits network has no generate function")
        Just (gen, _)  ->
          assertEqual (name ++ ": generate must reference every logit slot in [0.."
                       ++ show (size - 1) ++ "] exactly once")
                      [0 .. size - 1] (sort (nub (vectorIndices gen)))
  | (name, src, _) <- readLogitsPrograms
  ]

-- Every logit index read by the probability reader must be in bounds [0 .. size-1].
writeLogitsInvariant_probIndicesInBounds :: TestTree
writeLogitsInvariant_probIndicesInBounds = testGroup "probIndicesInBounds"
  [ testCase name $ do
      prog <- parseOrFail src
      let size = getSize (readLogitsPlan prog)
      case probFun (readLogitsGroup prog) of
        Nothing         -> return ()
        Just (probE, _) ->
          forM_ (vectorIndices probE) $ \i ->
            assertBool (name ++ ": prob reads out-of-range logit index " ++ show i
                        ++ " (size " ++ show size ++ ")")
                       (i >= 0 && i < size)
  | (name, src, _) <- readLogitsPrograms
  ]


------------------------------------------------------------------------
-- § 3.4  Dead arms (task writelogits-dead-arm-nan)
--
-- A constructor of probability exactly zero has no conditional to write: its slots used
-- to be 0/0 (NaN in the interpreter, ZeroDivisionError in Python).  They now hold noise
-- that is on-manifold for each slot (design "Per-slot validity").  Because that noise is
-- random, vectors are compared with *zero-weight-aware* equality: a slot under an arm
-- whose probability is exactly zero in the expected vector is not compared -- inference
-- never reads it, so it carries no information either way (review decision on the task).

-- | Which slots of a plan-shaped vector are live, judged from the vector's own flags:
-- a slot is dead when some enclosing arm has probability exactly zero.
liveSlotMask :: PartitionPlan -> [Double] -> [Bool]
liveSlotMask plan0 v0 = fst (go True plan0 v0)
  where
    go live p xs = case p of
      Discretes _ (MultiDiscretes vals) -> leaf (length vals)
      Discretes _ _                     -> error "liveSlotMask: Discretes without an enumeration"
      Continuous                        -> leaf 2
      TuplePlan a b ->
        let (ma, r1) = go live a xs; (mb, r2) = go live b r1 in (ma ++ mb, r2)
      EitherPlan a b ->
        let pLeft = head xs
            (ma, r1) = go (live && pLeft /= 0) a (tail xs)
            (mb, r2) = go (live && pLeft /= 1) b r1
        in (live : ma ++ mb, r2)
      ADTPlan _ ctors ->
        let nf = adtFlagSlots ctors
            ps = if nf == 0 then [1] else take nf xs
            step (acc, rest) ((_, fps), pc) =
              let (m, r) = goMany (live && pc /= 0) fps rest in (acc ++ m, r)
            (fieldMask, r') = foldl step ([], drop nf xs) (zip ctors ps)
        in (replicate nf live ++ fieldMask, r')
      where leaf n = (replicate n live, drop n xs)
    goMany live fps xs = foldl (\(acc, r) fp -> let (m, r') = go live fp r in (acc ++ m, r')) ([], xs) fps

-- | Per-slot validity violations of a whole vector (design "Formal Constraints"): finite
-- everywhere, softmax groups nonnegative and summing to 1, Either flags in [0, 1], sigma > 0.
planViolations :: PartitionPlan -> [Double] -> [String]
planViolations plan0 v0 =
  [ "slot " ++ show i ++ " is not finite: " ++ show x | (i, x) <- zip [0 :: Int ..] v0, isNaN x || isInfinite x ]
  ++ fst (go plan0 (zip [0 :: Int ..] v0))
  where
    softmax what ys =
      [ what ++ " slots " ++ show (map fst ys) ++ " are not a distribution: " ++ show (map snd ys)
      | any ((< 0) . snd) ys || abs (sum (map snd ys) - 1) > 1e-9 ]
    go p xs = case p of
      Discretes _ (MultiDiscretes vals) -> let (h, t) = splitAt (length vals) xs in (softmax "discrete" h, t)
      Discretes _ _ -> error "planViolations: Discretes without an enumeration"
      Continuous -> case xs of
        (_ : (i, sigma) : t) -> ([ "sigma slot " ++ show i ++ " is not positive: " ++ show sigma | not (sigma > 0) ], t)
        _ -> (["vector too short for a Continuous slot"], [])
      TuplePlan a b -> let (ea, r1) = go a xs; (eb, r2) = go b r1 in (ea ++ eb, r2)
      EitherPlan a b -> case xs of
        ((i, f) : t) ->
          let (ea, r1) = go a t; (eb, r2) = go b r1
          in ([ "Either flag slot " ++ show i ++ " is outside [0, 1]: " ++ show f | f < 0 || f > 1 ] ++ ea ++ eb, r2)
        [] -> (["vector too short for an Either flag"], [])
      ADTPlan _ ctors ->
        let nf = adtFlagSlots ctors
            (flags, t) = splitAt nf xs
            (ef, r') = foldl (\(acc, r) fp -> let (e, r2) = go fp r in (acc ++ e, r2)) ([], t) (concatMap snd ctors)
        in ((if nf == 0 then [] else softmax "ADT flag" flags) ++ ef, r')

-- | Zero-weight-aware vector equality: every live slot of @expected@ (see 'liveSlotMask')
-- matches; dead slots are skipped.
checkVectorLive :: String -> PartitionPlan -> [Double] -> [Double] -> IO ()
checkVectorLive label plan expected slots = do
  assertEqual (label ++ ": vector length") (length expected) (length slots)
  forM_ [ i | (i, True) <- zip [0 ..] (liveSlotMask plan expected) ] $ \i ->
    checkSlot label slots i (expected !! i) 1e-9

-- | Write a closed-form program's main vector and check it end to end: live slots against
-- @expected@ (NaN marks a dead slot, which is what the vector used to hold), the whole vector
-- against the per-slot validity constraints, and the dead slots against the mask.
checkDeadArmProgram :: String -> [String] -> [IRValue] -> [Double] -> IO ()
checkDeadArmProgram label src args expected = do
  prog  <- parseOrFail (unlines src)
  slots <- writeLogitsSlots prog args
  let plan = endpointPlan prog mainTarget
      expectedDead = [ i | (i, x) <- zip [0 :: Int ..] expected, isNaN x ]
      maskDead     = [ i | (i, False) <- zip [0 ..] (liveSlotMask plan slots) ]
  assertEqual (label ++ ": dead slots (by the vector's own flags)") expectedDead maskDead
  checkVectorLive label plan expected slots
  assertEqual (label ++ ": per-slot validity violations in " ++ show slots) [] (planViolations plan slots)

nan :: Double
nan = 0 / 0

colorObject :: [String]
colorObject = [ "data Color = Red | Green | Blue", "data Object = Nil | Obj color::Color" ]

nestedOuter :: [String]
nestedOuter = [ "data Color = Red | Green | Blue", "data Inner = A | B color::Color", "data Outer = N | O inner::Inner" ]

-- The ticket's repro.  Layout: [P(Nil), P(Obj), P(Red|Obj), P(Green|Obj), P(Blue|Obj)].
deadArm_adtField :: TestTree
deadArm_adtField = testCase "adtField" $
  checkDeadArmProgram "adtField" (colorObject ++ ["main = Nil"]) [] [1, 0, nan, nan, nan]

-- An Either arm through a read-logits network fed P(Left) = 1: the Right arm is dead.
-- Layout: [P(Left), P(Red|Left), P(Green|Left), P(True|Right), P(False|Right)].
deadArm_eitherArm :: TestTree
deadArm_eitherArm = testCase "eitherArm" $
  checkDeadArmProgram "eitherArm"
    [ "data Color = Red | Green", "neural readE :: (Symbol -> Either Color Bool) of _", "main sym = readE sym" ]
    [mockLiteral [1.0, 0.25, 0.75, 0.5, 0.5]] [1, 0.25, 0.75, nan, nan]

-- A dead inner constructor inside a live outer one.
-- Layout: [P(N), P(O), P(A|O), P(B|O), P(Red|B,O), P(Green|B,O), P(Blue|B,O)].
deadArm_nestedInner :: TestTree
deadArm_nestedInner = testCase "nestedInnerDead" $
  checkDeadArmProgram "nestedInnerDead" (nestedOuter ++ ["main = O A"]) [] [0, 1, 1, 0, nan, nan, nan]

-- A dead outer constructor: the whole nested region is filled, inner flags included, and
-- those flags must themselves be a valid softmax.
deadArm_nestedOuter :: TestTree
deadArm_nestedOuter = testCase "nestedOuterDead" $
  checkDeadArmProgram "nestedOuterDead" (nestedOuter ++ ["main = N"]) [] [1, 0, nan, nan, nan, nan, nan]

-- A dead arm holding a nested Either: its flag is filled through the sigmoid link, its arms
-- through softmax.  Layout: [P(None), P(Some), P(Left|Some), Bool|Left (2), Bool|Right (2)].
deadArm_nestedEitherFlag :: TestTree
deadArm_nestedEitherFlag = testCase "nestedEitherFlag" $
  checkDeadArmProgram "nestedEitherFlag"
    [ "data W = None | Some e::Either Bool Bool", "main = None" ] [] [1, 0, nan, nan, nan, nan, nan]

-- Per-function endpoint over a real value (the ticket's "common realistic case").
deadArm_perFunctionEndpoint :: TestTree
deadArm_perFunctionEndpoint = testCase "perFunctionEndpoint" $ do
  let src = colorObject ++ ["main b = if b then Nil else Obj Red"]
  checkDeadArmProgram "perFunctionEndpoint True"  src [VBool True]  [1, 0, nan, nan, nan]
  checkDeadArmProgram "perFunctionEndpoint False" src [VBool False] [0, 1, 1, 0, 0]

-- Only an exactly-zero arm is dead.  An arm of probability 1e-300 is reachable and has
-- conditionals of its own, which are written, not filled (review decision on the task).
-- The 1e-300 comes in through a read-logits network: a closed-form `Uniform < 1e-300` arm
-- would not test this, because the compiled prob function itself already folds any branch
-- mass below ~1e-10 to an exact, impossible 0 (a separate defect, filed from this task).
deadArm_tinyArmIsLive :: TestTree
deadArm_tinyArmIsLive = testCase "tinyArmIsLive" $
  checkDeadArmProgram "tinyArmIsLive"
    (colorObject ++ ["neural readO :: (Symbol -> Object) of _", "main sym = readO sym"])
    [mockLiteral [1.0, 1.0e-300, 0.25, 0.5, 0.25]] [1.0, 1.0e-300, 0.25, 0.5, 0.25]

-- The fill is noise, not a constant: different generators give different dead slots and
-- identical live ones.
deadArm_fillIsFreshNoise :: TestTree
deadArm_fillIsFreshNoise = testCase "fillIsFreshNoise" $ do
  prog <- parseOrFail (unlines (colorObject ++ ["main = Nil"]))
  compiled <- compileOrFail prog
  let run seed = evalRand (runWriteLogitsRandC prog compiled mainTarget []) (mkStdGen seed)
      floats (Right (VList l)) = return [x | VFloat x <- toList l]
      floats other = assertFailure ("writeLogits failed: " ++ show other) >> return []
  vs <- mapM (floats . run) [1, 2]
  case vs of
    [a, b] -> do
      assertEqual "live slots do not depend on the generator" (take 2 a) (take 2 b)
      assertBool ("dead slots should be fresh noise, got " ++ show (drop 2 a) ++ " twice") (drop 2 a /= drop 2 b)
    _ -> assertFailure "expected two vectors"

-- The compile-time purity guard sees a writeLogits body through 'stripDeadSlotFills', which
-- must remove a dead-arm fill and nothing else: randomness on the live side of the guard,
-- or under any other `if`, stays visible.
deadArm_stripOnlyFills :: TestTree
deadArm_stripOnlyFills = testCase "stripDeadSlotFillsOnlyStripsFills" $ do
  let zero = IRConst (VFloat 0)
      guardOn v fill live = IRIf (IROp OpEq (IRVar v) zero) fill live
      samples e = length [ () | IRSample _ <- irUniverse e ]
  assertEqual "the fill of a dead-arm guard is stripped" 0
    (samples (stripDeadSlotFills (guardOn "l_wlarm_main_normal_Obj" (IRSample IRNormal) (IRConst (VFloat 1)))))
  assertEqual "the live side of a dead-arm guard is kept" 1
    (samples (stripDeadSlotFills (guardOn "l_wlarm_main_normal_Obj" (IRConst (VFloat 1)) (IRSample IRNormal))))
  assertEqual "an ordinary `if` on a user variable is untouched" 1
    (samples (stripDeadSlotFills (guardOn "x" (IRSample IRNormal) (IRConst (VFloat 1)))))

deadArmTests :: TestTree
deadArmTests = testGroup "deadArm"
  [ deadArm_adtField
  , deadArm_eitherArm
  , deadArm_nestedInner
  , deadArm_nestedOuter
  , deadArm_nestedEitherFlag
  , deadArm_perFunctionEndpoint
  , deadArm_tinyArmIsLive
  , deadArm_fillIsFreshNoise
  , deadArm_stripOnlyFills
  ]

------------------------------------------------------------------------

writeLogitsTests :: TestTree
writeLogitsTests = testGroup "WriteLogits"
  [ testGroup "gaussianParams"
      [ writeLogitsProps_gaussianScale
      , writeLogitsProps_gaussianNegScale
      , writeLogitsProps_gaussianSum
      , writeLogitsProps_gaussianSub
      ]
  , testGroup "either"
      [ writeLogitsProps_eitherFlagInUnitInterval
      , writeLogitsProps_eitherFlagSignMatchesSide
      , writeLogitsProps_eitherIfMixtureFlag
      ]
  , testGroup "sumTypeNonIdentity"
      [ writeLogitsProps_adtNestedFieldClosed
      , writeLogitsProps_adtRemapThroughNetwork
      , writeLogitsProps_adtTwoFieldConditionalMarginals
      , writeLogitsProps_eitherCompositeArmRemap
      ]
  , writeLogitsProps_adtSingleConstrHasNoFlagSlot
  , readLogitsProps_singleCtorNestedPlan
  , readLogitsProps_singleCtorNestedNoFlagFactor
  , writeLogitsInvariant_sigmaPositive
  , writeLogitsInvariant_discreteNonNegative
  , writeLogitsInvariant_discreteSumsToOne
  , writeLogitsInvariant_outputDimMatchesPlan
  , writeLogitsError_continuousMixtureRequiresCollapse
  , writeLogitsInvariant_generateCoversAllSlots
  , writeLogitsInvariant_probIndicesInBounds
  , deadArmTests
  ]

------------------------------------------------------------------------
-- Corpus roundtrip invariants: writeLogits and the read-logits readers must be two
-- views of the same logit-vector semantics. Two complementary directions:
--
--  * LogitIdentity (logits -> distribution -> logits): for every corpus
--    program whose main is a pure read-logits passthrough (`main sym = nn sym`),
--    feeding the mock NN a literal logit vector and writing main's output
--    distribution back out must reproduce that vector exactly. This pins the slot
--    *layout*: writeLogits's discrete slots re-derive their values through the
--    prob reader's index arithmetic, continuous slots through the
--    normal-params extraction, so any drift between makeGen/makeProb/writeLogits
--    offsets surfaces as a slot mismatch. (It cannot catch formula bugs:
--    both sides of the identity go through the same reader.)
--
--  * DensityAgreement (distribution -> logits -> distribution): for every
--    writeLogits invocation the corpus declares (`writeLogits_len`/`writeLogits_at`
--    cases, giving a known-good endpoint + argument list), the endpoint's written
--    logit vector, read back through the plan's standalone prob reader, must
--    assign the same (prob, dim) as the endpoint's own compiled prob
--    function at forward-sampled points. On transformed outputs (e.g. the
--    affine-Gaussian family) the two sides take independent compiler paths
--    (toIRNormalParams vs makeProbRec), so this direction catches *formula*
--    bugs -- e.g. a mis-(de)normalized mu/sigma in the Gaussian reader.
--    Valid only where the output distribution is plan-representable
--    (independent tuple slots -- true of the current writeLogits corpus; a
--    dependent-slot program would need excluding here, since writeLogits
--    deliberately marginalises cross-slot correlations, design § 3.7).

-- `main sym = nn sym` (after normalization: a ReadNN directly on the lambda
-- parameter). Only for these does main's output distribution equal the
-- read-logits network's own, making writeLogits the vector-level identity.
isReadLogitsPassthrough :: Program -> Bool
isReadLogitsPassthrough p = case lookup "main" (functions p) of
  Just (Expr _ (Lambda s (Expr _ (ReadNN _ (Expr _ (Var s')))))) -> s == s'
  _                                                              -> False

compileOrFail :: Program -> IO IREnv
compileOrFail p = either (\e -> assertFailure ("compile failed: " ++ show e) >> return undefined)
                         return (compile defaultCompilerConfig p)

-- Whether a writeLogits function was actually generated for the named endpoint. The roundtrip
-- invariants only apply where writeLogits exists: a continuous arm inside an Either/ADT is
-- refused (no writeLogits built), so its program is skipped here rather than asserted broken.
writeLogitsGenerated :: Program -> String -> Bool
writeLogitsGenerated p target = case compile defaultCompilerConfig p of
  Right (IREnv groups _ _) -> maybe False (isJust . writeLogitsFun) (find ((== target) . groupName) groups)
  Left _                   -> False

-- | Both sweeps draw on every interpreter-routed, non-slow corpus program,
-- with its unshaped test cases.
writeLogitsRoundtripTests :: Corpus -> IO TestTree
writeLogitsRoundtripTests corpus = do
  identity <- corpusSweep corpus SweepSpec
    { sweepName = "WriteLogitsRoundtrip.LogitIdentity", sweepTier = Default, sweepSlow = SkipSlow
    , sweepSelect = \e -> let p = ceProgram e in
        interpreterRouted e && isReadLogitsPassthrough p && envelopesShapeable p && writeLogitsGenerated p "main"
    , sweepNote = "logits -> distribution -> logits is the identity on a passthrough main" } $ \e ->
      logitIdentityCase (ceName e) (ceProgram e)
  density <- corpusSweepAll corpus SweepSpec
    { sweepName = "WriteLogitsRoundtrip.DensityAgreement", sweepTier = Default, sweepSlow = SkipSlow
    , sweepSelect = \e -> interpreterRouted e && not (null (invocations e))
    , sweepNote = "a written logit vector, read back, gives the endpoint's own (prob, dim)" } $ \es ->
      return $ testGroup "DensityAgreement"
        [ densityAgreementCase (ceName e) p target args
        | e <- es
        , let p = ceProgram e
        , (target, args) <- invocations e
        , writeLogitsGenerated p target
        ]
  return $ testGroup "WriteLogitsRoundtrip" [identity, density]
  where
    interpreterRouted e = Interpreter `elem` ceBackends e
    invocations e = nub [ (t, a) | tc <- ceCases e, Just (t, a) <- [writeLogitsInvocation tc] ]
    writeLogitsInvocation (WriteLogitsLengthTestCase _ t a _)  = Just (t, a)
    writeLogitsInvocation (WriteLogitsSlotTestCase _ t a _ _)  = Just (t, a)
    writeLogitsInvocation _                                 = Nothing

-- logits -> distribution -> logits: writeLogits(main)((2, v)) == v for valid
-- logit vectors v. randomMockNN (mock mode 0) is the generator of valid
-- vectors (normalized softmax groups, sigma > 0, flags in [0,1]).
logitIdentityCase :: String -> Program -> TestTree
logitIdentityCase name p = testCase (name ++ ".logitIdentity") $ do
  compiled <- compileOrFail p
  let plan = endpointPlan p "main"
  forM_ [0 .. 4 :: Int] $ \seed -> do
    let vec = evaluateMockNN plan (VTuple (VInt 0) (VInt seed))
    slots <- case vec of
      VList l -> return l
      other   -> assertFailure (name ++ ": mock NN returned a non-vector: " ++ show other)
    case runWriteLogitsC p compiled "main" (shapeNeuralParams p [VTuple (VInt 2) vec]) of
      Left err -> assertFailure (name ++ ": writeLogits failed: " ++ show err)
      Right (VList out) -> do
        assertEqual (name ++ ": roundtripped vector length") (length (toList slots)) (length (toList out))
        -- Zero-weight-aware: a slot under an arm the input gives probability exactly zero is
        -- dead noise on the way out (task writelogits-dead-arm-nan), so it is not compared.
        let live = liveSlotMask plan [ x | VFloat x <- toList slots ]
        forM_ [ t | (t, True) <- zip (zip3 [0 :: Int ..] (toList slots) (toList out)) live ] $ \(i, sIn, sOut) ->
          case (sIn, sOut) of
            (VFloat vIn, VFloat vOut) ->
              assertBool (name ++ ": logit slot " ++ show i ++ " fed " ++ show vIn
                          ++ " but writeLogits returned " ++ show vOut)
                         (abs (vIn - vOut) < 1e-6)
            _ -> assertFailure (name ++ ": logit slot " ++ show i
                                ++ " is not a float pair: " ++ show (sIn, sOut))
      Right other -> assertFailure (name ++ ": writeLogits returned non-list: " ++ show other)

-- distribution -> logits -> distribution: the endpoint's written vector,
-- read back through the plan's standalone prob reader, agrees with the
-- endpoint's own prob function on forward-sampled points (prob and dim).
densityAgreementCase :: String -> Program -> String -> [IRValue] -> TestTree
densityAgreementCase name p target explicitArgs = testCase caseName $ do
  compiled <- compileOrFail p
  let args = writeLogitsArgsFor p explicitArgs
      plan = endpointPlan p target
      planReader = makeProb (adts p) defaultCompilerConfig plan
      readBack vec x = generateDet (neurals p) (writeLogitsDecls p) compiled [IRConst vec, IRConst x] planReader
  case runWriteLogitsC p compiled target args of
    Left err  -> assertFailure (name ++ ": writeLogits failed: " ++ show err)
    Right vec -> do
      let samples = evalRand (replicateM 20 (runGenNamedC p compiled target args)) (mkStdGen 42)
      forM_ (nub samples) $ \x -> do
        (pOwn, dOwn) <- case runProbNamedC p compiled target args x of
          Right (VProbDim pr d) -> return (pr, d)
          other -> assertFailure (name ++ ": prob(" ++ show x ++ ") returned " ++ show other) >> return (0, 0)
        (pDec, dDec) <- case readBack vec x of
          Right (VTuple (VFloat pr) (VTuple (VFloat d) _)) -> return (pr, d)
          other -> assertFailure (name ++ ": plan reader at " ++ show x ++ " returned " ++ show other) >> return (0, 0)
        assertBool (caseName ++ ": prob differs at sample " ++ show x
                    ++ ": own " ++ show pOwn ++ " vs read-back " ++ show pDec)
                   (abs (pOwn - pDec) < probTolerance)
        assertEqual (caseName ++ ": dim differs at sample " ++ show x) dOwn dDec
  where
    -- distinct .tst invocations of the same endpoint differ only in args;
    -- fold them into the test name so every case is uniquely addressable
    caseName = name ++ "." ++ target
             ++ (if null explicitArgs then "" else show explicitArgs)
             ++ ".densityAgreement"
