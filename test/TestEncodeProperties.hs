-- Aspirational test suite for AutoNeural encode.
--
-- OUT OF SCOPE (intentional — not tested here):
--   § 3.1  collapse operator itself (moment-matching) for non-Gaussian closures (task 07).
--          The *error path* — rejecting a non-Gaussian continuous slot that lacks a
--          collapse — IS covered (encodeError_continuousMixtureRequiresCollapse).
--   § 3.4  noised void fill on constructor change
--   § 3.5  sigma=0 / sigma=epsilon floor for hardened / observed values
--
-- Everything else in the design is covered:
--   § 1.1  Output dimension == getSize plan             (encodeInvariant_outputDimMatchesPlan)
--   § 1.2  Per-slot validity: sigma>0, softmax sums to 1, flags in [0,1]
--                                                       (encodeInvariant_*, encodeProps_either*)
--   § 2.2  Gaussian linear ops: +c, *c, -(c), x+y      (encodeProps_gaussian*)
--   § 2.3  Discrete finite-domain maps                  (discrete_manytoonemap test case files)
--   § 2.4  Discrete if-mixture (flag tracks P(Left))    (encodeProps_eitherFlag*)
--   § 2.6  Tuple = concatenation                        (encodeInvariant_outputDimMatchesPlan)
--   § 3.3  Sample freely allowed                        (implicit in Gaussian programs)
--   § 3.7  Cross-slot correlations silently marginalised (no test — not observable)

module TestEncodeProperties
  ( encodeProps_gaussianScale
  , encodeProps_gaussianNegScale
  , encodeProps_gaussianSum
  , encodeProps_gaussianSub
  , encodeProps_eitherFlagInUnitInterval
  , encodeProps_eitherFlagSignMatchesSide
  , encodeProps_eitherIfMixtureFlag
  , encodeProps_adtSingleConstrFlagIsOne
  , encodeInvariant_sigmaPositive
  , encodeInvariant_discreteNonNegative
  , encodeInvariant_discreteSumsToOne
  , encodeInvariant_outputDimMatchesPlan
  , encodeError_continuousMixtureRequiresCollapse
  ) where

import Test.HUnit
import Control.Monad (forM_)
import Data.Foldable (toList)
import Data.List (isInfixOf)

import SPLL.Prelude (runEncode)
import SPLL.Parser (tryParseProgram)
import SPLL.Lang.Types
import SPLL.Lang.Lang (Program(..))
import SPLL.AutoNeural (makePartitionPlan, getSize, PartitionPlan(..))
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType (RType(..))

------------------------------------------------------------------------
-- Internal helpers

parseOrFail :: String -> IO Program
parseOrFail src =
  case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p

-- Run encode and return the flat list of slot values, asserting success.
encodeSlots :: Program -> [IRValue] -> IO [Double]
encodeSlots prog args =
  case runEncode defaultCompilerConfig prog args of
    Left err        -> assertFailure ("runEncode failed: " ++ err ++ "\n" ++ show prog) >> return []
    Right (VList l) -> return [x | VFloat x <- toList l]
    Right other     -> assertFailure ("encode returned non-list: " ++ show other) >> return []

checkSlot :: String -> [Double] -> Int -> Double -> Double -> IO ()
checkSlot label slots i expected tol =
  assertBool (label ++ ": slot " ++ show i
              ++ " expected " ++ show expected
              ++ ", got " ++ show (slots !! i)
              ++ " (tol=" ++ show tol ++ ")")
             (abs (slots !! i - expected) < tol)

-- Closed-form encode: no outer NN arguments.
closedEncode :: String -> IO [Double]
closedEncode src = parseOrFail src >>= (`encodeSlots` [])

-- Mock sym: random mode, fixed seed.
mockSeeded :: Int -> IRValue
mockSeeded seed = VTuple (VInt 0) (VInt seed)

-- Mock sym: spike mode — concentrates the NN distribution on one value.
mockSpiked :: IRValue -> IRValue
mockSpiked v = VTuple (VInt 1) (VTuple v (VInt 0))

------------------------------------------------------------------------
-- § 2.2  Gaussian linear ops — exact parameter recovery (closed-form programs)
--
-- These programs use 'Normal' directly (no NN sym arg).  The encode
-- function calls main_normal() analytically and must recover exact
-- (mu, sigma) pairs.  Tolerance is 1e-6 (no sampling, pure arithmetic).

-- 3.0 * Normal  →  mu = 0.0, sigma = 3.0
encodeProps_gaussianScale :: Test
encodeProps_gaussianScale = TestCase $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = 3.0 * Normal"
    ]
  assertEqual "encode length" 2 (length slots)
  checkSlot "gaussian_scale" slots 0   0.0  1e-6  -- mu
  checkSlot "gaussian_scale" slots 1   3.0  1e-6  -- sigma

-- (-2.0) * Normal + 1.0  →  mu = 1.0, sigma = |-2| = 2.0
-- Key invariant: sigma = |c|, not c itself.
encodeProps_gaussianNegScale :: Test
encodeProps_gaussianNegScale = TestCase $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = (-2.0) * Normal + 1.0"
    ]
  assertEqual "encode length" 2 (length slots)
  checkSlot "gaussian_negscale" slots 0   1.0  1e-6  -- mu
  checkSlot "gaussian_negscale" slots 1   2.0  1e-6  -- sigma = |-2| = 2, not -2

-- (Normal + 2.0) + (1.5 * Normal + (-0.5))
-- Each Normal is an independent sample; § 2.2 sum rule applies:
--   mu    = 2.0 + (-0.5) = 1.5
--   sigma = sqrt(1.0^2 + 1.5^2) = sqrt(3.25)
encodeProps_gaussianSum :: Test
encodeProps_gaussianSum = TestCase $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = (Normal + 2.0) + (1.5 * Normal + (-0.5))"
    ]
  assertEqual "encode length" 2 (length slots)
  checkSlot "gaussian_sum" slots 0   1.5          1e-6
  checkSlot "gaussian_sum" slots 1   (sqrt 3.25)  1e-6  -- sqrt(1^2 + 1.5^2)

-- Normal - 3.0  →  mu = -3.0, sigma = 1.0
encodeProps_gaussianSub :: Test
encodeProps_gaussianSub = TestCase $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = Normal - 3.0"
    ]
  assertEqual "encode length" 2 (length slots)
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
encodeProps_eitherFlagInUnitInterval :: Test
encodeProps_eitherFlagInUnitInterval = TestCase $ do
  prog <- parseOrFail eitherSrc
  forM_
    [ mockSpiked (VEither (Left  (VInt 0)))
    , mockSpiked (VEither (Right (VBool True)))
    , mockSeeded 42
    , mockSeeded 99
    ] $ \sym -> do
      slots <- encodeSlots prog [sym]
      assertBool ("Either flag out of [0,1]: " ++ show (head slots))
                 (head slots >= 0 && head slots <= 1)

-- When spiked toward Left, flag > 0.5; toward Right, flag < 0.5.
encodeProps_eitherFlagSignMatchesSide :: Test
encodeProps_eitherFlagSignMatchesSide = TestCase $ do
  prog    <- parseOrFail eitherSrc
  slotsL  <- encodeSlots prog [mockSpiked (VEither (Left  (VInt 0)))]
  slotsR  <- encodeSlots prog [mockSpiked (VEither (Right (VBool True)))]
  assertBool ("spiked Left:  flag should be > 0.5, got " ++ show (head slotsL))
             (head slotsL > 0.5)
  assertBool ("spiked Right: flag should be < 0.5, got " ++ show (head slotsR))
             (head slotsR < 0.5)

-- § 2.4  Either if-mixture: `if cond then Left .. else Right ..` (non-identity).
-- The flag slot is f = P(cond), realised automatically by the query-based encode
-- (encode = main_prob(Left VAny), and IfThenElse prob compilation mixes the branches).
-- condNN drives the flag; spiking it at 0 makes the condition true (flag > 0.5),
-- spiking it at 1 makes it false (flag < 0.5).  The Either decoder NN is declared first
-- so runEncode selects its encode function.
eitherIfMixtureSrc :: String
eitherIfMixtureSrc = unlines
  [ "neural outNN  :: (Symbol -> Either Int Bool) of ([0, 1, 2] | [True, False])"
  , "neural condNN :: (Symbol -> Int) of [0, 1]"
  , "main sym = if condNN sym == 0 then left 1 else right True"
  ]

encodeProps_eitherIfMixtureFlag :: Test
encodeProps_eitherIfMixtureFlag = TestCase $ do
  prog   <- parseOrFail eitherIfMixtureSrc
  slotsT <- encodeSlots prog [mockSpiked (VInt 0)]   -- condNN == 0 likely  → flag high
  slotsF <- encodeSlots prog [mockSpiked (VInt 1)]   -- condNN == 1 likely  → flag low
  assertBool ("if-mixture flag must be in [0,1], got " ++ show (head slotsT))
             (head slotsT >= 0 && head slotsT <= 1)
  assertBool ("cond true-spiked: flag should be > 0.5, got " ++ show (head slotsT))
             (head slotsT > 0.5)
  assertBool ("cond false-spiked: flag should be < 0.5, got " ++ show (head slotsF))
             (head slotsF < 0.5)

------------------------------------------------------------------------
-- § 1.2  ADT: constructor flags sum to 1; single-constructor flag is 1.

adtSrc :: String
adtSrc = unlines
  [ "data MyADT = A i1 :: Int, i2 :: Int"
  , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
  , "main sym = adtNN sym"
  ]

-- With one constructor the flag for A must always be 1.0.
encodeProps_adtSingleConstrFlagIsOne :: Test
encodeProps_adtSingleConstrFlagIsOne = TestCase $ do
  prog <- parseOrFail adtSrc
  forM_ [0, 1, 42, 999 :: Int] $ \seed -> do
    slots <- encodeSlots prog [mockSeeded seed]
    assertBool ("ADT 1-constructor flag must be 1.0 (seed=" ++ show seed
                ++ "), got " ++ show (head slots))
               (abs (head slots - 1.0) < 0.01)

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
-- For a Continuous plan, encode = [mu, sigma]; sigma is slot 1.
encodeInvariant_sigmaPositive :: Test
encodeInvariant_sigmaPositive = TestList
  [ TestCase $ do
      prog  <- parseOrFail src
      slots <- encodeSlots prog (defaultArgs n)
      assertBool ("sigma must be > 0 for " ++ name ++ ", got "
                  ++ show (if length slots >= 2 then slots !! 1 else -1))
                 (length slots >= 2 && slots !! 1 > 0)
  | (name, src, n) <- gaussianPrograms
  ]

-- § 1.2  Discrete softmax slots: every entry ≥ 0.
encodeInvariant_discreteNonNegative :: Test
encodeInvariant_discreteNonNegative = TestList
  [ TestCase $ do
      prog  <- parseOrFail src
      slots <- encodeSlots prog (defaultArgs n)
      forM_ (zip [0 :: Int ..] slots) $ \(i, v) ->
        assertBool ("slot " ++ show i ++ " must be >= 0 for " ++ name
                    ++ ", got " ++ show v)
                   (v >= 0)
  | (name, src, n) <- discretePrograms
  ]

-- § 1.2  Discrete softmax slots: sum to approximately 1.
-- Checked over several mock seeds to cover different NN configurations.
encodeInvariant_discreteSumsToOne :: Test
encodeInvariant_discreteSumsToOne = TestList
  [ TestCase $
      forM_ [1, 7, 42 :: Int] $ \seed -> do
        prog  <- parseOrFail src
        slots <- encodeSlots prog (replicate n (mockSeeded seed))
        let total = sum slots
        assertBool ("encode probs must sum to ~1.0 for " ++ name
                    ++ " (seed=" ++ show seed ++ "), got " ++ show total)
                   (abs (total - 1.0) < 1.0e-4)
  | (name, src, n) <- discretePrograms
  ]

-- § 1.1  Output dimension == getSize plan.
-- The plan is derived from the neural declaration's type; it is the
-- contract that encode output must honour regardless of program content.
encodeInvariant_outputDimMatchesPlan :: Test
encodeInvariant_outputDimMatchesPlan = TestList
  [ TestCase $ do
      prog <- parseOrFail src
      let (_, TArrow _ target, nnTag) = head (neurals prog)
          plan        = makePartitionPlan (adts prog) target nnTag
          expectedLen = getSize plan
      slots <- encodeSlots prog (defaultArgs n)
      assertEqual ("output dim == getSize plan for " ++ name)
                  expectedLen (length slots)
  | (name, src, n) <- allPrograms
  ]

------------------------------------------------------------------------
-- § 2.4 / § 3.1  Continuous if-mixture must be rejected without `collapse`.
--
-- `if .. then Normal + 2.0 else Normal + 5.0` is a mixture of two Gaussians, which is not
-- Gaussian-closed.  PInfer degrades its PType to Integrate, so no normal-parameter function
-- is generated for the continuous slot.  Encoding it must fail cleanly (a Left
-- CompilerError pointing at `collapse`), not dangle on a missing function reference.
encodeError_continuousMixtureRequiresCollapse :: Test
encodeError_continuousMixtureRequiresCollapse = TestCase $ do
  prog <- parseOrFail $ unlines
    [ "neural mixNN :: (Symbol -> Float)"
    , "main = if Uniform < 0.5 then Normal + 2.0 else Normal + 5.0"
    ]
  case runEncode defaultCompilerConfig prog [] of
    Left err ->
      assertBool ("error should mention `collapse`, got: " ++ err)
                 ("collapse" `isInfixOf` err)
    Right v  ->
      assertFailure ("expected a compile error for a non-Gaussian continuous output, got: "
                     ++ show v)
