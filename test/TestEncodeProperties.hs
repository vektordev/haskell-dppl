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
  ( encodeTests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual, assertFailure)
import Control.Monad (forM_)
import Data.Foldable (toList)
import Data.List (isInfixOf, nub, sort)

import SPLL.Prelude (runEncode)
import SPLL.Parser (tryParseProgram)
import SPLL.Lang.Types
import SPLL.Lang.Lang (Program(..))
import SPLL.AutoNeural (makeAutoNeural, makePartitionPlan, getSize, PartitionPlan(..))
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType (RType(..))

------------------------------------------------------------------------
-- Internal helpers

parseOrFail :: String -> IO Program
parseOrFail src =
  case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p

-- The encode bridge lives on the value-producing function, not on a neural declaration.
-- Each test program here encodes its `main` output, so "main" is the target.
mainTarget :: String
mainTarget = "main"

-- Run encode and return the flat list of slot values, asserting success.
encodeSlots :: Program -> [IRValue] -> IO [Double]
encodeSlots prog args =
  case runEncode defaultCompilerConfig prog mainTarget args of
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
encodeProps_gaussianScale :: TestTree
encodeProps_gaussianScale = testCase "gaussianScale" $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = 3.0 * Normal"
    ]
  assertEqual "encode length" 2 (length slots)
  checkSlot "gaussian_scale" slots 0   0.0  1e-6  -- mu
  checkSlot "gaussian_scale" slots 1   3.0  1e-6  -- sigma

-- (-2.0) * Normal + 1.0  →  mu = 1.0, sigma = |-2| = 2.0
-- Key invariant: sigma = |c|, not c itself.
encodeProps_gaussianNegScale :: TestTree
encodeProps_gaussianNegScale = testCase "gaussianNegScale" $ do
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
encodeProps_gaussianSum :: TestTree
encodeProps_gaussianSum = testCase "gaussianSum" $ do
  slots <- closedEncode $ unlines
    [ "neural gaussNN :: (Symbol -> Float)"
    , "main = (Normal + 2.0) + (1.5 * Normal + (-0.5))"
    ]
  assertEqual "encode length" 2 (length slots)
  checkSlot "gaussian_sum" slots 0   1.5          1e-6
  checkSlot "gaussian_sum" slots 1   (sqrt 3.25)  1e-6  -- sqrt(1^2 + 1.5^2)

-- Normal - 3.0  →  mu = -3.0, sigma = 1.0
encodeProps_gaussianSub :: TestTree
encodeProps_gaussianSub = testCase "gaussianSub" $ do
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
encodeProps_eitherFlagInUnitInterval :: TestTree
encodeProps_eitherFlagInUnitInterval = testCase "eitherFlagInUnitInterval" $ do
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
encodeProps_eitherFlagSignMatchesSide :: TestTree
encodeProps_eitherFlagSignMatchesSide = testCase "eitherFlagSignMatchesSide" $ do
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
-- spiking it at 1 makes it false (flag < 0.5).  The encode is queried on `main`, whose
-- Either Int Bool output type resolves to the EitherPlan via the registry.
eitherIfMixtureSrc :: String
eitherIfMixtureSrc = unlines
  [ "neural outNN  :: (Symbol -> Either Int Bool) of ([0, 1, 2] | [True, False])"
  , "neural condNN :: (Symbol -> Int) of [0, 1]"
  , "main sym = if condNN sym == 0 then left 1 else right True"
  ]

encodeProps_eitherIfMixtureFlag :: TestTree
encodeProps_eitherIfMixtureFlag = testCase "eitherIfMixtureFlag" $ do
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
encodeProps_adtSingleConstrFlagIsOne :: TestTree
encodeProps_adtSingleConstrFlagIsOne = testCase "adtSingleConstrFlagIsOne" $ do
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
encodeInvariant_sigmaPositive :: TestTree
encodeInvariant_sigmaPositive = testGroup "sigmaPositive"
  [ testCase name $ do
      prog  <- parseOrFail src
      slots <- encodeSlots prog (defaultArgs n)
      assertBool ("sigma must be > 0 for " ++ name ++ ", got "
                  ++ show (if length slots >= 2 then slots !! 1 else -1))
                 (length slots >= 2 && slots !! 1 > 0)
  | (name, src, n) <- gaussianPrograms
  ]

-- § 1.2  Discrete softmax slots: every entry ≥ 0.
encodeInvariant_discreteNonNegative :: TestTree
encodeInvariant_discreteNonNegative = testGroup "discreteNonNegative"
  [ testCase name $ do
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
encodeInvariant_discreteSumsToOne :: TestTree
encodeInvariant_discreteSumsToOne = testGroup "discreteSumsToOne"
  [ testCase name $
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
encodeInvariant_outputDimMatchesPlan :: TestTree
encodeInvariant_outputDimMatchesPlan = testGroup "outputDimMatchesPlan"
  [ testCase name $ do
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
-- § 2.4 / § 3.1  A non-Gaussian continuous output must be rejected by encode.
--
-- `if .. then Normal + 2.0 else Normal + 5.0` is a mixture of two Gaussians, which is not
-- Gaussian-closed.  PInfer degrades its PType to Integrate, so no normal-parameter function
-- is generated for the continuous slot.  Encoding it must fail cleanly (a Left
-- CompilerError naming the non-Gaussian continuous output), not dangle on a missing
-- function reference.
encodeError_continuousMixtureRequiresCollapse :: TestTree
encodeError_continuousMixtureRequiresCollapse = testCase "continuousMixtureRequiresCollapse" $ do
  prog <- parseOrFail $ unlines
    [ "neural mixNN :: (Symbol -> Float)"
    , "main = if Uniform < 0.5 then Normal + 2.0 else Normal + 5.0"
    ]
  case runEncode defaultCompilerConfig prog mainTarget [] of
    Left err ->
      assertBool ("error should report a non-Gaussian continuous output, got: " ++ err)
                 ("not Gaussian" `isInfixOf` err)
    Right v  ->
      assertFailure ("expected a compile error for a non-Gaussian continuous output, got: "
                     ++ show v)

------------------------------------------------------------------------
-- Decoder logit-index liveness.
--
-- AutoNeural lays a decoder's output into a flat logit vector of `getSize plan` slots.
-- The generated `generate` (sampler) and `forward` (probability) readers must index only
-- live slots [0 .. size-1]; furthermore the sampler must reference *every* slot exactly
-- once across the whole layout.  A missing slot (sampled field never reads its logits) or
-- an aliased slot (a field overlapping the constructor flags) means it is sampling from
-- the wrong logits.  This is the regression guard for the `makeGenADTConstr` field-offset
-- bug: an ADT constructor's fields were laid out from index 0 rather than from the
-- constructor's own base index, so for `data Object = Null | Object shape, color` the
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
vectorIndices :: IRExpr -> [Int]
vectorIndices root =
  [ i | IRIndex (IRVar v) idx <- irUniverse root, v == vectorOut, i <- idxConsts idx ]
  where
    idxConsts (IRConst (VInt i)) = [i]
    idxConsts (IROp OpPlus a b)  = constOperand a ++ constOperand b
    idxConsts _                  = []
    constOperand (IRConst (VInt i)) = [i]
    constOperand _                  = []

decoderGroup :: Program -> IRFunGroup
decoderGroup prog =
  makeAutoNeural (adts prog) defaultCompilerConfig [] (head (neurals prog))

decoderPlan :: Program -> PartitionPlan
decoderPlan prog =
  let (_, TArrow _ target, tag) = head (neurals prog)
  in makePartitionPlan (adts prog) target tag

-- Decoder programs exercising ADT-with-field layouts, plus reuse of the cross-program list.
decoderPrograms :: [ProgramSpec]
decoderPrograms =
  [ ( "adt_twofield"
    , unlines [ "data MyADT = A i1 :: Int, i2 :: Int"
              , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
              , "main sym = adtNN sym" ]
    , 1 )
  , ( "clevr_reduced"  -- reduced from the CLEVR scene decoder; field-carrying + nested ADTs
    , unlines [ "data Object = Null | Object shape :: Shape, color :: Color"
              , "data Shape = Cube | Sphere"
              , "data Color = Red | Blue"
              , "neural extractCLEVR :: (Symbol -> Object)"
              , "main sym = extractCLEVR sym" ]
    , 1 )
  ] ++ allPrograms

-- generate must reference every logit slot exactly once across [0 .. size-1].
encodeInvariant_generateCoversAllSlots :: TestTree
encodeInvariant_generateCoversAllSlots = testGroup "generateCoversAllSlots"
  [ testCase name $ do
      prog <- parseOrFail src
      let size = getSize (decoderPlan prog)
      case genFun (decoderGroup prog) of
        Nothing        -> assertFailure (name ++ ": decoder has no generate function")
        Just (gen, _)  ->
          assertEqual (name ++ ": generate must reference every logit slot in [0.."
                       ++ show (size - 1) ++ "] exactly once")
                      [0 .. size - 1] (sort (nub (vectorIndices gen)))
  | (name, src, _) <- decoderPrograms
  ]

-- Every logit index read by the probability reader must be in bounds [0 .. size-1].
encodeInvariant_probIndicesInBounds :: TestTree
encodeInvariant_probIndicesInBounds = testGroup "probIndicesInBounds"
  [ testCase name $ do
      prog <- parseOrFail src
      let size = getSize (decoderPlan prog)
      case probFun (decoderGroup prog) of
        Nothing         -> return ()
        Just (probE, _) ->
          forM_ (vectorIndices probE) $ \i ->
            assertBool (name ++ ": prob reads out-of-range logit index " ++ show i
                        ++ " (size " ++ show size ++ ")")
                       (i >= 0 && i < size)
  | (name, src, _) <- decoderPrograms
  ]

------------------------------------------------------------------------

encodeTests :: TestTree
encodeTests = testGroup "Encode"
  [ testGroup "gaussianParams"
      [ encodeProps_gaussianScale
      , encodeProps_gaussianNegScale
      , encodeProps_gaussianSum
      , encodeProps_gaussianSub
      ]
  , testGroup "either"
      [ encodeProps_eitherFlagInUnitInterval
      , encodeProps_eitherFlagSignMatchesSide
      , encodeProps_eitherIfMixtureFlag
      ]
  , encodeProps_adtSingleConstrFlagIsOne
  , encodeInvariant_sigmaPositive
  , encodeInvariant_discreteNonNegative
  , encodeInvariant_discreteSumsToOne
  , encodeInvariant_outputDimMatchesPlan
  , encodeError_continuousMixtureRequiresCollapse
  , encodeInvariant_generateCoversAllSlots
  , encodeInvariant_probIndicesInBounds
  ]
