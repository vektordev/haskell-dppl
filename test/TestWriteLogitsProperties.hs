-- Aspirational test suite for AutoNeural writeLogits.
--
-- OUT OF SCOPE (intentional — not tested here):
--   § 3.1  collapse operator itself (moment-matching) for non-Gaussian closures (task 07).
--          The *error path* — rejecting a non-Gaussian continuous slot that lacks a
--          collapse — IS covered (writeLogitsError_continuousMixtureRequiresCollapse).
--   § 3.4  noised void fill on constructor change
--   § 3.5  sigma=0 / sigma=epsilon floor for hardened / observed values
--
-- Everything else in the design is covered:
--   § 1.1  Output dimension == getSize plan             (writeLogitsInvariant_outputDimMatchesPlan)
--   § 1.2  Per-slot validity: sigma>0, softmax sums to 1, flags in [0,1]
--                                                       (writeLogitsInvariant_*, writeLogitsProps_either*)
--   § 2.2  Gaussian linear ops: +c, *c, -(c), x+y      (writeLogitsProps_gaussian*)
--   § 2.3  Discrete finite-domain maps                  (discrete_manytoonemap test case files)
--   § 2.4  Discrete if-mixture (flag tracks P(Left))    (writeLogitsProps_eitherFlag*)
--   § 2.6  Tuple = concatenation                        (writeLogitsInvariant_outputDimMatchesPlan)
--   § 3.3  Sample freely allowed                        (implicit in Gaussian programs)
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
import System.FilePath (takeBaseName)
import Data.Foldable (toList)
import Data.List (find, isInfixOf, nub, sort)
import Data.Maybe (isJust)

import SPLL.Prelude (runWriteLogits, compile, runWriteLogitsC, runProbNamedC, runGenNamedC)
import SPLL.Parser (tryParseProgram)
import SPLL.Lang.Types
import SPLL.AutoNeural (makeAutoNeural, makePartitionPlan, makeProb, getSize, PartitionPlan(..))
import SPLL.IntermediateRepresentation
import SPLL.Typing.RType (RType(..))
import IRInterpreter (generateDet)
import MockNN (evaluateMockNN)
import TestCaseParser (parseTestCases, parseProgram, TestCase(..), Backend(..))
import TestTolerances (probTolerance)
import End2EndTesting (getAllTestFiles, writeLogitsArgsFor, endpointPlan)

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
-- § 1.2  ADT: constructor flags sum to 1; single-constructor flag is 1.

adtSrc :: String
adtSrc = unlines
  [ "data MyADT = A i1 :: Int, i2 :: Int"
  , "neural adtNN :: (Symbol -> MyADT) of {A [0, 1, 2] [3, 4, 5]}"
  , "main sym = adtNN sym"
  ]

-- With one constructor the flag for A must always be 1.0.
writeLogitsProps_adtSingleConstrFlagIsOne :: TestTree
writeLogitsProps_adtSingleConstrFlagIsOne = testCase "adtSingleConstrFlagIsOne" $ do
  prog <- parseOrFail adtSrc
  forM_ [0, 1, 42, 999 :: Int] $ \seed -> do
    slots <- writeLogitsSlots prog [mockSeeded seed]
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
  , ( "clevr_reduced"  -- reduced from the CLEVR scene read-logits network; field-carrying + nested ADTs
    , unlines [ "data Object = Null | Object shape :: Shape, color :: Color"
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
  , writeLogitsProps_adtSingleConstrFlagIsOne
  , writeLogitsInvariant_sigmaPositive
  , writeLogitsInvariant_discreteNonNegative
  , writeLogitsInvariant_discreteSumsToOne
  , writeLogitsInvariant_outputDimMatchesPlan
  , writeLogitsError_continuousMixtureRequiresCollapse
  , writeLogitsInvariant_generateCoversAllSlots
  , writeLogitsInvariant_probIndicesInBounds
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

-- Corpus pool: every interpreter-routed testCases/*.ppl with its test cases.
loadRoundtripPool :: IO [(String, Program, [TestCase])]
loadRoundtripPool = do
  files <- getAllTestFiles
  pool <- mapM (\(ppl, tst) -> do
    prog <- parseProgram ppl
    (backends, slow, tcs) <- parseTestCases tst
    return (takeBaseName ppl, prog, backends, slow, tcs)) files
  return [(n, p, tcs) | (n, p, backends, slow, tcs) <- pool, Interpreter `elem` backends, not slow]

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

writeLogitsRoundtripTests :: IO TestTree
writeLogitsRoundtripTests = do
  pool <- loadRoundtripPool
  return $ testGroup "WriteLogitsRoundtrip"
    [ testGroup "LogitIdentity"
        [ logitIdentityCase n p | (n, p, _) <- pool, isReadLogitsPassthrough p, writeLogitsGenerated p "main" ]
    , testGroup "DensityAgreement"
        [ densityAgreementCase n p target args
        | (n, p, tcs) <- pool
        , (target, args) <- nub [ (t, a) | tc <- tcs, Just (t, a) <- [writeLogitsInvocation tc] ]
        , writeLogitsGenerated p target
        ]
    ]
  where
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
    case runWriteLogitsC p compiled "main" [VTuple (VInt 2) vec] of
      Left err -> assertFailure (name ++ ": writeLogits failed: " ++ show err)
      Right (VList out) -> do
        assertEqual (name ++ ": roundtripped vector length") (length (toList slots)) (length (toList out))
        forM_ (zip3 [0 :: Int ..] (toList slots) (toList out)) $ \(i, sIn, sOut) ->
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
