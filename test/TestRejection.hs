module TestRejection (rejectionTests) where

-- Exercises the compiler's *unhappy* paths: programs that must be rejected, and
-- the reason they are rejected. Three rejection stages are covered:
--
--   * Validator    -- validateProgram (structural / scoping checks, pre-typing)
--   * Compile      -- the full SPLL.Prelude.compile pipeline must surface the
--                     validator rejection as a Left rather than crash
--   * TypeInference -- programs that pass the validator but are ill-typed
--
-- The initial corpus of invalid programs is drawn from SPLL.Examples (the
-- invalid* family). Unlike the aggregate QuickCheck property in Spec.hs (which
-- only samples one invalid program per run), each program here gets its own
-- HUnit case asserting both that it is rejected and *why* -- so a regression
-- that changes which rule fires is pinpointed to the offending program.

import SPLL.Lang.Lang
import SPLL.Lang.Types (Program(..), makeTypeInfo, GenericValue(..), MultiValue(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Examples
import SPLL.Validator (validateProgram)
import SPLL.Prelude (compile, runProb, runInteg, uniform, constB, constF, (#+#), (#<#))
import SPLL.IntermediateRepresentation (defaultCompilerConfig, checkQueryType)
import SPLL.Typing.Infer (addTypeInfo)

import Control.Exception (try, evaluate, SomeException)
import Data.List (isInfixOf)
import Data.Either (isLeft)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

rejectionTests :: TestTree
rejectionTests = testGroup "Rejection"
  [ validatorTests
  , compileRejectsTests
  , queryTypeGuardTests
  , typeInferenceTests
  ]

-- ----------------------------------------------------------------------------
-- Validator stage
-- ----------------------------------------------------------------------------

-- A program with no 'main' entry point: not reachable via the invalid* family
-- (those all declare main), so it is constructed locally here.
noMainProg :: Program
noMainProg = Program [("notMain", uniform)] [] [] []

-- ANY is a marginal-query sentinel and must never appear in a source program.
anyInProgramProg :: Program
anyInProgramProg = Program [("main", Constant makeTypeInfo VAny)] [] [] []

-- Two PartitionPlan annotations for the same RType (Int) that disagree must be
-- rejected as a conflicting registration -- not reachable via the invalid* family,
-- so it is constructed locally here (see SPLL.Validator.validateEncodeDecls).
encodeCollisionProg :: Program
encodeCollisionProg = Program [("main", constF 1.0)] [] []
  [ (TInt, MultiDiscretes [VInt 0, VInt 1])
  , (TInt, MultiDiscretes [VInt 0, VInt 1, VInt 2])
  ]

-- The (source -> Symbol) "Encoder" neural declaration direction has been removed: it named
-- an external network (NN2) with no SPLL call site. Such a declaration must be rejected at
-- validation, pointing the user at the registry syntax ("neural encode :: T of M").
encoderDeclProg :: Program
encoderDeclProg = Program [("main", constB True)] [("ren", TArrow TBool TSymbol, Nothing)] [] []

-- A neural declaration whose type is not an arrow at all (nor the Encoder-direction
-- arrow above): must be rejected at validation for the same reason -- neural
-- declarations must have the form (Symbol -> target). Previously this fell through
-- validateNeuralShape's catch-all (Right ()) and crashed later, deep in AutoNeural's
-- makeAutoNeural, instead of being rejected here.
malformedNeuralDeclProg :: Program
malformedNeuralDeclProg = Program [("main", constB True)] [("ren", TBool, Nothing)] [] []

-- Each entry: (case name, program, distinctive substring of the expected error).
-- The substring identifies *which* validation rule should fire, so we catch both
-- "should have been rejected but wasn't" and "rejected for the wrong reason".
validatorCases :: [(String, Program, String)]
validatorCases =
  [ ("missingDecl",      invalidMissingDecl,     "used without declaration")
  , ("missingInjF",      invalidMissingInjF,     "Cannot find InjF")
  , ("wrongArgCount",    invalidWrongArgCount,   "Wrong number of arguments")
  , ("duplicateDecl1",   invalidDuplicateDecl1,  "possibly declared multiple times")
  , ("duplicateDecl2",   invalidDuplicateDecl2,  "Shawdowing is not allowed")
  , ("duplicateDecl3",   invalidDuplicateDecl3,  "already a function name")
  , ("duplicateDecl4",   invalidDuplicateDecl4,  "Shawdowing is not allowed")
  , ("duplicateDecl5",   invalidDuplicateDecl5,  "already a function name")
  , ("reservedName",     invalidReservedName,    "already used by an InjF")
  , ("reservedName2",    invalidReservedName2,   "already used by an InjF")
  , ("noMain",           noMainProg,             "no 'main' function")
  , ("anyInProgram",     anyInProgramProg,       "ANY may not be used")
  , ("encodeCollision",  encodeCollisionProg,    "conflicting PartitionPlan annotations")
  , ("encoderDecl",      encoderDeclProg,        "neural encode")
  , ("malformedNeuralDecl", malformedNeuralDeclProg, "must have the form (Symbol -> target)")
  ]

validatorTests :: TestTree
validatorTests = testGroup "Validator"
  [ testCase name $ case validateProgram prog of
      Right () -> assertFailure "Program validated even though it should be rejected"
      Left err -> assertBool
        ("Rejected, but for the wrong reason. Expected substring: " ++ show needle
          ++ "\nGot: " ++ err)
        (needle `isInfixOf` err)
  | (name, prog, needle) <- validatorCases ]

-- ----------------------------------------------------------------------------
-- Compile stage: the public entry point must propagate the rejection as a Left.
-- ----------------------------------------------------------------------------

compileRejectsTests :: TestTree
compileRejectsTests = testGroup "CompileRejects"
  [ testCase name $
      assertBool "compile should return Left for an invalid program"
        (isLeft (compile defaultCompilerConfig prog))
  | (name, prog, _) <- validatorCases ]

-- ----------------------------------------------------------------------------
-- Type-inference stage: well-formed (passes the validator) but ill-typed.
-- ----------------------------------------------------------------------------

-- plus on two Bools: structurally fine (plus is a known 2-ary InjF) so the
-- validator accepts it, but RType inference rejects the class-constraint.
boolPlusBoolProg :: Program
boolPlusBoolProg = Program [("main", constB True #+# constB False)] [] [] []

typeInferenceCases :: [(String, Program)]
typeInferenceCases =
  [ ("boolPlusBool", boolPlusBoolProg)
  ]

typeInferenceTests :: TestTree
typeInferenceTests = testGroup "TypeInference"
  [ testCase name $ case addTypeInfo prog of
      Left _  -> return ()
      Right _ -> assertFailure "Ill-typed program was accepted by type inference"
  | (name, prog) <- typeInferenceCases ]

-- ----------------------------------------------------------------------------
-- Query-type guard: a query value whose type does not match the program's return
-- type (e.g. p(0.5) against a Bool-returning program) must fail with a clear
-- diagnostic rather than a silent bogus number (guard folded away by the
-- optimizer) or a deep "not a boolean" panic. The guard is emitted into the IR
-- (IRConformsTo) and evaluated by the interpreter, so the failure surfaces as a
-- thrown error we catch here. --noTypeCheck (checkQueryType=False) removes it.
-- ----------------------------------------------------------------------------

-- main = Uniform < 0.5 : a Bool-returning program. Symmetric threshold so that,
-- without the guard, the optimizer would fold the sample check away and return a
-- plausible-but-meaningless 0.5 -- the silent case the guard is meant to catch.
boolProg :: Program
boolProg = Program [("main", uniform #<# constF 0.5)] [] [] []

-- Fully forces the query result, propagating any error thrown by the guard.
forced :: (Show e, Show a) => Either e a -> IO (Either SomeException Int)
forced = try . evaluate . length . show

queryTypeGuardTests :: TestTree
queryTypeGuardTests = testGroup "QueryTypeGuard"
  [ testCase "p() rejects a float query against a Bool program" $ do
      res <- forced (runProb defaultCompilerConfig boolProg [] (VFloat 0.5))
      case res of
        Left e  -> assertBool ("expected conformance diagnostic, got: " ++ show e)
                              ("does not conform to return type TBool" `isInfixOf` show e)
        Right _ -> assertFailure "float query against a Bool program was silently accepted"
  , testCase "cdf() rejects a float query against a Bool program" $ do
      res <- forced (runInteg defaultCompilerConfig boolProg [] (VFloat 0.5))
      case res of
        Left e  -> assertBool ("expected conformance diagnostic, got: " ++ show e)
                              ("does not conform to return type TBool" `isInfixOf` show e)
        Right _ -> assertFailure "float cdf query against a Bool program was silently accepted"
  , testCase "p() accepts a well-typed Bool query" $ do
      res <- forced (runProb defaultCompilerConfig boolProg [] (VBool True))
      case res of
        Left e  -> assertFailure ("well-typed Bool query was rejected: " ++ show e)
        Right _ -> return ()
  , testCase "--noTypeCheck disables the guard" $ do
      let conf = defaultCompilerConfig { checkQueryType = False }
      res <- forced (runProb conf boolProg [] (VFloat 0.5))
      case res of
        Left e  -> assertBool ("guard should be off, but a conformance error was raised: " ++ show e)
                              (not ("does not conform" `isInfixOf` show e))
        Right _ -> return ()
  ]
