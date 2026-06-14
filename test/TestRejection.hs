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
import SPLL.Lang.Types (Program(..), makeTypeInfo, GenericValue(..))
import SPLL.Examples
import SPLL.Validator (validateProgram)
import SPLL.Prelude (compile, uniform, constB, (#+#))
import SPLL.IntermediateRepresentation (defaultCompilerConfig)
import SPLL.Typing.Infer (addTypeInfo)

import Data.List (isInfixOf)
import Data.Either (isLeft)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

rejectionTests :: TestTree
rejectionTests = testGroup "Rejection"
  [ validatorTests
  , compileRejectsTests
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
