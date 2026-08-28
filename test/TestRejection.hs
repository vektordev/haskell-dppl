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
import SPLL.Lang.Types (Program(..), makeTypeInfo, GenericValue(..), MultiValue(..), Expr(..), ExprF(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Examples
import SPLL.Validator (validateProgram)
import SPLL.Prelude (compile, runProb, runInteg, uniform, constB, constF, (#+#), (#<#))
import SPLL.IntermediateRepresentation (defaultCompilerConfig, checkQueryType, noIntegrate)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Parser (tryParseProgram)
import SPLL.Typing.AlgebraicDataTypes (anyCtorTestMessage, adtCdfMessage)
import qualified SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorch (pyMangle, pythonKeywords)
import SPLL.CodeGenJulia (juliaMangle, juliaKeywords)
import qualified SPLL.CodeGenJulia
import SPLL.Prelude (compile)

import Control.Exception (try, evaluate, SomeException)
import Data.List (isInfixOf, nub)
import Data.Either (isLeft)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

rejectionTests :: TestTree
rejectionTests = testGroup "Rejection"
  [ validatorTests
  , compileRejectsTests
  , queryTypeGuardTests
  , typeInferenceTests
  , anyCtorTestTests
  , adtCumulativeTests
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
anyInProgramProg = Program [("main", Expr makeTypeInfo (Constant VAny))] [] [] []

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


-- ----------------------------------------------------------------------------
-- Constructor test on a marginal wildcard. A hole has no constructor, so both
-- answers are wrong; the two scalar backends used to answer False (silently
-- deleting that branch's mass) while the interpreter crashed, so the same
-- program gave different numbers depending on where it ran (task
-- is-ctor-on-any-slot-diverges-across-backends). All three must now refuse with
-- the same message.
--
-- The runtime half can only be pinned on the interpreter: the failing shape
-- needs a neural ADT latent, and neural programs are filtered out of the Julia
-- and Python query groups (End2EndTesting.nonNeuralsQueries). The other two
-- backends are pinned at the codegen level instead -- that the emitted
-- predicate carries the refusal and does not fall through to a bare
-- isinstance/isa. Batched mode is out of scope: pythonLibBatched.py has no
-- isAny at all, because batched mode has no marginal-wildcard representation.
-- ----------------------------------------------------------------------------

-- A neural ADT latent observed through a non-point-invertible test (isRed), so
-- the reconstruction carries a hole in the colour slot and the compiled code
-- reaches isRed(ANY).
anyCtorProgSrc :: String
anyCtorProgSrc = unlines
  [ "data Color = Red | Green | Blue"
  , "data Obj = Mk c :: Color, f :: Bool"
  , "neural readObj :: (Symbol -> Obj)"
  , "main sym = let o = readObj sym in (if isRed (c o) then 0 else 1, f o)"
  ]

-- A constructor named after a Python keyword. Emitting it verbatim produced
-- @class None:@, a SyntaxError (task
-- codegen-adt-name-collides-with-target-keyword); the backends now mangle it.
-- The corpus (testCases/adtKeywordNames*) pins that the emitted code runs; what
-- it cannot pin is the invariant below -- that mangling the *identifier* leaves
-- the *diagnostic* still naming what the user wrote, so all three backends and
-- the interpreter keep saying the same words.
keywordCtorProgSrc :: String
keywordCtorProgSrc = unlines
  [ "data Flag = None | Some end::Float"
  , "main = if Uniform < 0.3 then None else Some Uniform"
  ]

-- A plain two-constructor ADT: enough to pin what the backends emit for
-- is<Ctor>, which does not depend on the rest of the program.
adtCodegenProgSrc :: String
adtCodegenProgSrc = unlines
  [ "data Coin = Heads | Tails"
  , "main = isHeads (if Uniform < 0.3 then Heads else Tails)"
  ]

withParsed :: String -> (Program -> IO ()) -> IO ()
withParsed src k = case tryParseProgram "" src of
  Left err -> assertFailure ("test program failed to parse: " ++ show err)
  Right p  -> k p

anyCtorTestTests :: TestTree
anyCtorTestTests = testGroup "AnyConstructorTest"
  [ testCase "interpreter refuses a constructor test on an ANY slot" $
      withParsed anyCtorProgSrc $ \prog -> do
        let conf = defaultCompilerConfig { noIntegrate = True }
            args = [VTuple (VInt 2) (constructVList [ VFloat v | v <- [1.0, 0.5, 0.3, 0.2, 0.4, 0.6] ])]
        res <- forced (runProb conf prog args (VTuple (VInt 0) (VBool True)))
        case res of
          Left e  -> assertBool ("expected the ANY constructor-test refusal, got: " ++ show e)
                                (anyCtorTestMessage "Red" `isInfixOf` show e)
          Right _ -> assertFailure
            "a constructor test on an ANY slot silently produced a number"
  , testCase "emitted Python refuses rather than answering False" $
      withParsed adtCodegenProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> do
            let src = unlines (SPLL.CodeGenPyTorch.generateFunctions True env)
            assertBool "emitted isHeads carries no ANY refusal"
                       (anyCtorTestMessage "Heads" `isInfixOf` src)
  , testCase "emitted Julia refuses rather than answering False" $
      withParsed adtCodegenProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> do
            let src = unlines (SPLL.CodeGenJulia.generateFunctions env)
            assertBool "emitted isHeads carries no ANY refusal"
                       (anyCtorTestMessage "Heads" `isInfixOf` src)
  , testCase "a keyword constructor is mangled in Python identifiers but not in its diagnostic" $
      withParsed keywordCtorProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> do
            let src = unlines (SPLL.CodeGenPyTorch.generateFunctions True env)
            assertBool "Python identifier for constructor None was not mangled"
                       ("class None_:" `isInfixOf` src)
            assertBool "a bare `class None:` survived; the emitted file cannot parse"
                       (not ("class None:" `isInfixOf` src))
            -- The refusal must still quote the source name, or Python says
            -- isNone_ where the interpreter says isNone.
            assertBool "the ANY refusal names the mangled identifier instead of the source constructor"
                       (anyCtorTestMessage "None" `isInfixOf` src)
  , testCase "a keyword field is mangled in Julia identifiers" $
      withParsed keywordCtorProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> do
            let src = unlines (SPLL.CodeGenJulia.generateFunctions env)
            -- `end` closes the struct; unmangled, the module was mis-parsed
            -- rather than rejected at the offending token.
            assertBool "the field accessor was not emitted under a mangled name"
                       ("function end_(x" `isInfixOf` src)
            assertBool "an unmangled `end` accessor is still emitted"
                       (not ("function end(x" `isInfixOf` src))
  , testCase "mangling a keyword does not collide with a name already spelled that way" $ do
      -- The naive rule (mangle exact keywords only) sends the distinct source
      -- names None and None_ both to None_, emitting two `class None_:` where
      -- the second silently shadows the first. Escaping the whole
      -- keyword-plus-underscores family keeps the map injective.
      assertBool "None and None_ collapse onto one Python identifier"
                 (pyMangle "None" /= pyMangle "None_")
      assertBool "end and end_ collapse onto one Julia identifier"
                 (juliaMangle "end" /= juliaMangle "end_")
      assertBool "the escape does not shift a name that needs no mangling"
                 (pyMangle "Some" == "Some" && juliaMangle "fld" == "fld")
      -- Injectivity over the family the escape exists for. Mangling is
      -- deliberately *not* idempotent here: re-mangling shifts one more
      -- underscore along, which is what keeps the members apart.
      assertBool "the keyword-plus-underscores family is not mangled injectively"
                 (length (nub (map pyMangle ["None", "None_", "None__"])) == 3)
      -- No output is itself a keyword, so nothing needs a second round.
      assertBool "a mangled name is still a Python keyword"
                 (not (any ((`elem` pythonKeywords) . pyMangle) pythonKeywords))
      assertBool "a mangled name is still a Julia keyword"
                 (not (any ((`elem` juliaKeywords) . juliaMangle) juliaKeywords))
  , testCase "a collision mangling cannot see is refused, not silently emitted" $
      -- Residue of the name-local design: pyMangle sees one name at a time, so
      -- a field named isNone_ colliding with constructor None's derived
      -- predicate is invisible to it. 'adtIdentifierRenaming' has the whole
      -- declaration set and refuses.
      withParsed collidingNamesProgSrc $ \prog -> do
        res <- forced (Right (compileToPython prog) :: Either String String)
        case res of
          Left e  -> assertBool ("expected the mangling-collision refusal, got: " ++ show e)
                                ("mangling collided" `isInfixOf` show e)
          Right _ -> assertFailure
            "two ADT identifiers were emitted under one name instead of being refused"
  ]

-- A field whose name is what constructor @None@'s predicate mangles to. The two
-- are distinct in the source and indistinguishable in the output.
collidingNamesProgSrc :: String
collidingNamesProgSrc = unlines
  [ "data T = None | Mk isNone_::Float"
  , "main = Mk Uniform"
  ]

compileToPython :: Program -> String
compileToPython prog = case compile defaultCompilerConfig prog of
  Left err  -> error ("compile failed: " ++ show err)
  Right env -> unlines (SPLL.CodeGenPyTorch.generateFunctions True env)


-- ----------------------------------------------------------------------------
-- cdf() on an ADT-valued program. An ADT is an unordered sum, so there is no
-- order for a cumulative distribution to integrate along; the compiler refuses
-- rather than inventing one out of declaration order (task
-- adt-valued-query-corpus-sweep, the "cdf" axis -- pin the refusal, do not
-- silently omit it). The corpus cannot express this: a .tst cdf row asserts a
-- number, and this query has none.
--
-- p() on the same program is unaffected and stays covered by the corpus
-- (testCases/recursiveAdtMultiCtor and friends); the third case here guards
-- against the refusal creeping from the cumulative path onto the point one.
-- ----------------------------------------------------------------------------

-- A two-constructor recursive ADT returned directly by main -- the smallest
-- program whose query type is a TADT.
adtValuedProgSrc :: String
adtValuedProgSrc = unlines
  [ "data DTree = Leaf | Node l::DTree, r::DTree"
  , "genT = if Uniform < 0.6 then Leaf else Node genT genT"
  , "main = genT"
  ]

adtCumulativeTests :: TestTree
adtCumulativeTests = testGroup "AdtCumulative"
  [ testCase "cdf() refuses an ADT-valued program with a diagnostic" $
      withParsed adtValuedProgSrc $ \prog -> do
        res <- forced (runInteg defaultCompilerConfig prog [] (VADT "Leaf" []))
        case res of
          Left e  -> assertBool ("expected the ADT-cdf refusal, got: " ++ show e)
                                (adtCdfMessage "DTree" `isInfixOf` show e)
          Right _ -> assertFailure
            "cdf() on an ADT-valued program produced a number; an ADT has no order to integrate along"
  , testCase "the refusal names the ADT, not a generic placeholder" $
      assertBool "adtCdfMessage does not mention the type it was given"
                 ("DTree" `isInfixOf` adtCdfMessage "DTree")
  , testCase "p() on the same program is unaffected" $
      withParsed adtValuedProgSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VADT "Leaf" []))
        case res of
          Left e  -> assertFailure ("point query on an ADT-valued program was rejected: " ++ show e)
          Right _ -> return ()
  ]
