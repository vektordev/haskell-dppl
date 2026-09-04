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
import SPLL.Lang.Types (makeTypeInfo, GenericValue(..), MultiValue(..), CompilerError)
import SPLL.Typing.RType (RType(..))
import SPLL.Examples
import SPLL.Validator (validateProgram)
import SPLL.Prelude (compile, runProb, runInteg, uniform, constB, constF, (#+#), (#<#))
import SPLL.IntermediateRepresentation (defaultCompilerConfig, checkQueryType, noIntegrate, firstAnyExceptIR, anyExceptCodegenRefusal, IRValue)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Parser (tryParseProgram)
import SPLL.Typing.AlgebraicDataTypes (anyCtorTestMessage, adtCdfMessage)
import qualified SPLL.CodeGenPyTorch
import SPLL.CodeGenPyTorch (pyMangle, pythonKeywords)
import SPLL.CodeGenJulia (juliaMangle, juliaKeywords)
import qualified SPLL.CodeGenJulia

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
  , generateBackedTests
  , generateBackedReadNNSymbolTests
  , generateBackedProjectionTests
  , vAnyExceptCodegenTests
  , intractableComparisonTests
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
-- so it is constructed locally here (see SPLL.Validator.validateWriteLogitsDecls).
writeLogitsCollisionProg :: Program
writeLogitsCollisionProg = Program [("main", constF 1.0)] [] []
  [ (TInt, MultiDiscretes [VInt 0, VInt 1])
  , (TInt, MultiDiscretes [VInt 0, VInt 1, VInt 2])
  ]

-- The reverse (source -> Symbol) neural declaration shape has been removed: it used to
-- name an external network (NN2) with no SPLL call site. Such a declaration must be
-- rejected at validation, pointing the user at the registry syntax ("neural writeLogits ::
-- T of M").
reversedNeuralShapeProg :: Program
reversedNeuralShapeProg = Program [("main", constB True)] [("ren", TArrow TBool TSymbol, Nothing)] [] []

-- A neural declaration whose type is not an arrow at all (nor the reversed-shape
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
  , ("writeLogitsCollision", writeLogitsCollisionProg, "conflicting PartitionPlan annotations")
  , ("reversedNeuralShapeDecl", reversedNeuralShapeProg, "neural writeLogits")
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

-- ----------------------------------------------------------------------------
-- Generate-backed inference: 'toIREnumerate' compiles an enumerated conditional's
-- operands forward, which measures the query correctly only while they are
-- deterministic given the enumerated latents. A branch that is not -- an
-- unbounded self-recursive call with no decreasing argument -- used to compile
-- to `main.generate() == sample`, a "probability" that returns a different
-- number on every call with the same query value, with no crash and no
-- diagnostic on the Python and Julia backends. It must be refused instead: NeST
-- does exact inference (task self-recursive-prob-nondeterministic-fallback).
-- ----------------------------------------------------------------------------

-- "resample both grammars and try again if they disagree". Terminates almost
-- surely under sampling (the recursion is geometric in the disagreement
-- probability) but has no static bound, unlike dice.ppl's `x + (-1.0)`.
selfRecursiveAgreeSrc :: String
selfRecursiveAgreeSrc = unlines
  [ "data Sym = A | B"
  , "genA = if Uniform < 0.7 then A else B"
  , "genB = if Uniform < 0.4 then A else B"
  , "main = let a = genA in"
  , "       let b = genB in"
  , "       if a == b then a else main"
  ]

-- The same enumeration with a constant else branch: deterministic given the
-- enumerated latents, so the forward-and-compare premise holds and it must
-- still compile. Guards the refusal against firing on the shape it was
-- written to leave alone.
enumeratedConstantElseSrc :: String
enumeratedConstantElseSrc = unlines
  [ "data Sym = A | B"
  , "genA = if Uniform < 0.7 then A else B"
  , "genB = if Uniform < 0.4 then A else B"
  , "main = let a = genA in"
  , "       let b = genB in"
  , "       if a == b then a else A"
  ]

generateBackedTests :: TestTree
generateBackedTests = testGroup "GenerateBackedInference"
  [ testCase "unbounded self-recursion in an enumerated branch is refused" $
      withParsed selfRecursiveAgreeSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VADT "A" []))
        case res of
          Left e  -> assertBool ("expected the generate-backed refusal, got: " ++ show e)
                                ("generate-backed fallback" `isInfixOf` show e)
          Right _ -> assertFailure
            "a probability function that draws fresh randomness on every call was accepted"
  , testCase "the refusal names the generator it would have called" $
      withParsed selfRecursiveAgreeSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VADT "A" []))
        assertBool "the refusal does not name main_gen, so it does not say what is wrong"
                   (either (\e -> "main_gen" `isInfixOf` show e) (const False) res)
  , testCase "a deterministic else branch under the same enumeration still compiles" $
      withParsed enumeratedConstantElseSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VADT "A" []))
        case res of
          Left e  -> assertFailure ("a deterministic enumerated branch was refused: " ++ show e)
          Right _ -> return ()
  ]

-- ----------------------------------------------------------------------------
-- A random 'Symbol' argument to 'ReadNN': the two 'toIRGenerate' calls in the
-- 'ReadNN' inference equation and in 'toIRNormalParams' have no guard that
-- their argument is 'Deterministic', so 'readMNist(if Uniform < 0.5 then s
-- else t)' used to compile a probability function that drew the coin *inside*
-- the compiled body -- a different network input, and hence a different
-- number, on every call with the same query (task
-- readnn-random-symbol-generate-backed). This is a special case of the same
-- generate-backed-inference defect as 'GenerateBackedInference' above, so it
-- is caught by the same central guard (task
-- central-generate-backed-prob-body-guard, 'requireNoGenerateBacked') that
-- landed after this task was filed -- Phase 1b of the task's own workflow: no
-- code change needed, this group is the regression test that pins it.
-- ----------------------------------------------------------------------------

-- The symbol argument to readMNist is itself the result of a coin flip
-- between the two program parameters.
readNNRandomSymbolSrc :: String
readNNRandomSymbolSrc = unlines
  [ "neural readMNist :: (Symbol -> Int) of [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"
  , "main s t = readMNist(if Uniform < 0.5 then s else t) ++ 1"
  ]

-- Not affected: the symbol argument is a bound parameter with no random
-- choice above it, so the guard must not fire here.
readNNDeterministicSymbolSrc :: String
readNNDeterministicSymbolSrc = unlines
  [ "neural readMNist :: (Symbol -> Int) of [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"
  , "main s = readMNist(s) ++ 1"
  ]

-- These exercise 'compile' directly rather than 'runProb'/'runInteg':  the
-- refusal fires while assembling the 'IREnv' (which bundles the prob and
-- integ bodies together), before any query value or MockNN-formatted
-- argument would be needed, and using 'compile' keeps that pinned regardless
-- of MockNN's own input-shape requirements.
generateBackedReadNNSymbolTests :: TestTree
generateBackedReadNNSymbolTests = testGroup "GenerateBackedReadNNSymbol"
  [ testCase "a randomly-chosen Symbol argument to ReadNN is refused" $
      withParsed readNNRandomSymbolSrc $ \prog -> do
        res <- forced (compile defaultCompilerConfig prog)
        case res of
          Left e  -> assertBool ("expected the central generate-backed refusal, got: " ++ show e)
                                ("central-generate-backed-prob-body-guard" `isInfixOf` show e)
          Right _ -> assertFailure
            "a probability/integrate function that samples which network input to read was accepted"
  , testCase "the refusal names the offending functions and their randomness source" $
      withParsed readNNRandomSymbolSrc $ \prog -> do
        res <- forced (compile defaultCompilerConfig prog)
        assertBool "the refusal does not name main.prob, main.integ and IRUniform, so it does not say what is wrong"
                   (either (\e -> "main.prob" `isInfixOf` show e
                               && "main.integ" `isInfixOf` show e
                               && "IRUniform" `isInfixOf` show e)
                           (const False) res)
  , testCase "a deterministic Symbol argument to ReadNN still compiles" $
      withParsed readNNDeterministicSymbolSrc $ \prog -> do
        res <- forced (compile defaultCompilerConfig prog)
        case res of
          Left e  -> assertFailure ("a bound, non-random Symbol argument was refused: " ++ show e)
          Right _ -> return ()
  ]

-- ----------------------------------------------------------------------------
-- 'fst'/'snd' discarding an intractable ('Bottom') sibling. ModalityInfer's
-- 'projFst'/'projSnd' are the only pType-*raising* constructs in the
-- language: 'fst (Uniform, Uniform * Uniform)' types 'Integrate' at the
-- projection even though the discarded second component is 'Bottom'.
-- 'toIRInference's "no probabilistic parameter" 'InjF' clauses used to test
-- this via 'countProbParams params == 0', which only counts the three
-- tractable rungs (Integrate/PNormal/PLogNormal) and so treated a 'Bottom'
-- sibling exactly like an absent one -- falling through to 'toIRGenerate'
-- and comparing a *fresh* random draw against the query sample: silently
-- wrong on every call, not a crash, on the Python and Julia backends (task
-- projection-discards-intractable-sibling-generate-backed). Both "count == k"
-- guards (0 and 1 probabilistic parameters) now additionally require every
-- parameter to be measurable (no 'Bottom' among them); a 'fst'/'snd' node
-- with a 'Bottom' sibling then matches no 'InjF' clause at all and falls to
-- 'toIRInference's own catch-all ("found no way to convert to IR"),
-- refusing the program at compile time instead of silently miscompiling it.
-- ----------------------------------------------------------------------------

fstBottomSiblingSrc :: String
fstBottomSiblingSrc = "main = fst (Uniform, Uniform * Uniform)"

sndBottomSiblingSrc :: String
sndBottomSiblingSrc = "main = snd (Uniform * Uniform, Uniform)"

-- Not affected: the discarded sibling is itself measurable (Normal), so
-- every parameter really is either Deterministic or tractable and the fixed
-- guard still fires.
fstNormalSiblingSrc :: String
fstNormalSiblingSrc = "main = fst (Uniform, Normal)"

-- Not affected for a different reason: here it is the *projected* side that
-- is Bottom, not the discarded sibling, so the whole 'fst' node's own pType
-- is Bottom (the meet) and ModalityInfer emits no probability function for
-- 'main' at all -- a clean, pre-existing "no compiled variant for this mode"
-- refusal, not the no-clause-matches crash the buggy predicate produced.
fstProjectedBottomSrc :: String
fstProjectedBottomSrc = "main = fst (Uniform * Uniform, Uniform)"

generateBackedProjectionTests :: TestTree
generateBackedProjectionTests = testGroup "GenerateBackedProjection"
  [ testCase "fst discarding a Bottom sibling is refused, not generate-backed" $
      withParsed fstBottomSiblingSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VFloat 0.5))
        case res of
          Left e  -> assertBool ("expected the no-clause-matches refusal, got: " ++ show e)
                                ("found no way to convert to IR" `isInfixOf` show e)
          Right _ -> assertFailure
            "fst (Uniform, Uniform * Uniform) compiled to a probability function -- \
            \it must be refused, not silently generate-backed"
  , testCase "snd discarding a Bottom sibling is refused, not generate-backed" $
      withParsed sndBottomSiblingSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VFloat 0.5))
        case res of
          Left e  -> assertBool ("expected the no-clause-matches refusal, got: " ++ show e)
                                ("found no way to convert to IR" `isInfixOf` show e)
          Right _ -> assertFailure
            "snd (Uniform * Uniform, Uniform) compiled to a probability function -- \
            \it must be refused, not silently generate-backed"
  , testCase "fst over a tractable (Normal) sibling still compiles" $
      withParsed fstNormalSiblingSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VFloat 0.5))
        case res of
          Left e  -> assertFailure ("fst (Uniform, Normal) was refused: " ++ show e)
          Right _ -> return ()
  , testCase "fst projecting the Bottom side is refused for intractability, not a clause-match crash" $
      -- Deliberately not routed through 'forced': that helper only tells crash
      -- from no-crash (both an ordinary Left and an ordinary Right show without
      -- throwing), and the point of this case is to tell apart two different
      -- *Left*s -- the pre-existing, graceful "no compiled variant" answer from
      -- the buggy no-clause-matches crash the other cases in this group pin.
      withParsed fstProjectedBottomSrc $ \prog ->
        case runProb defaultCompilerConfig prog [] (VFloat 0.5) of
          Left e  -> assertBool ("expected the ordinary Bottom/no-compiled-variant refusal, got: " ++ e)
                                ("has no compiled probability function" `isInfixOf` e)
          Right v -> assertFailure
            ("fst (Uniform * Uniform, Uniform) compiled to a probability function (" ++ show v
              ++ "), but the whole node is Bottom and should have none")
  ]

-- ----------------------------------------------------------------------------
-- VAnyExcept codegen refusal. 'eqInv1'/'eqInv2' (the False-branch witness of an
-- == inverse) and the ADT is<Ctor> inverse materialise 'VAnyExcept' -- "any
-- value other than this one" -- a symbolic set with no runtime representation.
-- The optimizer normally consumes it before codegen; where it survives, the
-- two scalar text backends used to crash deep inside pyVal/juliaVal with an
-- internal IR variable name and a source line ("unknown pyVal for VAnyExcept
-- [...]"), while the interpreter answered the same program correctly. Both
-- scalar backends now refuse at compile time with a diagnostic naming the
-- construct instead (task vanyexcept-unrenderable-in-text-backends).
-- ----------------------------------------------------------------------------

-- Three lines, no neural network: an == observation on a constructor field
-- (reached through head/col) inverts to VAnyExcept on its False branch.
vAnyExceptProgSrc :: String
vAnyExceptProgSrc = unlines
  [ "data Color = Red | Green"
  , "data Obj = Obj col :: Color"
  , "main = let scene = [if Uniform < 0.5 then Obj Red else Obj Green] in col (head scene) == Red"
  ]

vAnyExceptCodegenTests :: TestTree
vAnyExceptCodegenTests = testGroup "VAnyExceptCodegenRefusal"
  [ testCase "the interpreter answers the reproducer directly (the reference this refusal is measured against)" $
      withParsed vAnyExceptProgSrc $ \prog -> do
        res <- forced (runProb defaultCompilerConfig prog [] (VBool True))
        case res of
          Left e  -> assertFailure ("interpreter should answer this program, got: " ++ show e)
          Right _ -> return ()
  , testCase "the compiled IR does carry a VAnyExcept placeholder (guards against a stale reproducer)" $
      withParsed vAnyExceptProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> case firstAnyExceptIR env of
            Just _  -> return ()
            Nothing -> assertFailure
              "expected a VAnyExcept placeholder in the compiled IR; the reproducer may have stopped reproducing"
  , testCase "Python codegen refuses with a diagnostic naming VAnyExcept, not a pyVal panic" $
      withParsed vAnyExceptProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> case anyExceptCodegenRefusal "Python" env of
            Left msg -> assertBool ("diagnostic does not name VAnyExcept: " ++ msg)
                                    ("VAnyExcept" `isInfixOf` msg)
            Right () -> assertFailure "expected a VAnyExcept refusal, none was raised"
  , testCase "Julia codegen refuses with a diagnostic naming VAnyExcept, not a juliaVal panic" $
      withParsed vAnyExceptProgSrc $ \prog ->
        case compile defaultCompilerConfig prog of
          Left err -> assertFailure ("compile failed: " ++ show err)
          Right env -> case anyExceptCodegenRefusal "Julia" env of
            Left msg -> assertBool ("diagnostic does not name VAnyExcept: " ++ msg)
                                    ("VAnyExcept" `isInfixOf` msg)
            Right () -> assertFailure "expected a VAnyExcept refusal, none was raised"
  ]

-- ----------------------------------------------------------------------------
-- Comparisons with no closed form (task
-- ircompiler-integrate-comparison-no-conversion-crash)
-- ----------------------------------------------------------------------------

-- Two operands that each own a CDF, whose *difference* has no closed form.
-- ModalityInfer used to call this pair integral-ready and type the comparison
-- 'Integrate'; IRCompiler, which has an equation only for a fixed bound, two
-- Gaussians, or two enumerable domains, then fell through to its catch-all
-- @error "found no way to convert to IR"@ -- a compiler crash on a well-typed
-- program, and the shape TestFuzz's typed generator kept rediscovering.
--
-- The fix is a typing verdict, not a codegen one: the comparison is
-- sampling-only, so the program keeps its generate function and a probability
-- query is declined by name.
intractableComparisonSrc :: String
intractableComparisonSrc = "main = Uniform > exp(Uniform)\n"

-- The Gaussian-difference case, which *is* closed-form ('normalDiffCdfAtZero').
-- The positive control: it guards the narrowing against over-refusing, which
-- would be just as wrong and much quieter.
gaussianComparisonSrc :: String
gaussianComparisonSrc = "main = Normal > Normal\n"

-- | Run a probability query, forcing it fully so a lazy 'error' surfaces here
-- rather than escaping the assertion. @Left@ is a crash, @Right@ the (declined
-- or answered) result -- a distinction the tests below turn on, since the whole
-- point is that this shape must reach the /declined/ side.
forcedProb :: Program -> IRValue -> IO (Either SomeException (Either CompilerError IRValue))
forcedProb prog x = do
  let res = runProb defaultCompilerConfig prog [] x
  outcome <- try (evaluate (length (show res)))
  return (fmap (const res) outcome)

intractableComparisonTests :: TestTree
intractableComparisonTests = testGroup "IntractableComparison"
  [ testCase "a comparison with no closed form is declined, not crashed" $
      withParsed intractableComparisonSrc $ \prog -> do
        res <- forcedProb prog (VBool True)
        case res of
          Left ex -> assertFailure
            ("the query crashed instead of being declined: " ++ show ex)
          Right (Left e) -> assertBool
            ("expected the missing-variant diagnostic, got: " ++ e)
            ("has no compiled probability function" `isInfixOf` e)
          Right (Right _) -> assertFailure
            "a comparison with no closed-form answer was accepted for probability mode"
  , testCase "the decline is not the found-no-way-to-convert crash" $
      -- Pins the *manner* of the refusal as well as its existence: this string
      -- is the IRCompiler catch-all, i.e. the bug itself.
      withParsed intractableComparisonSrc $ \prog -> do
        res <- forcedProb prog (VBool True)
        assertBool "the IRCompiler catch-all fired instead of a typing verdict"
                   (not ("found no way to convert to IR" `isInfixOf` show res))
  , testCase "the Gaussian-difference comparison is still accepted" $
      withParsed gaussianComparisonSrc $ \prog -> do
        res <- forcedProb prog (VBool True)
        case res of
          Left ex        -> assertFailure ("the closed-form comparison crashed: " ++ show ex)
          Right (Left e) -> assertFailure ("the closed-form comparison was refused: " ++ e)
          Right (Right _) -> return ()
  ]
