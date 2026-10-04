-- | Small compile/query helpers shared between 'Spec.hs' (the main test
-- suite) and 'TestCorpus' (the Corpus group, split into its own test-suite
-- process -- see the module haddock on 'TestCorpus' for why).
module TestSupport
  ( topKConf
  , topKBCConf
  , bcConf
  , irDensity
  , reasonablyClose
  , expectCompiled
  , refusalReasons
  , expectVariantRefused
  ) where

import Test.QuickCheck
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Prelude (runProb)
import TestTolerances (reasonablyCloseTolerance)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure)
import Data.List (isInfixOf, intercalate)

topKConf :: Double -> CompilerConfig
topKConf thresh = defaultCompilerConfig {topKThreshold = Just thresh}

topKBCConf :: Double -> CompilerConfig
topKBCConf thresh = (topKConf thresh) {countBranches = True}

bcConf :: CompilerConfig
bcConf = defaultCompilerConfig {countBranches = True}

irDensity :: CompilerConfig -> Program -> IRValue -> [IRValue] -> IRValue
irDensity conf p s params = either error id $ runProb conf p params s

reasonablyClose :: IRValue -> IRValue -> Property
reasonablyClose (VFloat a) (VFloat b) = counterexample (show a ++ "/=" ++ show b) (property $ abs (a - b) <= reasonablyCloseTolerance)
reasonablyClose a b = a === b

-- | A compile the test asserts must succeed. Failing here is a broken fixture,
-- so surface the compiler's own message instead of a pattern-match panic.
expectCompiled :: Either CompilerError IREnv -> IREnv
expectCompiled (Right env) = env
expectCompiled (Left err)  = error ("test fixture failed to compile: " ++ show err)

-- | Every variant the IR compiler refused, as @group.variant: reason@ (task
-- static-refusals-become-absent-variants: a refused shape is an absent variant
-- with a recorded reason, not an exception).
refusalReasons :: IREnv -> [String]
refusalReasons (IREnv gs _ _) =
  [ groupName g ++ "." ++ lbl ++ ": " ++ showRefusal r | g <- gs, (lbl, r) <- refusedVariants g ]

-- | Assert that compiling succeeded with the given variant (@"prob"@,
-- @"integ"@, ...) of the given group refused, its recorded reason containing
-- the needle.
expectVariantRefused :: String -> String -> String -> Either CompilerError IREnv -> Assertion
expectVariantRefused grp lbl needle compiled = case compiled of
  Left err -> assertFailure ("expected " ++ grp ++ "." ++ lbl ++ " to be refused, but the whole compile was: " ++ err)
  Right env@(IREnv gs _ _) -> case [ r | g <- gs, groupName g == grp, Just r <- [lookup lbl (refusedVariants g)] ] of
    [] -> assertFailure ("expected " ++ grp ++ "." ++ lbl ++ " to be refused; recorded refusals: "
                         ++ (if null (refusalReasons env) then "(none)" else intercalate "\n" (refusalReasons env)))
    (r : _) -> assertBool ("expected the refusal of " ++ grp ++ "." ++ lbl ++ " to mention " ++ show needle
                           ++ ", got: " ++ showRefusal r)
                 (needle `isInfixOf` showRefusal r)
