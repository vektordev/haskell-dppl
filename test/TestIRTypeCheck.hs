module TestIRTypeCheck (irTypeCheckTests) where

-- That the IR type checker ('SPLL.IRTypeCheck') accepts what the compiler
-- emits. The checker's own constructs, builtins, rejections and environment
-- rules are tested in the nest-ir package (nest-ir/test/TestIRTypeCheck.hs).

import SPLL.CompilerConfig
import SPLL.IRTypeCheck
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile)
import SPLL.IR.Neural (oracleSignatures)
import MockNN (programMockOracle)
import SPLL.Examples (testDiceAdd, testRecursion, testThetaTree, testLetIn, testCallLambdaAdvanced, gaussLists, testNN)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

irTypeCheckTests :: TestTree
irTypeCheckTests = testGroup "IRTypeCheck"
  [ compilerOutputTests
  ]

-- | Programs the compiler compiles today must check: the checker is a
-- contract the compiler's output already meets. A small spread rather than
-- the corpus (see the task document for the corpus survey).
compilerOutputTests :: TestTree
compilerOutputTests = testGroup "compiler output"
  ([ accepts name p | (name, p) <-
      [ ("testDiceAdd", testDiceAdd), ("testRecursion", testRecursion), ("testThetaTree", testThetaTree)
      , ("testLetIn", testLetIn), ("testCallLambdaAdvanced", testCallLambdaAdvanced)
      , ("gaussLists", gaussLists), ("testNN", testNN) ] ]
   ++ [ acceptsSource name src | (name, src) <- sources ])
  where
    accepts name p = testCase name $ case compile defaultCompilerConfig p of
      Left err -> assertFailure ("does not compile: " ++ show err)
      Right env -> case checkIREnvWith (oracleSignatures (programMockOracle p)) env of
        Left err -> assertFailure (showIRTypeError err)
        Right _ -> return ()
    acceptsSource name src = case tryParseProgram name src of
      Left _ -> testCase name (assertFailure "does not parse")
      Right p -> accepts name p
    sources =
      [ ("enumerated sum over an ADT", unlines
          [ "data Mix = Zero | Two ma::Int, mb::Bool"
          , "main = draw v0 = (if Uniform < 0.5 then Zero else Two 1 False) in (if isTwo v0 then mb v0 else False)" ])
      , ("Either and tuples", unlines
          [ "main = draw e = if Uniform < 0.5 then left Normal else right 0.0 in if isLeft e then (fromLeft e, 1) else (fromRight e, 2)" ])
      , ("a list built by recursion", unlines
          [ "build n = if n == 0 then [] else (Uniform < 0.5) : build (n - 1)"
          , "main = build 3" ])
      , ("a polymorphic helper at two types", unlines
          [ "addTwice x = x + x"
          , "main = (addTwice Normal, addTwice (if Uniform < 0.5 then 1 else 2))" ])
      ]
