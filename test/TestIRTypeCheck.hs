module TestIRTypeCheck (irTypeCheckTests) where

-- The IR type checker ('SPLL.IRTypeCheck', docs-repo task
-- ir-fuzz-generator-m0-ir-type-checker): what each construct is typed as,
-- what is rejected and why, the environment-level rules (generalisation per
-- call-graph component, the standard library, ADT functions, externals), and
-- that the checker accepts real compiler output.

import SPLL.IntermediateRepresentation
import SPLL.IRTypeCheck
import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..))
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile)
import SPLL.Examples (testDiceAdd, testRecursion, testThetaTree, testLetIn, testCallLambdaAdvanced, gaussLists, testNN)

import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure, Assertion)

irTypeCheckTests :: TestTree
irTypeCheckTests = testGroup "IRTypeCheck"
  [ constructTests
  , builtinTests
  , rejectionTests
  , environmentTests
  , compilerOutputTests
  ]

-- | The type of a closed expression, printed.
typeOf :: IRExpr -> Either String String
typeOf e = either (Left . showIRTypeError) (Right . showIRType) (inferIRExpr [] [] e)

hasType :: String -> IRExpr -> Assertion
hasType expected e = case typeOf e of
  Right t -> assertEqual (show e) expected t
  Left err -> assertFailure ("rejected, expected " ++ expected ++ ":\n" ++ err)

-- | Rejected, with a message containing the given text.
rejects :: String -> IRExpr -> Assertion
rejects needle e = case typeOf e of
  Right t -> assertFailure ("accepted at " ++ t ++ ", expected a rejection: " ++ show e)
  Left err | needle `isInfixOf` err -> return ()
           | otherwise -> assertFailure ("rejected for another reason than " ++ show needle ++ ":\n" ++ err)

f :: Double -> IRExpr
f = IRConst . VFloat

i :: Int -> IRExpr
i = IRConst . VInt

b :: Bool -> IRExpr
b = IRConst . VBool

v :: String -> IRExpr
v = IRVar

tensor :: [Int] -> [IRExpr] -> IRExpr
tensor sh = IRBuiltin (BTensor (map EFixed sh))

constructTests :: TestTree
constructTests = testGroup "constructs"
  [ testCase "arithmetic is typed at its operands" $ do
      hasType "Float" (IROp OpPlus (f 1) (f 2))
      hasType "Int" (IROp OpMult (i 1) (i 2))
      hasType "Int" (IROp OpMod (i 7) (i 2))
      hasType "Float" (IROp OpDiv (f 1) (f 2))
      hasType "Bool" (IROp OpLessThan (IRConstruct TgTuple [f 1, i 2]) (IRConstruct TgTuple [f 0, i 3]))
      hasType "Bool" (IROp OpApprox (f 1) (f 1))
  , testCase "a lambda's parameter is inferred from its use" $ do
      hasType "Float -> Float" (IRLambda "x" (IROp OpPlus (v "x") (f 1)))
      hasType "a -> a" (IRLambda "x" (v "x"))
      hasType "a -> b -> a" (IRLambda "x" (IRLambda "y" (v "x")))
  , testCase "an operand of undetermined type keeps its constraint" $
      -- Numeric, but neither Float nor Int yet: the constraint is pending, not rejected.
      hasType "a -> a" (IRLambda "x" (IROp OpPlus (v "x") (v "x")))
  , testCase "if, let and application" $ do
      hasType "Int" (IRIf (b True) (i 1) (i 2))
      hasType "Int" (IRSelect (b True) (i 1) (i 2))
      hasType "Float" (IRLetIn "x" (IRSample IRNormal) (IROp OpMult (v "x") (v "x")))
      hasType "Bool" (IRApply (IRLambda "x" (IRUnaryOp OpNot (v "x"))) (b False))
  , testCase "the PResult layout is an ordinary nested tuple" $
      hasType "(Float, (Int, Bool))"
        (IRConstruct TgTuple [IRDensity IRNormal Log (f 0), IRConstruct TgTuple [i 0, b False]])
  , testCase "data constructors and their accessors" $ do
      hasType "[Int]" (IRConstruct TgCons [i 1, IRConst (VList EmptyList)])
      hasType "Int" (IRDestruct AcHead (IRConstruct TgCons [i 1, IRConst (VList EmptyList)]))
      hasType "Either Float a" (IRConstruct TgLeft [f 1])
      hasType "Float" (IRDestruct AcFromRight (IRConstruct TgRight [f 1]))
      hasType "Bool" (IRDestruct AcIsLeft (IRConstruct TgRight [f 1]))
      hasType "Int" (IRDestruct AcSnd (IRConstruct TgTuple [f 1, i 2]))
      hasType "Float" (IRDestruct (AcTheta 0) (IRConst (VThetaTree (ThetaTree [0.5] []))))
      hasType "ThetaTree" (IRDestruct (AcSubtree 0) (IRConst (VThetaTree (ThetaTree [] []))))
  , testCase "a marginal hole and an error have any type" $ do
      hasType "Float" (IRIf (b True) (IRConst VAny) (f 1))
      hasType "[Int]" (IRIf (b True) (IRConst (VList AnyList)) (IRConst (VList (ListCont (VInt 1) EmptyList))))
      hasType "Int" (IRIf (b True) (IRError "boom") (i 1))
  , testCase "unary operators" $ do
      hasType "Int" (IRUnaryOp OpNeg (i 1))
      hasType "Float" (IRUnaryOp OpLog (f 1))
      hasType "Bool" (IRUnaryOp OpIsAny (IRConstruct TgTuple [f 1, i 2]))
      hasType "Bool" (IRConformsTo TFloat (b True))
  , testCase "a closure value is typed from its body and environment" $
      hasType "Float -> Float"
        (IRConst (VClosure [("k", IRConst (VFloat 2))] "x" (IROp OpMult (IRVar "k") (IRVar "x"))))
  ]

builtinTests :: TestTree
builtinTests = testGroup "builtins"
  [ testCase "an enumerated sum: reduce of a map over a tensor" $
      hasType "Float"
        (IRBuiltin (BReduce ROpAdd 0)
          [IRBuiltin BMap [IRLambda "x" (IRDensity IRNormal Linear (v "x")), tensor [3] [f 0, f 1, f 2]]])
  , testCase "a tensor's elements may be structured" $
      hasType "Tensor[2] (Either Int Bool)"
        (tensor [2] [IRConstruct TgLeft [i 1], IRConstruct TgRight [b True]])
  , testCase "reducing or indexing one axis of a rank-2 tensor leaves rank 1" $ do
      let t = tensor [2, 3] (map f [1 .. 6])
      hasType "Tensor[3] Float" (IRBuiltin (BReduce ROpLogSumExp 0) [t])
      hasType "Tensor[2] Float" (IRBuiltin (BIndex 1) [t, i 0])
      hasType "Float" (IRBuiltin (BIndex 0) [IRBuiltin (BIndex 0) [t, i 1], i 2])
  , testCase "zip applies its operator's rule elementwise" $ do
      let t = tensor [2] [f 1, f 2]
      hasType "Tensor[2] Float" (IRBuiltin (BZip OpMult) [t, t])
      hasType "Tensor[2] Bool" (IRBuiltin (BZip OpLessThan) [t, t])
  , testCase "a tensor's shape reaches a builtin through a lambda" $
      hasType "Float"
        (IRApply (IRLambda "t" (IRBuiltin (BReduce ROpMax 0) [v "t"])) (tensor [2] [f 1, f 2]))
  , testCase "list builtins" $ do
      let xs = IRConst (VList (ListCont (VFloat 1) (ListCont (VFloat 2) EmptyList)))
      hasType "[Bool]" (IRBuiltin BMapList [IRLambda "x" (IROp OpGreaterThan (v "x") (f 0)), xs])
      hasType "Float" (IRBuiltin BListIndex [xs, i 1])
      hasType "Int" (IRBuiltin (BCategoricalIndex 0 2) [IRSample IRUniform, xs])
      hasType "Int" (IRBuiltin (BCategoricalIndex 1 1) [IRSample IRUniform, tensor [2] [f 1, f 2]])
  ]

rejectionTests :: TestTree
rejectionTests = testGroup "rejections"
  [ testCase "operand types" $ do
      rejects "cannot match" (IROp OpPlus (f 1) (i 1))
      rejects "expected a number" (IROp OpPlus (b True) (b False))
      rejects "cannot match Int with Float" (IROp OpDiv (i 1) (i 2))
      rejects "expected an ordered type" (IROp OpLessThan (b True) (b False))
      rejects "expected a type with equality" (IROp OpEq (IRLambda "x" (v "x")) (IRLambda "y" (v "y")))
      rejects "expected a type with equality" (IROp OpEq (tensor [1] [f 1]) (tensor [1] [f 1]))
      rejects "cannot match" (IRUnaryOp OpNot (f 1))
      rejects "expected a number" (IRUnaryOp OpAbs (b True))
  , testCase "a condition is a Bool and both arms agree" $ do
      rejects "cannot match" (IRIf (i 1) (f 1) (f 2))
      rejects "cannot match" (IRIf (b True) (f 1) (i 2))
  , testCase "scope" $ do
      rejects "unbound variable y" (IRLambda "x" (v "y"))
      rejects "unbound variable x" (IRLetIn "y" (v "x") (f 1))
  , testCase "a projection needs its structure" $ do
      rejects "cannot match" (IRDestruct AcFst (f 1))
      rejects "cannot match" (IRDestruct AcHead (IRConstruct TgTuple [f 1, f 1]))
      rejects "cannot match" (IRDestruct (AcTheta 0) (f 1))
      -- The interpreter pushes fst through a closure; the contract does not.
      rejects "cannot match" (IRDestruct AcFst (IRLambda "x" (IRConstruct TgTuple [v "x", v "x"])))
  , testCase "application" $ do
      rejects "cannot match" (IRApply (f 1) (f 2))
      rejects "infinite type" (IRLambda "x" (IRApply (v "x") (v "x")))
  , testCase "arity of constructs and builtins" $ do
      rejects "takes 2 arguments, got 1" (IRConstruct TgTuple [f 1])
      rejects "takes 2 arguments, got 3" (IRBuiltin BListIndex [f 1, f 2, f 3])
      rejects "takes 3 elements, got 2" (tensor [3] [f 1, f 2])
      rejects "rank at least 1" (tensor [] [f 1])
  , testCase "tensor builtins" $ do
      rejects "expected a tensor" (IRBuiltin (BReduce ROpAdd 0) [f 1])
      rejects "cannot match Bool with Float" (IRBuiltin (BReduce ROpAdd 0) [tensor [1] [b True]])
      rejects "out of range" (IRBuiltin (BReduce ROpAdd 1) [tensor [2] [f 1, f 2]])
      rejects "cannot match" (IRBuiltin (BIndex 0) [tensor [2] [f 1, f 2], f 0])
      rejects "cannot match" (IRBuiltin (BZip OpPlus) [tensor [2] [f 1, f 2], tensor [3] [f 1, f 2, f 3]])
      rejects "cannot match" (IRBuiltin (BZip OpAnd) [tensor [1] [f 1], tensor [1] [f 1]])
      rejects "cannot match" (IRBuiltin BMap [IRLambda "x" (IRUnaryOp OpNot (v "x")), tensor [1] [f 1]])
      rejects "expected a list or rank-1 tensor" (IRBuiltin (BCategoricalIndex 0 1) [f 0.5, f 1])
      rejects "expected a list or rank-1 tensor" (IRBuiltin (BCategoricalIndex 0 1) [f 0.5, tensor [1, 1] [f 1]])
  , testCase "a constraint deferred on a parameter is checked once the argument arrives" $ do
      rejects "expected a number" (IRApply (IRLambda "x" (IROp OpPlus (v "x") (v "x"))) (b True))
      rejects "expected a tensor" (IRApply (IRLambda "t" (IRBuiltin (BReduce ROpAdd 0) [v "t"])) (f 1))
  , testCase "constant values" $ do
      rejects "cannot match" (IRConst (VList (ListCont (VFloat 1) (ListCont (VInt 1) EmptyList))))
      rejects "holds 1 elements" (IRConst (VTensor [EFixed 2] [VFloat 1]))
      rejects "unknown ADT constructor" (IRConst (VADT "Nope" []))
  ]

-- | A one-function-per-group environment of probability-variant bodies
-- (bound as @name_prob@).
envOf :: [ADTDecl] -> [(String, IRExpr)] -> IREnv
envOf decls fns = IREnv [ group n e | (n, e) <- fns ] decls []
  where group n e = IRFunGroup { groupName = n, genFun = Nothing, probFun = Just (e, ""), integFun = Nothing
                               , writeLogitsFun = Nothing, normalFun = Nothing, groupDoc = ""
                               , refusedVariants = [], sampleDomain = Nothing, maskVariantOf = Nothing }

envTypes :: [(String, IRType)] -> IREnv -> Either String [(String, String)]
envTypes ext env = either (Left . showIRTypeError) (Right . map (fmap showIRType)) (checkIREnvWith ext env)

shapeDecl :: ADTDecl
shapeDecl = ADTDecl { dataName = "Shape"
                    , constructors = [("Circle", [("radius", TFloat)]), ("Square", [("side", TFloat)])]
                    , adtDepth = Nothing }

environmentTests :: TestTree
environmentTests = testGroup "environments"
  [ testCase "a helper is generalised before its callers, so it serves two types" $
      assertEqual "types"
        (Right [("ident_prob", "a -> a"), ("main_prob", "(Float, Int)")])
        (envTypes [] (envOf [] [ ("ident", IRLambda "x" (v "x"))
                              , ("main", IRConstruct TgTuple [IRApply (v "ident_prob") (f 1), IRApply (v "ident_prob") (i 1)]) ]))
  , testCase "a generalised helper's pending constraint is re-checked at every use" $ do
      let double = ("double", IRLambda "x" (IROp OpPlus (v "x") (v "x")))
      assertEqual "used at Float and Int"
        (Right [("double_prob", "a -> a"), ("main_prob", "(Float, Int)")])
        (envTypes [] (envOf [] [double, ("main", IRConstruct TgTuple [IRApply (v "double_prob") (f 1), IRApply (v "double_prob") (i 1)])]))
      case envTypes [] (envOf [] [double, ("main", IRApply (v "double_prob") (b True))]) of
        Left err | "expected a number" `isInfixOf` err && "main_prob" `isInfixOf` err -> return ()
        other -> assertFailure ("expected main_prob to be rejected, got " ++ show other)
  , testCase "mutual recursion is one component, checked monomorphically" $
      assertEqual "types"
        (Right [("even_prob", "Int -> Bool"), ("odd_prob", "Int -> Bool")])
        (envTypes [] (envOf []
          [ ("even", IRLambda "n" (IRIf (IROp OpEq (v "n") (i 0)) (b True) (IRApply (v "odd_prob") (IROp OpSub (v "n") (i 1)))))
          , ("odd", IRLambda "n" (IRIf (IROp OpEq (v "n") (i 0)) (b False) (IRApply (v "even_prob") (IROp OpSub (v "n") (i 1))))) ]))
  , testCase "the standard library is polymorphic" $
      assertEqual "types"
        (Right [("main_prob", "(Int, Int)")])
        (envTypes [] (envOf [] [("main", IRConstruct TgTuple
            [ IRApply (IRApply (v "indexOf") (f 1)) (IRConst (VList (ListCont (VFloat 1) EmptyList)))
            , IRApply (IRApply (v "indexOf") (b True)) (IRConst (VList (ListCont (VBool True) EmptyList))) ])]))
  , testCase "ADT constructors, tests and accessors come from the declaration" $ do
      assertEqual "types"
        (Right [("main_prob", "(Shape, (Bool, Float))")])
        (envTypes [] (envOf [shapeDecl] [("main", IRLetIn "s" (IRApply (v "Circle") (f 1))
            (IRConstruct TgTuple [v "s", IRConstruct TgTuple [IRApply (v "isSquare") (v "s"), IRApply (v "radius") (v "s")]]))]))
      assertEqual "an ADT value" (Right [("main_prob", "Shape")])
        (envTypes [] (envOf [shapeDecl] [("main", IRConst (VADT "Square" [VFloat 2]))]))
      case envTypes [] (envOf [shapeDecl] [("main", IRConst (VADT "Square" [VBool True]))]) of
        Left err | "cannot match" `isInfixOf` err -> return ()
        other -> assertFailure ("expected a field mismatch, got " ++ show other)
  , testCase "an external, such as a network, is a global of the given type" $ do
      let ext = [("net", ITArrow ITFloat (ITList ITFloat))]
      assertEqual "types" (Right [("main_prob", "Float")])
        (envTypes ext (envOf [] [("main", IRBuiltin BListIndex [IRApply (v "net") (f 0), i 0])]))
      case envTypes [] (envOf [] [("main", IRApply (v "net") (f 0))]) of
        Left err | "unbound variable net" `isInfixOf` err -> return ()
        other -> assertFailure ("expected net to be unbound without the external, got " ++ show other)
  , testCase "compile-time constants are bindings" $
      assertEqual "types" (Right [("TOP_K_CUTOFF", "Float"), ("main_prob", "Float")])
        (envTypes [] (IREnv [] [] [("TOP_K_CUTOFF", VFloat 0.1)] `withGroups` envOf [] [("main", v "TOP_K_CUTOFF")]))
  ]
  where withGroups (IREnv _ d c) (IREnv g _ _) = IREnv g d c

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
      Right env -> case checkIREnvWith (neuralExternals (neurals p)) env of
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
