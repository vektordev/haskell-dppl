module SPLL.Examples
  ( simpleList
  , simpleAdd
  , uniformProg
  , normalProg
  , uniformProgMult
  , normalProgMult
  , uniformProgPlus
  , uniformNegPlus
  , uniformIfProg
  , uniformExp
  , testList
  , simpleTuple
  , constantProg
  , simpleCall
  , testInjF
  , testInjFPlusLeft
  , testInjFPlusRight
  , testInjF2
  , testPlus3
  , testTopK
  , testTheta
  , testThetaTree
  , testAnd
  , testOr
  , testNot
  , testCallLambda
  , testCallLambdaAdvanced
  , testLambdaParameter
  , testLetIn
  , testRecursion
  , testNN
  , testDimProb
  , normalProgMultPlus
  , testCallArg
  , gaussLists
  , testTopLevelLambda
  , testDim
  , testCoin
  , testDice
  , testDiceAdd
  , testFibonacci
  , testPartialInjF
  , testInjFRenaming
  , testLambdaChoice
  , testConditionalLambdaBC
  , testNormalShiftedViaVar
  , testNormalScaledViaVar
  , testAutoNeural
  , invalidMissingDecl
  , invalidMissingInjF
  , invalidWrongArgCount
  , invalidDuplicateDecl1
  , invalidDuplicateDecl2
  , invalidDuplicateDecl3
  , invalidDuplicateDecl4
  , invalidDuplicateDecl5
  , invalidReservedName
  , invalidReservedName2
  , testLeft
  , testEither
  , testIsLeft
  , testIsRight
  , testFst
  , testHead
  , testTail
  , testFstCall
  , testFstDiscrete
  ) where

import SPLL.Lang.Lang

import SPLL.Typing.RType
import SPLL.Typing.Typing ()
import SPLL.Lang.Types
import SPLL.Prelude

simpleList :: Program
simpleList = Program [("main", constF 0.0 #:# nul)] [] []

simpleAdd :: Program
simpleAdd = Program [("main", constF 0.0 #+# constF 1.0)] [] []

uniformProg :: Program
uniformProg = Program [("main", uniform)] [] []

normalProg :: Program
normalProg = Program [("main", normal)] [] []

uniformProgMult :: Program
uniformProgMult = Program [("main", uniform #*# constF (-0.5))] [] []

normalProgMult :: Program
normalProgMult = Program [("main", normal #*# constF 0.5)] [] []

uniformProgPlus :: Program
uniformProgPlus = Program [("main", uniform #+# constF 4)] [] []

normalProgMultPlus :: Program
normalProgMultPlus = Program [("main", normal #*# constF 2 #+# constF 1)] [] []


uniformNegPlus :: Program
uniformNegPlus = Program [("main", negF (uniform #+#constF 4))] [] []

uniformIfProg :: Program
uniformIfProg = Program [("main", ifThenElse (GreaterThan makeTypeInfo uniform (constF 0.5))
                             uniform
                             (uniform #+# constF 5))] [] []

uniformExp :: Program
uniformExp = Program [("main", injF "exp" [uniform #+# constF 4])] [] []

testMultLeft :: Expr
testMultLeft = constF 3.0 #*# normal

testList :: Program
testList = Program [("main", (constF 0.5 #*# uniform) #:# (normal #:# nul))] [] []

simpleTuple :: Program
simpleTuple = Program [("main", tuple (constF 0.5 #*# uniform) normal)] [] []

constantProg :: Program
constantProg = Program [("main", constF 2)] [] []

simpleCall :: Program
simpleCall = Program [("unif", uniform), ("main", var "unif")] [] []

testCallArg :: Program
testCallArg = Program [("unif", "x" #-># (var "x" #+# uniform)), ("main", apply (var "unif") (constF 3))] [] []

testNeg :: Expr
testNeg = negF uniform

testNegFail :: Expr
testNegFail = negF (uniform #+# uniform)

testInjF :: Program
testInjF = Program [("main", injF "double" [uniform])] [] []

testInjFPlusLeft :: Program
testInjFPlusLeft = Program [("main", injF "plus" [constF 1, uniform])] [] []

testInjFPlusRight :: Program
testInjFPlusRight = Program [("main", injF "plus" [uniform, constF 1])] [] []

testInjF2 :: Program
testInjF2 = Program [("main", injF "double" [injF "plus" [constF 1, uniform]])] [] []

testPlus3 :: Program
testPlus3 = Program [("main", letIn "a" uniform (var "a" #+# var "a"))] [] []

testTopK :: Program
testTopK = Program [("main", ifThenElse (bernoulli 0.95) (constF 1) (constF 0))] [] []

testTheta :: Program
testTheta = Program [("main", "thetas" #-># theta (var "thetas") 0)] [] []

testThetaTree :: Program
testThetaTree = Program [("main", "thetas" #-># (theta (var "thetas") 2 #+# theta (Subtree makeTypeInfo (var "thetas") 1) 1))] [] []

testAnd :: Program
testAnd = Program [("main", (normal #<# constF 0) #&&# (uniform #># constF 0.5))] [] []

testOr :: Program
testOr = Program [("main", (normal #># constF 0) #||# (uniform #># constF 0.5))] [] []

testNot :: Program
testNot = Program [("main", (#!#) (uniform #<# constF 0.75))] [] []

testCallLambda :: Program
testCallLambda = Program [("main", apply ("x" #-># (var "x" #+# uniform)) (constF 2))] [] []

testCallLambdaAdvanced :: Program
testCallLambdaAdvanced = Program [("main", letIn "l" ("a" #-># (var "a" #+# uniform)) (apply (var "l") (constF 2)))] [] []

testLambdaParameter :: Program
testLambdaParameter = Program [("main", apply (var "other") ("x" #-># (var "x" #*# constF 2)) ), ("other", "f" #-># apply (var "f") (constF 5))] [] []

testLetIn :: Program
testLetIn = Program [("main", letIn "u" uniform (var "u" #+# constF 1))] [] []

testRecursion :: Program
testRecursion = Program [("main", apply (var "rec") (constF 8)),
                         ("rec", "x" #-># ifThenElse (var "x" #># constF 1) (constF 3 #*# apply (var "rec") (var "x" #*# constF 0.5)) uniform)] [] []

testNN :: Program
testNN = Program [("main", mNistAddExpr)] [("classifyMNist", TArrow TSymbol TInt, Just (MultiDiscretes (map VInt [0..9])))] []

testDimProb :: Program
testDimProb = Program [("main", IfThenElse makeTypeInfo (LessThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.4))) (Constant makeTypeInfo $ VFloat 0.5) (Normal makeTypeInfo))] [] []


mNistAddExpr :: Expr
mNistAddExpr = "im1" #-># ("im2" #-># (ReadNN makeTypeInfo "classifyMNist" (var "im1") #+# ReadNN makeTypeInfo "classifyMNist" (var "im2")))

gaussLists :: Program
gaussLists = Program [("main", "thetas" #->#
  ifThenElse
    (uniform #># theta (var "thetas") 0)
    nul
    (((normal #*# theta (var "thetas") 1) #+# theta (var "thetas") 2) #:#
      apply (var "main") (var "thetas")))] [] []

testTopLevelLambda :: Program
testTopLevelLambda = Program [("main", "a" #-># (var "a" #+# uniform))] [] []

testDim :: Program
testDim = Program [("main", ifThenElse (bernoulli 0.5) (uniform #*# constF 2) (constF 3))] [] []

testCoin :: Program
testCoin = Program [("main", ifThenElse (bernoulli 0.5) (constI 1) (constI 2))] [] []

testDice :: Program
testDice = Program [("main", dice 6)] [] []

testDiceAdd :: Program
testDiceAdd = Program [ ("main", injF "plusI" [var "dice", var "dice"]),
                        ("dice", dice 6)] [] []

-- Not working
testFibonacci :: Program
testFibonacci = Program [ ("main","idx" #-># apply (apply fix (var "fibonacci")) (var "idx")),
                          ("fibonacci", "fib" #-># ("n" #-># ifThenElse (var "n" #<# constF 2) (var "n") (apply (var "fib") (var "n" #-# constF 1) #+# apply (var "fib") (var "n" #-# constF 2))) )] [] []

testPartialInjF :: Program
testPartialInjF = Program [("main", apply (injF "plus" [uniform]) (constF 5))] [] []

testInjFRenaming :: Program
testInjFRenaming = Program [("main", apply ("a" #-># (var "a" #+# uniform)) (constF 5))] [] []

testLambdaChoice :: Program
testLambdaChoice = Program [("main", apply (ifThenElse (bernoulli 0.5) ("x" #-># (normal #+# var "x")) ("y" #-># (uniform #+# var "y"))) (constF 1))] [] []

-- Deterministic conditional function applied to a discrete float argument.
-- Triggers the IsConditional + toIREnumerate path in IRCompiler.
-- The argument is a coin flip between 1.0 and 2.0 (2 discrete float values).
-- selector maps the outcome: x>1.5 → 1.0, otherwise → 0.0.
-- 2 discrete values, each iteration contributes bc=1 → expected BC = 2.
testConditionalLambdaBC :: Program
testConditionalLambdaBC = Program
  [ ("main",     apply (var "selector") (ifThenElse (bernoulli 0.5) (constF 2.0) (constF 1.0)))
  , ("selector", "x" #-># ifThenElse (var "x" #># constF 1.5) (constF 1.0) (constF 0.0))
  ] [] []

-- Program that calls a named sub-function via Var with a continuous distribution.
-- With countBranches=False, stripBranchCount must correctly rewrite the dim-extraction
-- from the sub-function's result variable (killAll IRVar path).
-- P(main = 5.0) = normalPDF(5.0 - 5.0) = normalPDF(0.0).
testNormalShiftedViaVar :: Program
testNormalShiftedViaVar = Program
  [ ("main", injF "plus" [var "base", constF 5.0])
  , ("base", normal)
  ] [] []

-- Like testNormalShiftedViaVar but uses mult so the change-of-variables correction
-- is 1/2 rather than 1.  If killAll fails to correctly rewrite dim extraction from
-- the sub-function result, dim will be 0 and the CoV factor won't be applied,
-- yielding normalPDF(x/2) instead of the correct normalPDF(x/2) * 0.5.
-- P(main = 2.0) = normalPDF(1.0) * 0.5.
testNormalScaledViaVar :: Program
testNormalScaledViaVar = Program
  [ ("main", injF "mult" [var "base", constF 2.0])
  , ("base", normal)
  ] [] []

testAutoNeural :: Program
testAutoNeural = Program [("main", "sym" #-># ReadNN makeTypeInfo "readMNist" (var "sym"))] [("readMNist", TArrow TSymbol TInt, Just (MultiDiscretes (map VInt [0..9])))] []


-- ======================================= INVALID PROGRAMS ============================================

invalidMissingDecl :: Program
invalidMissingDecl = Program [("main", var "x")] [] []

invalidMissingInjF :: Program
invalidMissingInjF = Program [("main", injF "x" [])] [] []

invalidWrongArgCount :: Program
invalidWrongArgCount = Program [("main", injF "plus" [uniform])] [] []

invalidDuplicateDecl1 :: Program
invalidDuplicateDecl1 = Program [("main", letIn "x" (letIn "x" uniform uniform) uniform)] [] []

invalidDuplicateDecl2 :: Program
invalidDuplicateDecl2 = Program [("main", letIn "x" uniform (letIn "x" uniform uniform))] [] []

invalidDuplicateDecl3 :: Program
invalidDuplicateDecl3 = Program [("main", letIn "x" uniform (var "x")), ("x", uniform)] [] []

invalidDuplicateDecl4 :: Program
invalidDuplicateDecl4 = Program [("main", "x" #-># ("x" #-># uniform))] [] []

invalidDuplicateDecl5 :: Program
invalidDuplicateDecl5 = Program [("main", "x" #-># (var "x")), ("x", uniform)] [] []

invalidReservedName :: Program
invalidReservedName = Program [("main", letIn "plus" uniform uniform)] [] []

invalidReservedName2 :: Program
invalidReservedName2 = Program [("main", "plus" #-># uniform)] [] []


testLeft :: Program
testLeft = Program [("main", injF "fromLeft" [injF "left" [constF 2]])] [] []

testEither :: Program
testEither = Program [("main", ifThenElse (bernoulli 0.5) (injF "left" [uniform]) (injF "right" [constI 1]))] [] []

testIsLeft :: Program
testIsLeft = Program [("main", ifThenElse (injF "isLeft" [ifThenElse (bernoulli 0.4) (injF "left" [uniform]) (injF "right" [constI 1])])
                                  (constF 1)
                                  (constF 2))] [] []

testIsRight :: Program
testIsRight = Program [("main", ifThenElse (injF "isRight" [ifThenElse (bernoulli 0.4) (injF "left" [uniform]) (injF "right" [constI 1])])
                                  (constF 1)
                                  (constF 2))] [] []

testFst :: Program
testFst = Program [("main", tfst (tuple uniform normal))] [] []

testHead :: Program
testHead = Program [("main", lhead (cons uniform nul))] [] []

testTail :: Program
testTail = Program [("main", lhead (ltail (cons normal (cons uniform nul))))] [] []

testFstCall :: Program
testFstCall = Program [("main", tfst (var "bivariate")), ("bivariate", tuple uniform normal)] [] []

testFstDiscrete :: Program
testFstDiscrete = Program [("main", tfst (tuple uniform  (bernoulli 0.4)))] [] []
