module SPLL.Examples where

import SPLL.Lang.Lang

import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing (TypeInfo, makeTypeInfo)
import SPLL.Lang.Types
import SPLL.Prelude
import SPLL.Lang.Types (Program(Program))

--weatherHask lastDay = if lastDay == rainy
--  then let current = randA in (current, weatherHask current)
--  else let current = randB in (current, weatherHask current)

--gaussLists :: Expr
--gaussLists = ifThenElse
--  (GreaterThan makeTypeInfo uniform (theta 0))
--  (Null makeTypeInfo)
--  (Cons makeTypeInfo (PlusF makeTypeInfo (MultF makeTypeInfo normal (theta 1)) (theta 2)) (Call makeTypeInfo "main"))

exampleList :: [(String, Program)]
exampleList = [
              ("simpleList", simpleList),
              ("simpleAdd", simpleAdd),
              ("uniformProg", uniformProg),
              ("normalProg", normalProg),
              ("uniformProgMult", uniformProgMult),
              ("normalProgMult", normalProgMult),
              ("uniformProgPlus", uniformProgPlus),
              ("uniformNegPlus", uniformNegPlus),
              ("uniformIfProg", uniformIfProg),
              ("uniformExp", uniformExp),
              ("testList", testList),
              ("simpleTuple", simpleTuple),
              ("constantProg", constantProg),
              ("simpleCall", simpleCall),
              ("testInjF", testInjF),
              ("testInjFPlusLeft", testInjFPlusLeft),
              ("testInjFPlusRight", testInjFPlusRight),
              ("testInjF2", testInjF2),
              ("testPlus3", testPlus3),
              ("testTopK", testTopK),
              ("testTheta", testTheta),
              ("testThetaTree", testThetaTree),
              ("testAnd", testAnd),
              ("testOr", testOr),
              ("testNot", testNot),
              ("testCallLambda", testCallLambda),
              ("testCallLambdaAdvanced", testCallLambdaAdvanced),
              ("testLambdaParameter", testLambdaParameter),
              ("testLetIn", testLetIn),
              ("testRecursion", testRecursion),
              ("gaussLists", gaussLists),
              ("testTopLevelLambda", testTopLevelLambda),
              ("testDim", testDim),
              ("testCoin", testCoin),
              ("testDice", testDice)
              ]

paramExpr :: Expr
paramExpr = Arg makeTypeInfo "iterations" TFloat (ifThenElse
  (GreaterThan makeTypeInfo (var "iterations") (constF 0.5))
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (apply (var "main") (PlusF makeTypeInfo (var "iterations") (constF (-1.0)))))
  (Null makeTypeInfo))

simpleList :: Program
simpleList = Program [("main", constF 0.0 #:# Null makeTypeInfo)] []

simpleAdd :: Program
simpleAdd = Program [("main", PlusF makeTypeInfo (constF 0.0) (constF 1.0))] []

uniformProg :: Program
uniformProg = Program [("main", uniform)] []

normalProg :: Program
normalProg = Program [("main", normal)] []

uniformProgMult :: Program
uniformProgMult = Program [("main", uniform #*# constF (-0.5))] []

normalProgMult :: Program
normalProgMult = Program [("main", normal #*# constF 0.5)] []

uniformProgPlus :: Program
uniformProgPlus = Program [("main", uniform #+# constF 4)] []

normalProgMultPlus :: Program
normalProgMultPlus = Program [("main", normal #*# constF 2 #+# constF 1)] []


uniformNegPlus :: Program
uniformNegPlus = Program [("main", negF (uniform #+#constF 4))] []

uniformIfProg :: Program
uniformIfProg = Program [("main", ifThenElse (GreaterThan makeTypeInfo uniform (constF 0.5))
                             uniform
                             (uniform #+# constF 5))] []

uniformExp :: Program
uniformExp = Program [("main", injF "exp" [uniform #+# constF 4])] []

testMultLeft :: Expr
testMultLeft = constF 3.0 #*# normal

testList :: Program
testList = Program [("main", (constF 0.5 #*# uniform) #:# (normal #:# Null makeTypeInfo))] []

simpleTuple :: Program
simpleTuple = Program [("main", tuple (constF 0.5 #*# uniform) normal)] []

constantProg :: Program
constantProg = Program [("main", constF 2)] []

simpleCall :: Program
simpleCall = Program [("unif", uniform), ("main", var "unif")] []

testCallArg :: Program
testCallArg = Program [("unif", "x" #-># (var "x" #+# uniform)), ("main", apply (var "unif") (constF 3))] []

testNeg :: Expr
testNeg = negF uniform

testNegFail :: Expr
testNegFail = negF (uniform #+# uniform)

testInjF :: Program
testInjF = Program [("main", injF "double" [uniform])] []

testInjFPlusLeft :: Program
testInjFPlusLeft = Program [("main", injF "plus" [constF 1, uniform])] []

testInjFPlusRight :: Program
testInjFPlusRight = Program [("main", injF "plus" [uniform, constF 1])] []

testInjF2 :: Program
testInjF2 = Program [("main", injF "double" [injF "plus" [constF 1, uniform]])] []

testPlus3 :: Program
testPlus3 = Program [("main", letIn "a" uniform (var "a" #+# var "a"))] []

testTopK :: Program
testTopK = Program [("main", ifThenElse (bernoulli 0.95) (constF 1) (constF 0))] []

testTheta :: Program
testTheta = Program [("main", "thetas" #-># theta (var "thetas") 0)] []

testThetaTree :: Program
testThetaTree = Program [("main", "thetas" #-># (theta (var "thetas") 2 #+# theta (Subtree makeTypeInfo (var "thetas") 1) 1))] []

testAnd :: Program
testAnd = Program [("main", (normal #<# constF 0) #&&# (uniform #># constF 0.5))] []

testOr :: Program
testOr = Program [("main", (normal #># constF 0) #||# (uniform #># constF 0.5))] []

testNot :: Program
testNot = Program [("main", (#!#) (uniform #<# constF 0.75))] []

testCallLambda :: Program
testCallLambda = Program [("main", apply ("x" #-># (var "x" #+# uniform)) (constF 2))] []

testCallLambdaAdvanced :: Program
testCallLambdaAdvanced = Program [("main", letIn "l" ("a" #-># (var "a" #+# uniform)) (apply (var "l") (constF 2)))] []

testLambdaParameter :: Program
testLambdaParameter = Program [("main", apply (var "other") ("x" #-># (var "x" #*# constF 2)) ), ("other", "f" #-># apply (var "f") (constF 5))] []

testLetIn :: Program
testLetIn = Program [("main", letIn "u" uniform (var "u" #+# constF 1))] []
--testCallLambda = Program [] [] (CallLambda makeTypeInfo uniform (Lambda makeTypeInfo "a" (PlusF makeTypeInfo (var "a") uniform)))

testRecursion :: Program
testRecursion = Program [("main", apply (var "rec") (constF 8)),
                         ("rec", "x" #-># ifThenElse (var "x" #># constF 1) (constF 3 #*# apply (var "rec") (var "x" #*# constF 0.5)) uniform)] []

testNN :: Program
testNN = Program [("main", mNistAddExpr)] [("classifyMNist", TInt, EnumList $ map VInt [0,1,2,3,4,5,6,7,8,9])]

testDimProb :: Program
testDimProb = Program [("main", IfThenElse makeTypeInfo (LessThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.4))) (Constant makeTypeInfo $ VFloat 0.5) (Normal makeTypeInfo))] []


mNistAddExpr :: Expr
mNistAddExpr = "im1" #-># ("im2" #-># (ReadNN makeTypeInfo "classifyMNist" (var "im1") #+# ReadNN makeTypeInfo "classifyMNist" (var "im2")))

gaussLists :: Program
gaussLists = Program [("main", "thetas" #->#
  ifThenElse
    (uniform #># theta (var "thetas") 0)
    nul
    (((normal #*# theta (var "thetas") 1) #+# theta (var "thetas") 2) #:#
      apply (var "main") (var "thetas")))] []

testTopLevelLambda :: Program
testTopLevelLambda = Program [("main", "a" #-># (var "a" #+# uniform))] []

testDim :: Program
testDim = Program [("main", ifThenElse (bernoulli 0.5) (uniform #*# constF 2) (constF 3))] []

testCoin :: Program
testCoin = Program [("main", ifThenElse (bernoulli 0.5) (constI 1) (constI 2))] []

testDice :: Program
testDice = Program [("main", dice 6)] []

testDiceAdd :: Program
testDiceAdd = Program [ ("main", injF "plusI" [var "dice", var "dice"]),
                        ("dice", dice 6)] []

-- Not working
testFibonacci :: Program
testFibonacci = Program [ ("main","idx" #-># apply (apply fix (var "fibonacci")) (var "idx")),
                          ("fibonacci", "fib" #-># ("n" #-># ifThenElse (var "n" #<# constF 2) (var "n") (apply (var "fib") (var "n" #-# constF 1) #+# apply (var "fib") (var "n" #-# constF 2))) )] []

testPartialInjF :: Program
testPartialInjF = Program [("main", apply (injF "plus" [uniform]) (constF 5))] []

testInjFRenaming :: Program
testInjFRenaming = Program [("main", apply ("a" #-># (var "a" #+# uniform)) (constF 5))] []


testLeft :: Program
testLeft = Program [("main", injF "fromLeft" [injF "left" [constF 2]])] []

testEither :: Program
testEither = Program [("main", ifThenElse (bernoulli 0.5) (injF "left" [uniform]) (injF "right" [constI 1]))] []

testIsLeft :: Program
testIsLeft = Program [("main", ifThenElse (injF "isLeft" [ifThenElse (bernoulli 0.4) (injF "left" [uniform]) (injF "right" [constI 1])])
                                  (constF 1)
                                  (constF 2))] []

testIsRight :: Program
testIsRight = Program [("main", ifThenElse (injF "isRight" [ifThenElse (bernoulli 0.4) (injF "left" [uniform]) (injF "right" [constI 1])])
                                  (constF 1)
                                  (constF 2))] []

testFst :: Program
testFst = Program [("main", tfst (tuple uniform normal))] []

testHead :: Program
testHead = Program [("main", injF "head" [cons uniform nul])] []

testFstCall :: Program
testFstCall = Program [("main", tfst (var "bivariate")), ("bivariate", (tuple uniform normal))] []

testFstDiscrete :: Program
testFstDiscrete = Program [("main", tfst (tuple uniform  (bernoulli 0.4)))] []


{-
flipCoin :: Expr Double
flipCoin = GreaterThan makeTypeInfo uniform (constF 0.5))
variableLength :: Expr makeTypeInfo
variableLength = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0))
  (Null makeTypeInfo)
  --(Cons makeTypeInfo normal (Call makeTypeInfo "main"))
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Call makeTypeInfo "main"))

testProg :: Program
testProg = Program [("b", variableLength)]
             (Call makeTypeInfo "b")

testProgFix :: Program Float
testProgFix = Program [
                        ("main", ifThenElse
                                    (GreaterThan makeTypeInfo uniform(theta 1))
                                    (Call makeTypeInfo "term")
                                    (PlusF makeTypeInfo (theta 1) (Call makeTypeInfo "main"))),
                       ("b", theta 1),
                       ("term", ifThenElse
                           (GreaterThan makeTypeInfo (Call makeTypeInfo "b")(theta 1))
                           (constF 0.0))
                           (PlusF makeTypeInfo (theta 1) (Call makeTypeInfo "term")))]
              (Call makeTypeInfo "main")
testCoin :: Program Double
testCoin = Program [
                      ("f", ifThenElse
                                  (GreaterThan makeTypeInfo uniform (Call makeTypeInfo "b"))
                                  (Null makeTypeInfo)
                                  (Cons makeTypeInfo flipCoin (Call makeTypeInfo "f"))),
                     ("b", theta 0)
                     ]
              (Call makeTypeInfo "f")
dummyExpr :: Program
dummyExpr = Program [("main", GreaterThan makeTypeInfo uniform (Call makeTypeInfo "b")),
                                   ("b", theta 1)]
                          (Call makeTypeInfo "main")
maybeAdd :: Program Float
maybeAdd = Program [("maybeAddOne", ifThenElse
                                (GreaterThan makeTypeInfo uniform (theta 0))
                                (constF 0.0))
                                (PlusF makeTypeInfo (constF 1.0)) (Call makeTypeInfo "maybeAddTwo"))),
                   ("maybeAddTwo", ifThenElse
                               (GreaterThan makeTypeInfo uniform (theta 1))
                               (constF 0.0))
                               (PlusF makeTypeInfo (constF 2.0)) (Call makeTypeInfo "maybeAddOne")))]
                          (Call makeTypeInfo "maybeAddOne")
                          

nullIf :: Expr makeTypeInfo
nullIf =  ifThenElse
    (GreaterThan makeTypeInfo uniform (theta 0))
    (Null makeTypeInfo)
    (Cons makeTypeInfo (GreaterThan makeTypeInfo uniform (theta 1)) 
    (Null makeTypeInfo))

--testExpr :: Num a => Expr
testIf :: Expr Float
testIf = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0))
  (Constant makeTypeInfo (VBool True))
  (Constant makeTypeInfo (VBool False))

{-
--TODO Make params like Constant values (change to a type variable dynamically how?)
testLet2 :: Program
testLet2 = Program [](letIn "x"
                      (PlusF makeTypeInfo (theta 0) normal)
                      (injF "sig" [] (injF "mult" [theta 1]  (var "x"))))
-- let x = theta1 + normal in theta2 + sig(x) + theta3 * normal
-- let x = theta2 + sig(theta1 + normal) + theta3 * normal
-- theta1 = 0.1 theta2 = 0.8 
-- sample 1.9 -> x? sig(x) = 1.1 --> invert(sig = 1.1) = NaN
-- theta2 = 0.2
testLetNonInvert :: Program Double
testLetNonInvert = Program [] [] (letIn "x" (PlusF makeTypeInfo (theta 0) normal)
          (PlusF makeTypeInfo (injF "sig" [] (var "x")) (theta 1)))
          
testLetPot :: Program Double
testLetPot = Program [] [] (letIn "x" (PlusF makeTypeInfo (theta 0) normal) (injF "mult" [theta 1] (var "x")))

testInjFNot :: Program Double
testInjFNot  = Program [] [] (ifThenElse (injF "not" [] (GreaterThan makeTypeInfo (theta 0)uniform))
                            normal 
                            (injF "plus" [theta 1] normal))
testListPlus :: Program Double
testListPlus  = Program [] [] (injF "listMult" 
    [Cons makeTypeInfo (theta 0) (Cons makeTypeInfo (theta 1) (Null makeTypeInfo))] 
    (Cons makeTypeInfo (PlusF makeTypeInfo normal (constF 2.0)))
     (Cons makeTypeInfo (PlusF makeTypeInfo normal (constF 3.0))) (Null makeTypeInfo)))
    )
-}
testHakaru :: Program Double
testHakaru = Program [](LetInmakeTypeInfo "x" uniform
                                      (letIn  "y" uniform
                                         (Cons makeTypeInfo (var "x")
                                           (Cons makeTypeInfo
                                             (var "y")
                                             (Cons makeTypeInfo
                                                (PlusF makeTypeInfo (MultF makeTypeInfo (constF (-2.0)))(var "x")) (var "y"))
                                                (Null makeTypeInfo))))))
{-
-- let x = normal in (if flip then x + theta else x - 0.7)
testBranchedLetList :: Program Double
testBranchedLetList = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo normal (constF 1.0)))
                              (LetInmakeTypeInfo "y" normal
                                    (ifThenElse
                                      (GreaterThan makeTypeInfo uniform(constF 0.8)))
                                        (Cons makeTypeInfo
                                          (injF "sig" [] (injF "plus" [theta 0]  (var "x")))
                                          (Cons makeTypeInfo  (injF "sig" []  (var "y")) (Null makeTypeInfo)))
                                        (Cons makeTypeInfo
                                          (injF "sig" [] (injF "plus" [constF (-0.7))]  (var "x")))
                                          (Cons makeTypeInfo  (injF "sig" [] (injF "plus" [theta 1]  (var "y"))) (Null makeTypeInfo)))
                                          )))
testBranchedLetList2 :: Program Double
testBranchedLetList2 = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo normal (constF 0.357)))
                                        (Cons makeTypeInfo
                                          (ifThenElse
                                            (GreaterThan makeTypeInfo uniform(constF 0.659)))
                                            (injF "sig" [] (injF "plus" [theta 0]  (var "x")))
                                            (injF "sig" [] (injF "plus" [constF (-0.358))]  (var "x"))))
                                          (Cons makeTypeInfo(injF "sig" []
                                                  (MultF makeTypeInfo (constF (-0.358)))
                                                   (PlusF makeTypeInfo (var "x") normal))) (Null makeTypeInfo))
                                        ))
-- let x = normal in let y = normal in [(if flip then f(x*y) else g(x)), (if flip then f(y) else g(y)), sig(y * (x + normal))]
-- y = VBranch val1 val2
-- sig(y * (x + normal)) = BranchedProbability "x" (BranchedProbability "y" val1 val2) (BranchedProbability "y" val3 val4)
-- BranchProbability "y" v1 v2
-- BranchedProbability "x" 


-- let x = normal in [sig(x), x+uniform]
-- query [ < 0.5, 1]
testBranchedLetList3 :: Program Double
testBranchedLetList3 = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo normal (constF 0.357)))
                                  (LetInmakeTypeInfo "y" normal
                                        (Cons makeTypeInfo
                                          (ifThenElse
                                            (GreaterThan makeTypeInfo uniform(constF 0.659)))
                                            (injF "sig" [] (injF "plus" [theta 0]  (var "x")))
                                            (injF "sig" [] (injF "plus" [constF (-0.358))]  (var "x"))))
                                          (Cons makeTypeInfo
                                            (ifThenElse
                                              (GreaterThan makeTypeInfo uniform(constF 0.659)))
                                              (injF "sig" [] (injF "plus" [theta 0]  (var "y")))
                                              (injF "sig" [] (injF "plus" [constF (-0.358))]  (var "y"))))
                                          
                                          (Cons makeTypeInfo(injF "sig" []
                                                     (MultF makeTypeInfo (var "y")
                                                      (PlusF makeTypeInfo (var "x") normal))) (Null makeTypeInfo)
                                                    ))
                                                   )
                                        ))
                                        

testBranchedLet :: Program Double
testBranchedLet = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo normal (constF 1.0)))
                                    (ifThenElse
                                      (GreaterThan makeTypeInfo uniform(constF 0.8)))
                                      (injF "sig" [] (injF "plus" [theta 0]  (var "x")))
                                      (injF "sig" [] (injF "plus" [constF (-0.7))]  (var "x")))))
-}

testNestedLetInDecl :: Program Double
testNestedLetInDecl = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (theta 0) normal)
                         (letIn  "y" (PlusF makeTypeInfo (theta 1) (PlusF makeTypeInfo normal (var "x")))
                                  (Cons makeTypeInfo (var "x")
                                     (Cons makeTypeInfo (var "y")
                                       (Cons makeTypeInfo (PlusF makeTypeInfo normal  (var "y"))
                                        (Null makeTypeInfo))))))
-- let x = normal in let y = normal in [x, x+y]
                                   
testNestedLetInWit :: Program Double
testNestedLetInWit = Program [] [] (letIn "x" (MultF makeTypeInfo (theta 0) normal)
                         (letIn  "y" (MultF makeTypeInfo normal (theta 0) )
                                  (Cons makeTypeInfo (PlusF makeTypeInfo (var "y") (var "x"))
                                    (Cons makeTypeInfo  (var "x")
                                     (Null makeTypeInfo)))))
--testInjFD :: Program Double
--testInjFD = Program [] [] (injF "mult" [constF (-2.0))] (PlusF makeTypeInfo (theta 0) normal))

testObserve :: Program Double
testObserve = Program [] [] (LetInmakeTypeInfo "x"  normal
                              (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (constF 2.0)) normal)
                                (var "x")))

testLetXYD :: Program Double
testLetXYD = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (theta 0) normal)
                          (letIn  "y"  (theta 1)
                                         (Cons makeTypeInfo (var "x") 
                                           (Cons makeTypeInfo 
                                             (PlusF makeTypeInfo normal(var "y"))
                                             (Cons makeTypeInfo 
                                                (MultF makeTypeInfo (PlusF makeTypeInfo normal(var "x")) (var "y"))
                                                (Null makeTypeInfo))))))
                                             
testLetXY :: Program Double
testLetXY = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (theta 0) normal)
                          (letIn  "y" (PlusF makeTypeInfo (theta 1) normal)
                                         (Cons makeTypeInfo (var "x") 
                                           (Cons makeTypeInfo 
                                             (var "y")
                                             (Cons makeTypeInfo 
                                                (MultF makeTypeInfo (PlusF makeTypeInfo normal(var "x")) (var "y"))
                                                (Null makeTypeInfo))))))
                                             

testLetTuple :: Program Double
testLetTuple = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (theta 0) normal)
                                              (Cons makeTypeInfo (var "x") 
                                                (Cons makeTypeInfo 
                                                  (PlusF makeTypeInfo normal(var "x")) 
                                                  (Null makeTypeInfo))))

testNormal :: Program Double
testNormal = Program [] [] normal

--testLetE :: Expr Double
--testLetE = letIn "x" normal (injF "plus" [constF 3.0)] (var "x"))
testPlusProg :: Program Float
testPlusProg = Program [("main", ifThenElse
                                                   (GreaterThan makeTypeInfo (theta 1)(theta 1))
                                                   (theta 1)
                                                   (PlusF makeTypeInfo (theta 1) (Call makeTypeInfo "main")))]
                             (Call makeTypeInfo "main")

testPlus :: Expr makeTypeInfo
testPlus = ifThenElse
             (GreaterThan makeTypeInfo uniform (theta 0))
             (Null makeTypeInfo)
             (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Null makeTypeInfo))

testPlus2 :: Program
testPlus2 = Program [] [] (PlusF makeTypeInfo (MultF makeTypeInfo (theta 0) uniform) (theta 1))


testGreater :: Expr makeTypeInfo
testGreater = GreaterThan makeTypeInfo uniform (theta 0)

testGreater2 :: Expr Float
testGreater2 = GreaterThan makeTypeInfo (theta 0) uniform

testExpr2 :: Expr makeTypeInfo
testExpr2 = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0))
  (Null makeTypeInfo)
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Call makeTypeInfo "main"))

testBool :: Expr makeTypeInfo
testBool = GreaterThan makeTypeInfo uniform (theta 0)

testGauss :: Expr makeTypeInfo
testGauss = PlusF makeTypeInfo (MultF makeTypeInfo normal (theta 0)) (theta 1)


--  (ifThenElse
--    (GreaterThan makeTypeInfo uniform (theta 1))
--    (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Call makeTypeInfo "main"))
--    )

--testGauss = compile "Normal * theta[0] + theta[1]"

{--
MNIST_CNN_GEN :: Image -> Int (CNN yields distribution, we return sample)
e.g. [0 -> 0.5; 1 -> 0.3, 2 -> 0.2]; when sampling: return 0 with probability 0.5
     [0 -> 0.98; 1 -> 0.01, 2 -> 0.01]; when sampling: return 0 with probability 0.98
MNIST_CNN_Likelihood :: Image -> Int -> Float (index into distribution)
AutoDiff yields gradient for
MNIST_CNN:: Image -> Int (As Softmax over probabilities)
main =
  let
    x <- MNIST_CNN(imgA)
    y <- MNIST_CNN(imgB)
  in x + y

How do we train this? We get a result... 15 and imgA and imgB.
  MaxP(MNIST_CNN(imgA) = 6 && MNIST_CNN(imgB) = 9)
  MaxP(MNIST_CNN(imgA) = 7 && MNIST_CNN(imgB) = 8)
  MaxP(MNIST_CNN(imgA) = 8 && MNIST_CNN(imgB) = 7)
  MaxP(MNIST_CNN(imgA) = 9 && MNIST_CNN(imgB) = 6)

likelihood(imgA, imgB, N) = \sum{x,y | x+y=15} (imgA == x && imgB == y)

Maybe we can do Distributional MNist? (Assume for example we have a distribution of x-digit MNIST postal codes and samples from that distribution.
Assume we know the distribution, can we find the MNIST mapping?
 -}
testGaussianMixture :: Expr makeTypeInfo
testGaussianMixture = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo normal (theta 1))
      (theta 2))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo normal (theta 3))
        (theta 4))
      (Null makeTypeInfo)))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo normal (theta 5))
      (theta 6))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo normal (theta 7))
        (theta 8))
      (Null makeTypeInfo)))

gaussianMixture :: Expr makeTypeInfo
gaussianMixture = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo normal (theta 1))
      (theta 2))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo normal (theta 3))
        (theta 4))
      (Cons makeTypeInfo
        (Constant makeTypeInfo (VBool True))
        (Null makeTypeInfo))))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo normal (theta 5))
      (theta 6))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo normal (theta 7))
        (theta 8))
      (Cons makeTypeInfo
        (Constant makeTypeInfo (VBool True))
        (Null makeTypeInfo))))

testIntractable :: Expr makeTypeInfo
testIntractable = MultF makeTypeInfo
  (MultF makeTypeInfo normal (theta 1))
  (MultF makeTypeInfo normal (theta 2))

testInconsistent :: Expr Double
testInconsistent = ifThenElse
  (GreaterThan makeTypeInfo (constF 0.0)) (theta 0))
  (Constant makeTypeInfo (VBool True))
  (Constant makeTypeInfo (VBool False))

failureCase :: Expr makeTypeInfo
failureCase = MultF makeTypeInfo normal (theta 0)


gaussMultiLists :: Expr makeTypeInfo
gaussMultiLists = ifThenElse
  (GreaterThan makeTypeInfo uniform (theta 0) )
  (Null makeTypeInfo)
  (Cons makeTypeInfo
    (ifThenElse
      (GreaterThan makeTypeInfo uniform (theta 1))
      (PlusF makeTypeInfo (MultF makeTypeInfo normal (theta 2)) (theta 3))
      (PlusF makeTypeInfo (MultF makeTypeInfo normal (theta 4)) (theta 5)))
    (Call makeTypeInfo "main"))

-- typeinfer :: Expr makeTypeInfo -> Expr RType a
-- typeInferMaybe :: Expr (Maybe RType) a -> Expr RType a

testNNUntyped :: Expr makeTypeInfo
--testNN : Lambda im1 -> (Lambda im2 -> readNN im1 + readNN im2)
testNNUntyped = Lambda makeTypeInfo "im1" (Lambda makeTypeInfo "im2" (PlusI makeTypeInfo (ReadNN makeTypeInfo "classifyMNist" (var "im1")) (ReadNN makeTypeInfo "classifyMNist" (var "im2"))))
{-
testNN :: Expr
testNN = Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol TInt)) Bottom) "im1"
  (Lambda (TypeInfo (TArrow TSymbol TInt) Bottom) "im2" (PlusI (TypeInfo TInt Integrate)
    (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
    (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2"))))
    

mNistNoise :: Expr
mNistNoise = Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol TInt)) Bottom) "im1"
  (Lambda (TypeInfo (TArrow TSymbol TInt) Bottom) "im2"
    (IfThenElse (TypeInfo TInt Integrate) (GreaterThan (TypeInfo TBool Integrate) (Uniform (TypeInfo TFloat Integrate)) (ThetaI (TypeInfo TFloat Deterministic) 0) )
    (PlusI (TypeInfo TInt Integrate)
      (Constant (TypeInfo TInt Deterministic) (VInt 1))
      (PlusI (TypeInfo TInt Integrate)
            (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
            (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2"))))
    (PlusI (TypeInfo TInt Integrate)
      (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
      (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2")))))

triMNist :: Expr
triMNist = Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol (TArrow TSymbol TInt))) Bottom) "im1"
  (Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol TInt)) Bottom) "im2"
    (Lambda (TypeInfo (TArrow TSymbol TInt) Bottom) "im3" (PlusI (TypeInfo TInt Integrate)
      (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im3"))
      (PlusI (TypeInfo TInt Integrate)
        (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
        (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2")))
      )))

expertModels :: Expr makeTypeInfo
expertModels = Lambda makeTypeInfo "im" (ifThenElse
  (ReadNN makeTypeInfo "isMnist" (var "im"))
  (ReadNN makeTypeInfo "classifyMNist" (var "im"))
  (ReadNN makeTypeInfo "classifyCIFAR" (var "im")))

expertModelsTyped :: Expr
expertModelsTyped = Lambda (TypeInfo (TArrow TSymbol TInt) Integrate) "im" (IfThenElse (TypeInfo TInt Integrate)
  (ReadNN (TypeInfo TBool Integrate) "isMnist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (ReadNN (TypeInfo TInt Integrate) "classifyCIFAR" (Var (TypeInfo TSymbol Deterministic) "im")))

expertAnnotated :: Expr makeTypeInfo
expertAnnotated = Lambda makeTypeInfo "im" (ifThenElse
  (ReadNN makeTypeInfo "isMnist" (var "im"))
  (Cons makeTypeInfo (constI 1)) (Cons makeTypeInfo (ReadNN makeTypeInfo "classifyMNist" (var "im")) (Null makeTypeInfo)))
  (Cons makeTypeInfo (constI 2)) (Cons makeTypeInfo (ReadNN makeTypeInfo "classifyCIFAR" (var "im")) (Null makeTypeInfo))))

expertAnnotatedTyped :: Expr
expertAnnotatedTyped = Lambda (TypeInfo (TArrow TSymbol (SPLL.Typing.RType.ListOf TInt)) Integrate) "im" (IfThenElse (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate)
  (ReadNN (TypeInfo TBool Integrate) "isMnist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (Constant (TypeInfo TInt Deterministic) (VInt 1)) (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im")) (Null (TypeInfo (SPLL.Typing.RType.ListOf TInt) Deterministic))))
  (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (Constant (TypeInfo TInt Deterministic) (VInt 2)) (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (ReadNN (TypeInfo TInt Integrate) "classifyCIFAR" (Var (TypeInfo TSymbol Deterministic) "im")) (Null (TypeInfo (SPLL.Typing.RType.ListOf TInt) Deterministic)))))
-}
compilationExample :: Expr makeTypeInfo
compilationExample = GreaterThan makeTypeInfo uniform (theta 0)

--expert_model_proofs image =
--  if isMNist
--    then (1, classifyMNist image)
--    else (2, classifyCIFAR image)

--expert_model image =
--  if is28x28x1 image
--    then classifyMNist image
--    else classifyCIFAR image
-}
