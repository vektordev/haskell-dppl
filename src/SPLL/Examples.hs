module SPLL.Examples where

import SPLL.Lang.Lang

import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing (TypeInfo, makeTypeInfo)

--weatherHask lastDay = if lastDay == rainy
--  then let current = randA in (current, weatherHask current)
--  else let current = randB in (current, weatherHask current)

paramExpr :: Expr Double
paramExpr = Arg makeTypeInfo "iterations" TFloat (IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Var makeTypeInfo "iterations") (Constant makeTypeInfo (VFloat 0.5)))
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (CallArg makeTypeInfo "main" [PlusF makeTypeInfo (Call makeTypeInfo "iterations") (Constant makeTypeInfo (VFloat (-1.0)))]))
  (Null makeTypeInfo))

uniformProg :: Program a
uniformProg = Program [] [] (Uniform makeTypeInfo)
normalProg :: Program a
normalProg = Program [] [] (Normal makeTypeInfo)
uniformProgMult :: Program Double
uniformProgMult = Program [] [] (MultF makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat (-0.5))))
normalProgMult :: Program Double
normalProgMult = Program [] [] (MultF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat (0.5))))
uniformProgPlus :: Program Double
uniformProgPlus = Program [] [] (PlusF makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 4)))
uniformNegPlus :: Program Double
uniformNegPlus = Program [] [] (NegF makeTypeInfo (PlusF makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 4))))
uniformIfProg :: Program Double
uniformIfProg = Program [] [] (IfThenElse makeTypeInfo (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo $ VFloat 0.5))
                             (Uniform makeTypeInfo)
                             (PlusF makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo $ VFloat 5)))
uniformExp :: Program Double
uniformExp = Program [] [] (ExpF makeTypeInfo (PlusF makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 4))))

testMultLeft ::Expr Float
testMultLeft = MultF makeTypeInfo  (Constant makeTypeInfo (VFloat 3.0)) (Normal makeTypeInfo)

testList :: Program Double
testList = Program [] [] (Cons makeTypeInfo (MultF makeTypeInfo (Constant makeTypeInfo (VFloat 0.5)) (Uniform makeTypeInfo)) (Cons makeTypeInfo (Normal makeTypeInfo) (Null makeTypeInfo)))

simpleTuple :: Program Double
simpleTuple = Program [] [] (TCons makeTypeInfo (MultF makeTypeInfo (Constant makeTypeInfo (VFloat 0.5)) (Uniform makeTypeInfo)) (Normal makeTypeInfo))
constantProg :: Program Double
constantProg = Program [] [] (Constant makeTypeInfo $ VFloat 2)
simpleCall :: Program Double
simpleCall = Program [("unif", Uniform makeTypeInfo) ] [] (Call makeTypeInfo "unif")

testNeg :: Expr a
testNeg = NegF makeTypeInfo (Uniform makeTypeInfo)

testNegFail :: Expr a
testNegFail = NegF makeTypeInfo (PlusF makeTypeInfo (Uniform makeTypeInfo) (Uniform makeTypeInfo))

testInjF :: Program Double
testInjF = Program [] [] (InjF makeTypeInfo "double" [Uniform makeTypeInfo])

--testInjF2 :: Program Double
--testInjF2 = Program [] [] (ExpF makeTypeInfo (MultF makeTypeInfo (Constant makeTypeInfo (VFloat 2)) (Uniform makeTypeInfo)))

testInjF2 :: Program Double
testInjF2 = Program [] [] (ExpF makeTypeInfo (InjF makeTypeInfo "double" [Uniform makeTypeInfo]))

testPlus3 :: Program Double
testPlus3 = Program [] [] (LetIn makeTypeInfo "a" (Uniform makeTypeInfo) (PlusF makeTypeInfo (Var makeTypeInfo "a") (Var makeTypeInfo "a")))

testTopK :: Program Double
testTopK = Program [] [] (IfThenElse makeTypeInfo (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.05))) (Constant makeTypeInfo (VFloat 1)) (Constant makeTypeInfo (VFloat 0)))

testTheta :: Program Double
testTheta = Program [] [] (Lambda makeTypeInfo "thetas" (ThetaI makeTypeInfo (Var makeTypeInfo "thetas") 0))

testThetaTree :: Program Double
testThetaTree = Program [] [] (Lambda makeTypeInfo "thetas" (PlusF makeTypeInfo (ThetaI makeTypeInfo (Var makeTypeInfo "thetas") 2) (ThetaI makeTypeInfo (Subtree makeTypeInfo (Var makeTypeInfo "thetas") 1) 1)))

testAnd :: Program Double
testAnd = Program [] [] (And makeTypeInfo (LessThan makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 0))) (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.5))))

testOr :: Program Double
testOr = Program [] [] (Or makeTypeInfo (LessThan makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 0))) (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.5))))

testNot :: Program Double
testNot = Program [] [] (Not makeTypeInfo (LessThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.75))))

testCallLambda :: Program Double
testCallLambda = Program [] [] (Apply makeTypeInfo (Lambda makeTypeInfo "a" (PlusF makeTypeInfo (Var makeTypeInfo "a") (Uniform makeTypeInfo))) (Constant makeTypeInfo (VFloat 2)))

testCallLambdaAdvanced :: Program Double
testCallLambdaAdvanced = Program [] [] (LetIn makeTypeInfo "l" (Lambda makeTypeInfo "a" (PlusF makeTypeInfo (Var makeTypeInfo "a") (Uniform makeTypeInfo))) (Apply makeTypeInfo (Var makeTypeInfo "l") (Constant makeTypeInfo (VFloat 2))))

testLetIn :: Program Double
testLetIn = Program [] [] (LetIn makeTypeInfo "u" (Uniform makeTypeInfo) (PlusF makeTypeInfo (Var makeTypeInfo "u") (Constant makeTypeInfo (VFloat 1))))
--testCallLambda = Program [] [] (CallLambda makeTypeInfo (Uniform makeTypeInfo) (Lambda makeTypeInfo "a" (PlusF makeTypeInfo (Var makeTypeInfo "a") (Uniform makeTypeInfo))))
{-
flipCoin :: Expr Double
flipCoin = GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Constant makeTypeInfo (VFloat 0.5))
variableLength :: Expr makeTypeInfo a
variableLength = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Null makeTypeInfo)
  --(Cons makeTypeInfo (Normal makeTypeInfo) (Call makeTypeInfo "main"))
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Call makeTypeInfo "main"))

testProg :: Program a
testProg = Program [("b", variableLength)]
             (Call makeTypeInfo "b")

testProgFix :: Program Float
testProgFix = Program [
                        ("main", IfThenElse makeTypeInfo
                                    (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(ThetaI makeTypeInfo 1))
                                    (Call makeTypeInfo "term")
                                    (PlusF makeTypeInfo (ThetaI makeTypeInfo 1) (Call makeTypeInfo "main"))),
                       ("b", ThetaI makeTypeInfo 1),
                       ("term", IfThenElse makeTypeInfo
                           (GreaterThan makeTypeInfo (Call makeTypeInfo "b")(ThetaI makeTypeInfo 1))
                           (Constant makeTypeInfo (VFloat 0.0))
                           (PlusF makeTypeInfo (ThetaI makeTypeInfo 1) (Call makeTypeInfo "term")))]
              (Call makeTypeInfo "main")
testCoin :: Program Double
testCoin = Program [
                      ("f", IfThenElse makeTypeInfo
                                  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Call makeTypeInfo "b"))
                                  (Null makeTypeInfo)
                                  (Cons makeTypeInfo flipCoin (Call makeTypeInfo "f"))),
                     ("b", ThetaI makeTypeInfo 0)
                     ]
              (Call makeTypeInfo "f")
dummyExpr :: Program a
dummyExpr = Program [("main", GreaterThan makeTypeInfo (Uniform makeTypeInfo) (Call makeTypeInfo "b")),
                                   ("b", ThetaI makeTypeInfo 1)]
                          (Call makeTypeInfo "main")
maybeAdd :: Program Float
maybeAdd = Program [("maybeAddOne", IfThenElse makeTypeInfo
                                (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
                                (Constant makeTypeInfo (VFloat 0.0))
                                (PlusF makeTypeInfo (Constant makeTypeInfo (VFloat 1.0)) (Call makeTypeInfo "maybeAddTwo"))),
                   ("maybeAddTwo", IfThenElse makeTypeInfo
                               (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 1))
                               (Constant makeTypeInfo (VFloat 0.0))
                               (PlusF makeTypeInfo (Constant makeTypeInfo (VFloat 2.0)) (Call makeTypeInfo "maybeAddOne")))]
                          (Call makeTypeInfo "maybeAddOne")
                          

nullIf :: Expr makeTypeInfo a
nullIf =  IfThenElse makeTypeInfo
    (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
    (Null makeTypeInfo)
    (Cons makeTypeInfo (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 1)) 
    (Null makeTypeInfo))

--testExpr :: Num a => Expr a
testIf :: Expr Float
testIf = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Constant makeTypeInfo (VBool True))
  (Constant makeTypeInfo (VBool False))

{-
--TODO Make params like Constant values (change to a type variable dynamically how?)
testLet2 :: Program a
testLet2 = Program [](LetIn makeTypeInfo "x"
                      (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                      (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "mult" [ThetaI makeTypeInfo 1]  (Var makeTypeInfo "x"))))
-- let x = theta1 + normal in theta2 + sig(x) + theta3 * normal
-- let x = theta2 + sig(theta1 + normal) + theta3 * normal
-- theta1 = 0.1 theta2 = 0.8 
-- sample 1.9 -> x? sig(x) = 1.1 --> invert(sig = 1.1) = NaN
-- theta2 = 0.2
testLetNonInvert :: Program Double
testLetNonInvert = Program [] [] (LetIn makeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
          (PlusF makeTypeInfo (InjF makeTypeInfo "sig" [] (Var makeTypeInfo "x")) (ThetaI makeTypeInfo 1)))
          
testLetPot :: Program Double
testLetPot = Program [] [] (LetIn makeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo)) (InjF makeTypeInfo "mult" [ThetaI makeTypeInfo 1] (Var makeTypeInfo "x")))

testInjFNot :: Program Double
testInjFNot  = Program [] [] (IfThenElse makeTypeInfo (InjF makeTypeInfo "not" [] (GreaterThan makeTypeInfo (ThetaI makeTypeInfo 0)(Uniform makeTypeInfo)))
                            (Normal makeTypeInfo) 
                            (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 1] (Normal makeTypeInfo)))
testListPlus :: Program Double
testListPlus  = Program [] [] (InjF makeTypeInfo "listMult" 
    [Cons makeTypeInfo (ThetaI makeTypeInfo 0) (Cons makeTypeInfo (ThetaI makeTypeInfo 1) (Null makeTypeInfo))] 
    (Cons makeTypeInfo (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 2.0)))
     (Cons makeTypeInfo (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 3.0))) (Null makeTypeInfo)))
    )
-}
testHakaru :: Program Double
testHakaru = Program [](LetInmakeTypeInfo "x" (Uniform makeTypeInfo)
                                      (LetIn makeTypeInfo  "y" (Uniform makeTypeInfo)
                                         (Cons makeTypeInfo (Var makeTypeInfo "x")
                                           (Cons makeTypeInfo
                                             (Var makeTypeInfo "y")
                                             (Cons makeTypeInfo
                                                (PlusF makeTypeInfo (MultF makeTypeInfo (Constant makeTypeInfo (VFloat (-2.0)))(Var makeTypeInfo "x")) (Var makeTypeInfo "y"))
                                                (Null makeTypeInfo))))))
{-
-- let x = normal in (if flip then x + theta else x - 0.7)
testBranchedLetList :: Program Double
testBranchedLetList = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 1.0)))
                              (LetInmakeTypeInfo "y" (Normal makeTypeInfo)
                                    (IfThenElse makeTypeInfo
                                      (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(Constant makeTypeInfo (VFloat 0.8)))
                                        (Cons makeTypeInfo
                                          (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 0]  (Var makeTypeInfo "x")))
                                          (Cons makeTypeInfo  (InjF makeTypeInfo "sig" []  (Var makeTypeInfo "y")) (Null makeTypeInfo)))
                                        (Cons makeTypeInfo
                                          (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat (-0.7))]  (Var makeTypeInfo "x")))
                                          (Cons makeTypeInfo  (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 1]  (Var makeTypeInfo "y"))) (Null makeTypeInfo)))
                                          )))
testBranchedLetList2 :: Program Double
testBranchedLetList2 = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 0.357)))
                                        (Cons makeTypeInfo
                                          (IfThenElse makeTypeInfo
                                            (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(Constant makeTypeInfo (VFloat 0.659)))
                                            (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 0]  (Var makeTypeInfo "x")))
                                            (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat (-0.358))]  (Var makeTypeInfo "x"))))
                                          (Cons makeTypeInfo(InjF makeTypeInfo "sig" []
                                                  (MultF makeTypeInfo (Constant makeTypeInfo (VFloat (-0.358)))
                                                   (PlusF makeTypeInfo (Var makeTypeInfo "x") (Normal makeTypeInfo)))) (Null makeTypeInfo))
                                        ))
-- let x = normal in let y = normal in [(if flip then f(x*y) else g(x)), (if flip then f(y) else g(y)), sig(y * (x + normal))]
-- y = VBranch val1 val2
-- sig(y * (x + normal)) = BranchedProbability "x" (BranchedProbability "y" val1 val2) (BranchedProbability "y" val3 val4)
-- BranchProbability "y" v1 v2
-- BranchedProbability "x" 


-- let x = normal in [sig(x), x+uniform]
-- query [ < 0.5, 1]
testBranchedLetList3 :: Program Double
testBranchedLetList3 = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 0.357)))
                                  (LetInmakeTypeInfo "y" (Normal makeTypeInfo)
                                        (Cons makeTypeInfo
                                          (IfThenElse makeTypeInfo
                                            (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(Constant makeTypeInfo (VFloat 0.659)))
                                            (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 0]  (Var makeTypeInfo "x")))
                                            (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat (-0.358))]  (Var makeTypeInfo "x"))))
                                          (Cons makeTypeInfo
                                            (IfThenElse makeTypeInfo
                                              (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(Constant makeTypeInfo (VFloat 0.659)))
                                              (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 0]  (Var makeTypeInfo "y")))
                                              (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat (-0.358))]  (Var makeTypeInfo "y"))))
                                          
                                          (Cons makeTypeInfo(InjF makeTypeInfo "sig" []
                                                     (MultF makeTypeInfo (Var makeTypeInfo "y")
                                                      (PlusF makeTypeInfo (Var makeTypeInfo "x") (Normal makeTypeInfo)))) (Null makeTypeInfo)
                                                    ))
                                                   )
                                        ))
                                        

testBranchedLet :: Program Double
testBranchedLet = Program [](LetInmakeTypeInfo "x" (PlusF makeTypeInfo (Normal makeTypeInfo) (Constant makeTypeInfo (VFloat 1.0)))
                                    (IfThenElse makeTypeInfo
                                      (GreaterThan makeTypeInfo (Uniform makeTypeInfo)(Constant makeTypeInfo (VFloat 0.8)))
                                      (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [ThetaI makeTypeInfo 0]  (Var makeTypeInfo "x")))
                                      (InjF makeTypeInfo "sig" [] (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat (-0.7))]  (Var makeTypeInfo "x")))))
-}

testNestedLetInDecl :: Program Double
testNestedLetInDecl = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                         (LetIn makeTypeInfo  "y" (PlusF makeTypeInfo (ThetaI makeTypeInfo 1) (PlusF makeTypeInfo (Normal makeTypeInfo) (Var makeTypeInfo "x")))
                                  (Cons makeTypeInfo (Var makeTypeInfo "x")
                                     (Cons makeTypeInfo (Var makeTypeInfo "y")
                                       (Cons makeTypeInfo (PlusF makeTypeInfo (Normal makeTypeInfo)  (Var makeTypeInfo "y"))
                                        (Null makeTypeInfo))))))
-- let x = normal in let y = normal in [x, x+y]
                                   
testNestedLetInWit :: Program Double
testNestedLetInWit = Program [] [] (LetIn makeTypeInfo "x" (MultF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                         (LetIn makeTypeInfo  "y" (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 0) )
                                  (Cons makeTypeInfo (PlusF makeTypeInfo (Var makeTypeInfo "y") (Var makeTypeInfo "x"))
                                    (Cons makeTypeInfo  (Var makeTypeInfo "x")
                                     (Null makeTypeInfo)))))
--testInjFD :: Program Double
--testInjFD = Program [] [] (InjF makeTypeInfo "mult" [Constant makeTypeInfo (VFloat (-2.0))] (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo)))

testObserve :: Program Double
testObserve = Program [] [] (LetInmakeTypeInfo "x"  (Normal makeTypeInfo)
                              (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (Constant makeTypeInfo (VFloat 2.0)) (Normal makeTypeInfo))
                                (Var makeTypeInfo "x")))

testLetXYD :: Program Double
testLetXYD = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                          (LetIn makeTypeInfo  "y"  (ThetaI makeTypeInfo 1)
                                         (Cons makeTypeInfo (Var makeTypeInfo "x") 
                                           (Cons makeTypeInfo 
                                             (PlusF makeTypeInfo (Normal makeTypeInfo)(Var makeTypeInfo "y"))
                                             (Cons makeTypeInfo 
                                                (MultF makeTypeInfo (PlusF makeTypeInfo (Normal makeTypeInfo)(Var makeTypeInfo "x")) (Var makeTypeInfo "y"))
                                                (Null makeTypeInfo))))))
                                             
testLetXY :: Program Double
testLetXY = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                          (LetIn makeTypeInfo  "y" (PlusF makeTypeInfo (ThetaI makeTypeInfo 1) (Normal makeTypeInfo))
                                         (Cons makeTypeInfo (Var makeTypeInfo "x") 
                                           (Cons makeTypeInfo 
                                             (Var makeTypeInfo "y")
                                             (Cons makeTypeInfo 
                                                (MultF makeTypeInfo (PlusF makeTypeInfo (Normal makeTypeInfo)(Var makeTypeInfo "x")) (Var makeTypeInfo "y"))
                                                (Null makeTypeInfo))))))
                                             

testLetTuple :: Program Double
testLetTuple = Program [] [] (LetInmakeTypeInfo "x" (PlusF makeTypeInfo (ThetaI makeTypeInfo 0) (Normal makeTypeInfo))
                                              (Cons makeTypeInfo (Var makeTypeInfo "x") 
                                                (Cons makeTypeInfo 
                                                  (PlusF makeTypeInfo (Normal makeTypeInfo)(Var makeTypeInfo "x")) 
                                                  (Null makeTypeInfo))))

testNormal :: Program Double
testNormal = Program [] [] (Normal makeTypeInfo)

--testLetE :: Expr Double
--testLetE = LetIn makeTypeInfo "x" (Normal makeTypeInfo) (InjF makeTypeInfo "plus" [Constant makeTypeInfo (VFloat 3.0)] (Var makeTypeInfo "x"))
testPlusProg :: Program Float
testPlusProg = Program [("main", IfThenElse makeTypeInfo
                                                   (GreaterThan makeTypeInfo (ThetaI makeTypeInfo 1)(ThetaI makeTypeInfo 1))
                                                   (ThetaI makeTypeInfo 1)
                                                   (PlusF makeTypeInfo (ThetaI makeTypeInfo 1) (Call makeTypeInfo "main")))]
                             (Call makeTypeInfo "main")

testPlus :: Expr makeTypeInfo a
testPlus = IfThenElse makeTypeInfo
             (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
             (Null makeTypeInfo)
             (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Null makeTypeInfo))

testPlus2 :: Program a
testPlus2 = Program [] [] (PlusF makeTypeInfo (MultF makeTypeInfo (ThetaI makeTypeInfo 0) (Uniform makeTypeInfo)) (ThetaI makeTypeInfo 1))


testGreater :: Expr makeTypeInfo a
testGreater = GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0)

testGreater2 :: Expr Float
testGreater2 = GreaterThan makeTypeInfo (ThetaI makeTypeInfo 0) (Uniform makeTypeInfo)

testExpr2 :: Expr makeTypeInfo a
testExpr2 = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Null makeTypeInfo)
  (Cons makeTypeInfo (Constant makeTypeInfo (VBool True)) (Call makeTypeInfo "main"))

testBool :: Expr makeTypeInfo a
testBool = GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0)

testGauss :: Expr makeTypeInfo a
testGauss = PlusF makeTypeInfo (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 0)) (ThetaI makeTypeInfo 1)


--  (IfThenElse makeTypeInfo
--    (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 1))
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
testGaussianMixture :: Expr makeTypeInfo a
testGaussianMixture = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 1))
      (ThetaI makeTypeInfo 2))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 3))
        (ThetaI makeTypeInfo 4))
      (Null makeTypeInfo)))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 5))
      (ThetaI makeTypeInfo 6))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 7))
        (ThetaI makeTypeInfo 8))
      (Null makeTypeInfo)))

gaussianMixture :: Expr makeTypeInfo a
gaussianMixture = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 1))
      (ThetaI makeTypeInfo 2))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 3))
        (ThetaI makeTypeInfo 4))
      (Cons makeTypeInfo
        (Constant makeTypeInfo (VBool True))
        (Null makeTypeInfo))))
  (Cons makeTypeInfo
    (PlusF makeTypeInfo
      (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 5))
      (ThetaI makeTypeInfo 6))
    (Cons makeTypeInfo
      (PlusF makeTypeInfo
        (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 7))
        (ThetaI makeTypeInfo 8))
      (Cons makeTypeInfo
        (Constant makeTypeInfo (VBool True))
        (Null makeTypeInfo))))

testIntractable :: Expr makeTypeInfo a
testIntractable = MultF makeTypeInfo
  (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 1))
  (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 2))

testInconsistent :: Expr Double
testInconsistent = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Constant makeTypeInfo (VFloat 0.0)) (ThetaI makeTypeInfo 0))
  (Constant makeTypeInfo (VBool True))
  (Constant makeTypeInfo (VBool False))

failureCase :: Expr makeTypeInfo a
failureCase = MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 0)

gaussLists :: Expr makeTypeInfo a
gaussLists = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0))
  (Null makeTypeInfo)
  (Cons makeTypeInfo (PlusF makeTypeInfo (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 1)) (ThetaI makeTypeInfo 2)) (Call makeTypeInfo "main"))
  
gaussMultiLists :: Expr makeTypeInfo a
gaussMultiLists = IfThenElse makeTypeInfo
  (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0) )
  (Null makeTypeInfo)
  (Cons makeTypeInfo
    (IfThenElse makeTypeInfo
      (GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 1))
      (PlusF makeTypeInfo (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 2)) (ThetaI makeTypeInfo 3))
      (PlusF makeTypeInfo (MultF makeTypeInfo (Normal makeTypeInfo) (ThetaI makeTypeInfo 4)) (ThetaI makeTypeInfo 5)))
    (Call makeTypeInfo "main"))

-- typeinfer :: Expr makeTypeInfo a -> Expr RType a
-- typeInferMaybe :: Expr (Maybe RType) a -> Expr RType a

testNNUntyped :: Expr makeTypeInfo a
--testNN : Lambda im1 -> (Lambda im2 -> readNN im1 + readNN im2)
testNNUntyped = Lambda makeTypeInfo "im1" (Lambda makeTypeInfo "im2" (PlusI makeTypeInfo (ReadNN makeTypeInfo "classifyMNist" (Var makeTypeInfo "im1")) (ReadNN makeTypeInfo "classifyMNist" (Var makeTypeInfo "im2"))))
{-
testNN :: Expr a
testNN = Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol TInt)) Bottom) "im1"
  (Lambda (TypeInfo (TArrow TSymbol TInt) Bottom) "im2" (PlusI (TypeInfo TInt Integrate)
    (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
    (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2"))))
    

mNistNoise :: Expr a
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

triMNist :: Expr a
triMNist = Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol (TArrow TSymbol TInt))) Bottom) "im1"
  (Lambda (TypeInfo (TArrow TSymbol (TArrow TSymbol TInt)) Bottom) "im2"
    (Lambda (TypeInfo (TArrow TSymbol TInt) Bottom) "im3" (PlusI (TypeInfo TInt Integrate)
      (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im3"))
      (PlusI (TypeInfo TInt Integrate)
        (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im1"))
        (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im2")))
      )))

expertModels :: Expr makeTypeInfo a
expertModels = Lambda makeTypeInfo "im" (IfThenElse makeTypeInfo
  (ReadNN makeTypeInfo "isMnist" (Var makeTypeInfo "im"))
  (ReadNN makeTypeInfo "classifyMNist" (Var makeTypeInfo "im"))
  (ReadNN makeTypeInfo "classifyCIFAR" (Var makeTypeInfo "im")))

expertModelsTyped :: Expr a
expertModelsTyped = Lambda (TypeInfo (TArrow TSymbol TInt) Integrate) "im" (IfThenElse (TypeInfo TInt Integrate)
  (ReadNN (TypeInfo TBool Integrate) "isMnist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (ReadNN (TypeInfo TInt Integrate) "classifyCIFAR" (Var (TypeInfo TSymbol Deterministic) "im")))

expertAnnotated :: Expr makeTypeInfo a
expertAnnotated = Lambda makeTypeInfo "im" (IfThenElse makeTypeInfo
  (ReadNN makeTypeInfo "isMnist" (Var makeTypeInfo "im"))
  (Cons makeTypeInfo (Constant makeTypeInfo (VInt 1)) (Cons makeTypeInfo (ReadNN makeTypeInfo "classifyMNist" (Var makeTypeInfo "im")) (Null makeTypeInfo)))
  (Cons makeTypeInfo (Constant makeTypeInfo (VInt 2)) (Cons makeTypeInfo (ReadNN makeTypeInfo "classifyCIFAR" (Var makeTypeInfo "im")) (Null makeTypeInfo))))

expertAnnotatedTyped :: Expr a
expertAnnotatedTyped = Lambda (TypeInfo (TArrow TSymbol (SPLL.Typing.RType.ListOf TInt)) Integrate) "im" (IfThenElse (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate)
  (ReadNN (TypeInfo TBool Integrate) "isMnist" (Var (TypeInfo TSymbol Deterministic) "im"))
  (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (Constant (TypeInfo TInt Deterministic) (VInt 1)) (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (ReadNN (TypeInfo TInt Integrate) "classifyMNist" (Var (TypeInfo TSymbol Deterministic) "im")) (Null (TypeInfo (SPLL.Typing.RType.ListOf TInt) Deterministic))))
  (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (Constant (TypeInfo TInt Deterministic) (VInt 2)) (Cons (TypeInfo (SPLL.Typing.RType.ListOf TInt) Integrate) (ReadNN (TypeInfo TInt Integrate) "classifyCIFAR" (Var (TypeInfo TSymbol Deterministic) "im")) (Null (TypeInfo (SPLL.Typing.RType.ListOf TInt) Deterministic)))))
-}
compilationExample :: Expr makeTypeInfo a
compilationExample = GreaterThan makeTypeInfo (Uniform makeTypeInfo) (ThetaI makeTypeInfo 0)

--expert_model_proofs image =
--  if isMNist
--    then (1, classifyMNist image)
--    else (2, classifyCIFAR image)

--expert_model image =
--  if is28x28x1 image
--    then classifyMNist image
--    else classifyCIFAR image
-}
