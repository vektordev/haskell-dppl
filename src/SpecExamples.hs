module SpecExamples where

import SPLL.Lang

import SPLL.Typing.RType
import SPLL.Typing.PType
import qualified Data.Set as Set

variableLengthS :: Program  () Double
variableLengthS = Program [("b", IfThenElse ()
                          (GreaterThan () (Uniform ()) (ThetaI () 0))
                          (Null ())
                          (Cons () (Constant () (VBool True)) (Call () "b")))]
                  (Call () "b")
variableLengthT :: Program TypeInfoWit Double
variableLengthT = Program [("b", IfThenElse (TypeInfoWit (ListOf TBool) Integrate Set.empty)
                            (GreaterThan (TypeInfoWit TBool Integrate Set.empty)
                              (Uniform (TypeInfoWit TFloat Integrate Set.empty))
                              (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0))
                            (Null (TypeInfoWit NullList Deterministic Set.empty))
                            (Cons (TypeInfoWit (ListOf TBool) Integrate Set.empty)
                             (Constant (TypeInfoWit TBool Deterministic Set.empty) (VBool True))
                             (Call (TypeInfoWit (ListOf TBool) Integrate Set.empty)  "b")))]
                  (Call (TypeInfoWit (ListOf TBool) Integrate Set.empty) "b")

testLetS :: Program () Double
testLetS = Program [](LetIn () "x"
                      (PlusF () (ThetaI () 0) (Normal ()))
                      (InjF () "sig" [] (InjF () "mult" [ThetaI () 1]  (Var () "x"))))
-- let x = theta + normal in sig(theta1 * x)
testLetT :: Program TypeInfoWit Double
testLetT = Program [](LetIn (TypeInfoWit TFloat Deterministic Set.empty) "x"
                      (PlusF (TypeInfoWit TFloat Integrate Set.empty)
                        (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0)
                        (Normal (TypeInfoWit TFloat Integrate Set.empty)))
                      (InjF (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "sig" []
                        (InjF (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "mult"
                          [ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 1]
                          (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x"))))

testLetNonLetS :: Program () Double
testLetNonLetS = Program [] (LetIn () "x" (PlusF () (ThetaI () 0) (Normal ()))
          (PlusF () (InjF () "sig" [] (Var () "x")) (Uniform ())))

testLetNonLetT :: Program TypeInfoWit Double
testLetNonLetT = Program [] (LetIn (TypeInfoWit TFloat Bottom Set.empty) "x"
           (PlusF (TypeInfoWit TFloat Integrate Set.empty)
            (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0)
            (Normal (TypeInfoWit TFloat Integrate Set.empty)))
           (PlusF (TypeInfoWit TFloat Integrate Set.empty)
              (InjF (TypeInfoWit TFloat Deterministic (Set.singleton "x"))  "sig" []
                (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x"))
              (Uniform (TypeInfoWit TFloat Integrate Set.empty))))

testLetDS :: Program () Double
testLetDS = Program [] (LetIn () "x" (PlusF () (ThetaI () 0) (Constant () (VFloat 3.0)))
           (PlusF () (InjF () "sig" [] (Var () "x")) (Normal ())))
           
testLetDT :: Program TypeInfoWit Double
testLetDT = Program [] (LetIn (TypeInfoWit TFloat Integrate Set.empty) "x"
           (PlusF (TypeInfoWit TFloat Deterministic Set.empty)
            (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0)
             (Constant (TypeInfoWit TFloat Deterministic Set.empty) (VFloat 3.0)))
           (PlusF (TypeInfoWit TFloat Integrate Set.empty)
              (InjF (TypeInfoWit TFloat Deterministic (Set.singleton "x"))  "sig" []
                (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x"))
              (Normal (TypeInfoWit TFloat Integrate Set.empty))))

testLetTupleS :: Program () Double
testLetTupleS = Program [] (LetIn() "x" (PlusF () (ThetaI () 0) (Normal ()))
                                              (Cons () (Var () "x") 
                                                (Cons () 
                                                  (PlusF () (Normal ())(Var () "x")) 
                                                  (Null ()))))
testLetTupleT :: Program TypeInfoWit Double
testLetTupleT = Program [] 
  (LetIn (TypeInfoWit (ListOf TFloat) Integrate Set.empty)   "x" 
    (PlusF (TypeInfoWit TFloat Integrate Set.empty)
      (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0) 
      (Normal (TypeInfoWit TFloat Integrate Set.empty) ))
    (Cons (TypeInfoWit (ListOf TFloat) Integrate (Set.singleton "x"))  
      (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x") 
      (Cons (TypeInfoWit (ListOf TFloat) Integrate Set.empty) 
        (PlusF (TypeInfoWit TFloat Integrate Set.empty) 
          (Normal (TypeInfoWit TFloat Integrate Set.empty))
          (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x")) 
        (Null (TypeInfoWit NullList Deterministic Set.empty)))))
        
        
testLetXYS :: Program () Double
testLetXYS = Program [] (LetIn() "x" (PlusF () (ThetaI () 0) (Normal ()))
                          (LetIn ()  "y" (PlusF () (ThetaI () 1) (Normal ()))
                                         (Cons () (Var () "x") 
                                           (Cons () 
                                             (Var () "y")
                                             (Cons () 
                                                (MultF () (PlusF () (Normal ())(Var () "x")) (Var () "y"))
                                                (Null ()))))))
                                                
-- Let x = theta0 + normal in let y = theta1 + normal in [x, y, y * (x + normal)]
testLetXYT :: Program TypeInfoWit Double
testLetXYT = Program [] (LetIn (TypeInfoWit (ListOf TFloat) Integrate Set.empty) "x"
                            (PlusF (TypeInfoWit TFloat Integrate Set.empty) 
                                (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 0) 
                                (Normal (TypeInfoWit TFloat Integrate Set.empty)))
                          (LetIn (TypeInfoWit (ListOf TFloat) Integrate (Set.singleton "x")) "y" 
                                 (PlusF (TypeInfoWit TFloat Integrate Set.empty) 
                                    (ThetaI (TypeInfoWit TFloat Deterministic Set.empty) 1) 
                                    (Normal (TypeInfoWit TFloat Integrate Set.empty)))
                                 (Cons (TypeInfoWit (ListOf TFloat) Integrate (Set.fromList ["x", "y"])) 
                                   (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x") 
                                   (Cons (TypeInfoWit (ListOf TFloat) Integrate (Set.singleton "y")) 
                                     (Var (TypeInfoWit TFloat Deterministic (Set.singleton "y")) "y")
                                     (Cons (TypeInfoWit (ListOf TFloat) Integrate Set.empty)
                                        (MultF (TypeInfoWit TFloat Integrate Set.empty) 
                                           (PlusF (TypeInfoWit TFloat Integrate Set.empty)
                                              (Normal (TypeInfoWit TFloat Integrate Set.empty))
                                              (Var (TypeInfoWit TFloat Deterministic (Set.singleton "x")) "x")) 
                                           (Var (TypeInfoWit TFloat Deterministic (Set.singleton "y")) "y"))
                                        (Null (TypeInfoWit NullList Deterministic Set.empty)))))))
                                     