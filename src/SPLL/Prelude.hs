module SPLL.Prelude where

import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo, GenericValue (..))

-- Flow control
ifThenElse :: Expr -> Expr -> Expr -> Expr
ifThenElse = IfThenElse makeTypeInfo

injF :: String -> [Expr] -> Expr
injF = InjF makeTypeInfo

--Arithmetic

(#*#) :: Expr -> Expr -> Expr
(#*#) = MultF makeTypeInfo

(#+#) :: Expr -> Expr -> Expr
(#+#) = PlusF makeTypeInfo

(#-#) :: Expr -> Expr -> Expr
(#-#) a b = a #+# (neg b)

(#<*>#) :: Expr -> Expr -> Expr
(#<*>#) = MultI makeTypeInfo

(#<+>#) :: Expr -> Expr -> Expr
(#<+>#) = PlusI makeTypeInfo

(#<->#) :: Expr -> Expr -> Expr
(#<->#) a b = undefined

neg :: Expr -> Expr
neg = NegF makeTypeInfo

-- Variables

letIn :: String -> Expr -> Expr -> Expr
--letIn = LetIn makeTypeInfo
-- We can not infer probabilities on letIns. So we rewrite them as lambdas
-- We don't have full inference logic on lambdas yet, but we have none at all on LetIns
letIn s val body = apply (s #-># body) val

var :: String -> Expr
var = Var makeTypeInfo

constF :: Double -> Expr
constF = Constant makeTypeInfo . VFloat

constI :: Int -> Expr
constI = Constant makeTypeInfo . VInt

constB :: Bool -> Expr
constB = Constant makeTypeInfo . VBool

constL :: [Value] -> Expr
constL = Constant makeTypeInfo . VList

(#->#) :: String -> Expr -> Expr
(#->#) = Lambda makeTypeInfo

apply :: Expr -> Expr -> Expr
apply = Apply makeTypeInfo

-- Distributions

uniform :: Expr
uniform = Uniform makeTypeInfo

normal :: Expr
normal = Normal makeTypeInfo

bernoulli :: Double -> Expr
bernoulli p = uniform #<# constF p

binomial :: Int -> Double -> Expr
binomial n p = ifThenElse (bernoulli p) (constI 1) (constI 1) #+# binomial (n-1) p

dice :: Int -> Expr
dice 1 = constI 1
dice sides = ifThenElse (bernoulli (1/fromIntegral sides)) (constI sides)  (dice (sides-1))

-- Parameters

theta :: Expr -> Int -> Expr
theta = ThetaI makeTypeInfo

subtree :: Expr -> Int -> Expr
subtree = ThetaI makeTypeInfo

-- Product Types

cons :: Expr -> Expr -> Expr
cons = Cons makeTypeInfo

(#:#) :: Expr -> Expr -> Expr
(#:#) = cons

nul :: Expr
nul = Null makeTypeInfo

tuple :: Expr -> Expr -> Expr
tuple = TCons makeTypeInfo

-- Boolean Algebra

(#>#) :: Expr -> Expr -> Expr
(#>#) = GreaterThan makeTypeInfo

(#<#) :: Expr -> Expr -> Expr
(#<#) = LessThan makeTypeInfo

(#&&#) :: Expr -> Expr -> Expr
(#&&#) = And makeTypeInfo

(#||#) :: Expr -> Expr -> Expr
(#||#) = Or makeTypeInfo

(#!#) :: Expr -> Expr
(#!#) = Not makeTypeInfo

-- Other

-- This is a Z-Combinator
-- TODO: Our typesystem is not ready for that yet 
fix :: Expr
fix = "f" #->#
  apply ("u" #-># apply (var "f") ("n" #-># apply (apply (var "u") (var "u")) (var "n")))
    ("v" #-># apply (var "f") ("n" #-># apply (apply (var "v") (var "v")) (var "n")))


