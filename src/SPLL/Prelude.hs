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

(#<*>#) :: Expr -> Expr -> Expr
(#<*>#) = MultI makeTypeInfo

(#<+>#) :: Expr -> Expr -> Expr
(#<+>#) = PlusI makeTypeInfo

neg :: Expr -> Expr
neg = NegF makeTypeInfo

-- Variables

letIn :: String -> Expr -> Expr -> Expr
letIn = LetIn makeTypeInfo

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


