module SPLL.IntermediateRepresentation (
  IRExpr(..)
, StaticAnnotations(..)
, Tag(..)
, Operand(..)
, Distribution(..)
, toIRProbability
, toIRGenerate
, envToIR
) where

import Lang
import SPLL.Typing.RType
import SPLL.Typing.PType
import Transpiler
import SPLL.Analysis
import SPLL.Typing.Typing

data Operand = OpPlus | OpMult | OpGreaterThan | OpDiv | OpSub deriving (Show)

data Distribution = IRNormal | IRUniform deriving (Show)

data IRExpr a = IRIf (IRExpr a) (IRExpr a) (IRExpr a)
              | IROp Operand (IRExpr a) (IRExpr a)
              | IRTheta Int
              | IRConst (Value a)
              | IRCons (IRExpr a) (IRExpr a)
              | IRDensity Distribution (IRExpr a)
              | IRSample Distribution
              | IRLetIn String (IRExpr a) (IRExpr a)
              | IRVar String
              | IRLambda String (IRExpr a)
              deriving (Show)
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.

--TODO: sample here should be properly included in the structure somehow,
-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
envToIR :: (Fractional a, Show a) => Env (StaticAnnotations a) a -> [(String, IRExpr a)]
envToIR = concatMap (\(name, binding) -> [
  (name ++ "_prob", IRLambda "sample" (toIRProbability binding (IRVar "sample"))),
  (name ++ "_gen", toIRGenerate binding)])

hasAlgorithm :: [Tag a] -> Algorithm -> Bool
hasAlgorithm tags alg = alg `elem` ([a | Alg a <- tags])
--hasAlgorithm tags alg = not $ null $ filter (== alg) [a | Alg a <- tags]

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
toIRProbability :: (Fractional a, Show a) => Expr (StaticAnnotations a) a -> IRExpr a -> IRExpr a
toIRProbability (IfThenElse t cond left right) sample = IRLetIn "a" (toIRProbability cond (IRConst (VBool True)))
  (IROp OpPlus
    (IROp OpMult (IRVar "a") (toIRProbability left sample))
    (IROp OpMult (IROp OpPlus (IRConst $ VFloat (-1.0)) (IRVar "a")) (toIRProbability right sample)))
toIRProbability (Mult (StaticAnnotations TFloat _ extras) left right) sample
  | extras `hasAlgorithm` multLeft = IRLetIn "detGenP" (toIRGenerate left)
    (IROp OpDiv (toIRProbability right (IROp OpDiv sample (IRVar "detGenP"))) (IRVar "detGenP"))
  | extras `hasAlgorithm` multRight = IRLetIn "detGenP" (toIRGenerate right)
    (IROp OpDiv (toIRProbability left (IROp OpDiv sample (IRVar "detGenP"))) (IRVar "detGenP"))
toIRProbability (Plus (StaticAnnotations TFloat _ extras) left right) sample
  | extras `hasAlgorithm` plusLeft = IRLetIn "detGenP" (toIRGenerate left)
    (toIRProbability right (IROp OpSub sample (IRVar "detGenP")))
  | extras `hasAlgorithm` plusRight = IRLetIn "detGenP" (toIRGenerate right)
      (toIRProbability left (IROp OpSub sample (IRVar "detGenP")))
toIRProbability (Normal t) sample = IRDensity IRNormal sample
toIRProbability x sample = error ("found no way to convert to IR: " ++ show x)


--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: Expr (StaticAnnotations a) a -> IRExpr a
toIRGenerate (IfThenElse _ cond left right) = IRIf (toIRGenerate cond) (toIRGenerate left) (toIRGenerate right)
toIRGenerate (GreaterThan _ left right) = IROp OpGreaterThan (toIRGenerate left) (toIRGenerate right)
toIRGenerate (Plus _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (Mult _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (ThetaI _ ix) = IRTheta ix
toIRGenerate (Constant _ x) = IRConst x
toIRGenerate (Null _) = IRConst (VList [])
toIRGenerate (Cons _ hd tl) = IRCons (toIRGenerate hd) (toIRGenerate tl)
toIRGenerate (Uniform _) = IRSample IRUniform
toIRGenerate (Normal _) = IRSample IRNormal
--TODO: Lambda _ name expr, Call _ name, ReadNN _ expr
toIRGenerate _ = undefined