module SPLL.CodeGen (

) where

import SPLL.Lang
import SPLL.Typing.PType
import SPLL.Typing.RType
import SPLL.Typing.Typing
import Interpreter
import SPLL.Transpiler
import Data.Graph
import Control.Monad.Supply
import Control.Monad.Identity (runIdentity)
import Data.List (intersperse, intercalate)

type Varname = String

{-
data ComputationGraph = Bind String ComputationGraph ComputationGraph
                      | CGAdd ComputationGraph ComputationGraph
                      | CGSub ComputationGraph ComputationGraph
                      | CGMult ComputationGraph ComputationGraph
                      | CGDiv ComputationGraph ComputationGraph
-}

--TODO: Let's use this space to outline a proper architecture for the compiler.
--So we can probably use Lang as a starting point. The Expr type has been around a bit and I'm confident it'll stay.
-- We can strap a better frontend on it when we want.
--So, what do we do with that code?
-- Currently, we sit at Expr () a
--1: type check.
--  Now at Expr TypeInfo a , where a is (RType, PType).
--  Ideally, we instead would capture tags such as [Integrable, Deterministic, Enumerable], but that's bijective.
--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.
--4: Produce target language code from the above or interpret the above.

mkProbability :: Show a => IRDefinition a -> String
mkProbability (name, iRtree) = "function probability_" ++ name ++ "(" ++ intercalate ", " (["sample", "theta"] ++ argNames) ++ ")\n" ++ unlines (indentOnce body) ++ "end\n"
  where
    body = runSupplyVars (mkProbabilityBody "sample" "outProb" strippedTree) ++ ["return outProb"]
    (argNames, strippedTree) = unwrapLambdas iRtree

--take all leading lambda expressions and extract the bound identifiers. That is, convert x = \y -> \z -> w into x' = ([y,z], w)
--From getSubExprs :: Expr -> [Expr], we know that Lambda only ever gets one child node, thus [rest] is a nonrestrictive pattern.
unwrapLambdas :: Tree (IRNode a) -> ([String], Tree (IRNode a))
unwrapLambdas (Node (Simple StubLambda [IIdentifier name]) [rest]) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

runSupplyVars :: Supply Int a -> a
runSupplyVars codeGen = runSupply codeGen (+1) 1

mkVariable :: String -> Supply Int Varname
mkVariable suffix = do
  varID <- demand
  return ("l_" ++ show varID ++ "_" ++ suffix)

--We can also change the approach here to first boil down to another IR that directly maps to instructions.
mkProbabilityBody :: (Show a) => String -> String -> Tree (IRNode a) -> Supply Int [String]
mkProbabilityBody sample_name out_name (Node (Complex (Algorithm StubMultF _ "multRight" _)) [rng, det]) = do
  detSample <- mkVariable "detSample"
  l_inverse <- mkVariable "inverse"
  inverse_p <- mkVariable "inverse_p"
  --let l1 = varname1 ++ " = do"
  boxed <- mkDetGenerate detSample det
  --let l3 = "end"
  let l4 = l_inverse ++ " = " ++ sample_name ++ " / " ++ detSample
  boxed2 <- mkProbabilityBody l_inverse inverse_p rng
  let l5 = out_name ++ " = " ++ inverse_p ++ " / " ++ detSample
  return (boxed ++ [l4] ++ boxed2 ++ [l5])
  --inverse / (det sample)
mkProbabilityBody sample_name out_name (Node (Complex (Algorithm StubPlusF _ "plusRight" _ )) [rng, det]) = do
  detSample <- mkVariable "detSaple"
  l_inverse <- mkVariable "inverse"
  boxed <- mkDetGenerate detSample det
  let l4 = l_inverse ++ " = " ++ sample_name ++ " - " ++ detSample
  boxed2 <- mkProbabilityBody l_inverse out_name rng
  return (boxed ++ [l4] ++ boxed2)
mkProbabilityBody sample_name out_name (Node (Complex (Algorithm StubPlusI _ "enumeratePlusLeft" _)) [nodeEnum, otherSide]) = do
  loop_Counter <- mkVariable "loop_Counter"
  loop_Enum <- mkVariable "loop_Enum"
  inverse <- mkVariable "inverse"
  --TODO: Fix the enum range to be not so MNist-Specific
  let enumRange = "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"
  let l1 = loop_Counter ++ " = 0.0"
  let l2 = "for " ++ loop_Enum ++ " in " ++ enumRange
  let l3 = inverse ++ " = " ++ sample_name ++ " - " ++ loop_Enum
  let l34 = "if " ++ inverse ++ " in " ++ enumRange
  pEnum <- mkVariable "pEnum"
  box1 <- mkProbabilityBody loop_Enum pEnum nodeEnum
  pOtherSide <- mkVariable "pOtherSide"
  box2 <- mkProbabilityBody inverse pOtherSide otherSide
  let l4 = loop_Counter ++ " = " ++ loop_Counter ++ " + (" ++ pEnum ++ " * " ++ pOtherSide ++ ")"
  let lEnd1 = "end"
  let lEnd = "end"
  let lRet = out_name ++ " = " ++ loop_Counter
  return ([l1, l2] ++ indentOnce ([l3, l34] ++ (indentOnce (box1 ++ box2 ++ [l4])) ++ [lEnd1]) ++ [lEnd, lRet])
mkProbabilityBody sample_name out_name (Node (Simple StubNormal []) []) = do
  let l1 = out_name ++ " = (1 / sqrt(2 * pi)) * exp(-0.5 * " ++ sample_name ++ " * " ++ sample_name ++ ")"
  return [l1]
mkProbabilityBody sample_name out_name (Node (Simple StubReadNN []) [arg]) = do
  nnInput <- mkVariable "nnInput"
  box1 <- mkDetGenerate nnInput arg
  --TODO: encountering a currently-unencoded constraint that the NN input must be deterministic.
  --TODO: Also, the index magic below is kind of assumption-driven.
  let l2 = out_name ++ " = reader(" ++ nnInput ++ ")[" ++ sample_name ++ " + 1]"
  return (box1 ++ [l2])
mkProbabilityBody sample_name out_name n@(Node ir subelems) = do
  --Do not debug-display the subexpressions, as we don't know whether we need det or prob
  -- prevs <- mapM (mkProbabilityBody sample_name out_name) subelems
  return ["PROB:unknown how to deal with " ++ show ir]

indentOnce :: [String] -> [String]
indentOnce = map ("  " ++)

mkDetGenerate :: (Show a) => String -> Tree (IRNode a) -> Supply Int [String]
mkDetGenerate out_name n@(Node (Simple StubThetaI [IIndex i]) []) = do
  let l1 = out_name ++ " = theta[" ++ show (i+1) ++ "]"
  return [l1]
mkDetGenerate out_name (Node (Simple StubCall [IIdentifier ident]) []) = do
  let l1 = out_name ++ " = " ++ ident
  return [l1]
mkDetGenerate out_name (Node (Simple StubCall [IIdentifier ident]) args) = do
  argVars <- replicateM (length args) (mkVariable "arg")
  boxes <- mapM (\(arg, argVar) -> mkDetGenerate argVar arg) (zip args argVars)
  let l1 = out_name ++ " = " ++ ident ++ "(" ++ (intercalate ", " argVars) ++ ")"
  return (concat boxes ++ [l1])
mkDetGenerate out_name n@(Node ir subelems) = do
  prevs <- mapM (mkDetGenerate "") subelems
  return (concat prevs ++ ["DET: unknown how to deal with " ++ show ir])

mkIntegrate :: (Show a) => String-> Tree (IRNode a) -> Supply Int [String]
mkIntegrate sample_name n@(Node ir subelems) = do
  prevs <- mapM (mkIntegrate sample_name) subelems
  return (concat prevs ++ ["INT: unknown how to deal with " ++ show ir])
