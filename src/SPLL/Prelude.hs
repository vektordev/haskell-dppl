module SPLL.Prelude where

import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo, GenericValue (..))
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Validator (validateProgram)
import IRInterpreter (generateRand, generateDet)
import Control.Monad.Random (Rand, RandomGen)
import SPLL.IRCompiler
import Debug.Trace
import Data.Either
import SPLL.Typing.ForwardChaining (annotateProg)
import Text.PrettyPrint.Annotated.HughesPJClass
import PrettyPrint (pPrintProg, pPrintIREnv)
import Debug.Pretty.Simple

-- Flow control
ifThenElse :: Expr -> Expr -> Expr -> Expr
ifThenElse = IfThenElse makeTypeInfo

injF :: String -> [Expr] -> Expr
injF = InjF makeTypeInfo

--Arithmetic

(#*#) :: Expr -> Expr -> Expr
(#*#) a b = injF "mult" [a, b]
--(#*#) = MultF makeTypeInfo

(#/#) :: Expr -> Expr -> Expr
(#/#) a b = a #*# recipF b

(#+#) :: Expr -> Expr -> Expr
(#+#) a b = injF "plus" [a, b]
--(#+#) = PlusF makeTypeInfo

(#-#) :: Expr -> Expr -> Expr
(#-#) a b = a #+# negF b

(#<*>#) :: Expr -> Expr -> Expr
(#<*>#) a b = injF "multI" [a, b]

(#<+>#) :: Expr -> Expr -> Expr
(#<+>#) a b = injF "plusI" [a, b]

(#<->#) :: Expr -> Expr -> Expr
(#<->#) a b = undefined

negF :: Expr -> Expr
negF x = injF "neg" [x]

recipF :: Expr -> Expr
recipF x = injF "recip" [x]

expF :: Expr -> Expr
expF x = injF "exp" [x]

-- Variables

letIn :: String -> Expr -> Expr -> Expr
letIn = LetIn makeTypeInfo
-- We can not infer probabilities on letIns. So we rewrite them as lambdas
-- We don't have full inference logic on lambdas yet, but we have none at all on LetIns
--letIn s val body = apply (s #-># body) val

var :: String -> Expr
var = Var makeTypeInfo

constF :: Double -> Expr
constF = Constant makeTypeInfo . VFloat

constI :: Int -> Expr
constI = Constant makeTypeInfo . VInt

constB :: Bool -> Expr
constB = Constant makeTypeInfo . VBool

constL :: [Value] -> Expr
constL lst = Constant makeTypeInfo (constructVList lst)

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
subtree = Subtree makeTypeInfo

-- Product Types

cons :: Expr -> Expr -> Expr
cons = Cons makeTypeInfo

(#:#) :: Expr -> Expr -> Expr
(#:#) = cons

nul :: Expr
nul = Null makeTypeInfo

lhead :: Expr -> Expr
lhead x = injF "head" [x]

ltail :: Expr -> Expr
ltail x = injF "tail" [x]

tuple :: Expr -> Expr -> Expr
tuple = TCons makeTypeInfo

tfst :: Expr -> Expr
tfst x = injF "fst" [x]

tsnd :: Expr -> Expr
tsnd x = injF "snd" [x]

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

readNN :: String -> Expr -> Expr 
readNN = ReadNN makeTypeInfo

-- This is a Z-Combinator
-- TODO: Our typesystem is not ready for that yet 
fix :: Expr
fix = "f" #->#
  apply ("u" #-># apply (var "f") ("n" #-># apply (apply (var "u") (var "u")) (var "n")))
    ("v" #-># apply (var "f") ("n" #-># apply (apply (var "v") (var "v")) (var "n")))


compile :: CompilerConfig -> Program -> IREnv
compile _ p | isLeft (validateProgram p) = error $ fromLeft "" (validateProgram p)
compile conf p = do
  printIfVerbose conf "=== Parsed Program ==="
  pPrintIfMoreVerbose conf p
  printIfVerbose conf (pPrintProg p)

  let preAnnotated = annotateEnumsProg p
  printIfMoreVerbose conf "\n=== Annotated Program (1) ==="
  pPrintIfMoreVerbose conf preAnnotated

  let forwardChained = annotateProg preAnnotated
  printIfMoreVerbose conf "\n=== Chain named Program ==="
  pPrintIfMoreVerbose conf preAnnotated

  let typed = addTypeInfo forwardChained
  printIfMoreVerbose conf "\n=== Typed Program ==="
  pPrintIfMoreVerbose conf typed
  let annotated = annotateAlgsProg typed
  printIfMoreVerbose conf "\n=== Annotated Program (2) ==="
  pPrintIfMoreVerbose conf annotated

  let compiled = envToIR conf annotated
  printIfVerbose conf "\n=== Compiled Program ==="
  pPrintIfMoreVerbose conf compiled
  printIfVerbose conf (pPrintIREnv compiled)
  compiled

runGen :: (RandomGen g) => CompilerConfig -> Program -> [IRValue] -> Rand g IRValue
runGen _ p _ | isLeft (validateProgram p) = error $ fromLeft "" (validateProgram p)
runGen conf p args = do
  let compiled = compile conf p
  let (gen, _) = genFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst args
  generateRand (neurals p) compiled constArgs gen

runProb :: CompilerConfig -> Program -> [IRValue] -> IRValue -> IRValue
runProb _ p _ _ | isLeft (validateProgram p) = error $ fromLeft "" (validateProgram p)
runProb conf p args x = do
  let compiled = compile conf p
  let Just (prob, _) = probFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst (x:args)
  let val = generateDet (neurals p) compiled constArgs prob
  case val of
    Right v -> v
    Left err -> error err

runInteg :: CompilerConfig -> Program -> [IRValue] -> IRValue -> IRValue -> IRValue
runInteg _ p _ _ _ | isLeft (validateProgram p) = error $ fromLeft "" (validateProgram p)
runInteg conf p args low high = do
  let compiled = compile conf p
  let Just (integ, _) = integFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst (low:high:args)
  let val = generateDet (neurals p) compiled constArgs integ
  case val of
    Right v -> v
    Left err -> error err

printIfVerbose :: (Monad m) => CompilerConfig -> String -> m ()
printIfVerbose CompilerConfig {verbose=v} s | v >= 1 = trace s (return ())
printIfVerbose _ _ = return ()

printIfMoreVerbose :: (Monad m) => CompilerConfig -> String -> m ()
printIfMoreVerbose CompilerConfig {verbose=v} s | v >= 2 = trace s (return ())
printIfMoreVerbose _ _ = return ()

pPrintIfVerbose :: (Monad m, Show a) => CompilerConfig -> a -> m ()
pPrintIfVerbose CompilerConfig {verbose=v} s | v >= 1 = pTraceShow s (return ())
pPrintIfVerbose _ _ = return ()

pPrintIfMoreVerbose :: (Monad m, Show a) => CompilerConfig -> a -> m ()
pPrintIfMoreVerbose CompilerConfig {verbose=v} s | v >= 2 = pTraceShow s (return ())
pPrintIfMoreVerbose _ _ = return ()
