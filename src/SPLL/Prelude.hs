module SPLL.Prelude where

import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo, GenericValue (..), CompilerError, InjFName(..))
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Validator (validateProgram)
import IRInterpreter (generateRand, generateDet)
import Control.Monad.Random (Rand, RandomGen)
import SPLL.IRCompiler
import SPLL.IROptimizer (optimizeEnv)
import Debug.Trace
import Data.Either
import SPLL.Typing.ForwardChaining (annotateProg)
import Text.PrettyPrint.Annotated.HughesPJClass
import PrettyPrint (pPrintProg, pPrintIREnv)
import Debug.Pretty.Simple
import Data.Maybe (fromJust, isJust)

-- Flow control
ifThenElse :: Expr -> Expr -> Expr -> Expr
ifThenElse = IfThenElse makeTypeInfo

injF :: String -> [Expr] -> Expr
injF name = InjF makeTypeInfo (Named name)

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
(#<->#) a b = a #<+># negIF b

negF :: Expr -> Expr
negF x = injF "neg" [x]

negIF :: Expr -> Expr
negIF x = injF "negI" [x]

recipF :: Expr -> Expr
recipF x = injF "recip" [x]

expF :: Expr -> Expr
expF x = injF "exp" [x]

-- Variables

letIn :: String -> Expr -> Expr -> Expr
--letIn = LetIn makeTypeInfo
-- We can not infer probabilities on letIns. So we rewrite them as lambdas
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

isNull :: Expr -> Expr
isNull e = injF "isNull" [e]

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

-- Unit type

unit :: Expr
unit = Constant makeTypeInfo VUnit

-- Sum types

left :: Expr -> Expr
left x = injF "left" [x]

right :: Expr -> Expr
right x = injF "right" [x]

-- observe x pred: returns Left x if pred x, else Right ()
observe :: Expr -> Expr -> Expr
observe x pred = ifThenElse (apply pred x) (left x) (right unit)

sisLeft :: Expr -> Expr
sisLeft x = injF "isLeft" [x]

sisRight :: Expr -> Expr
sisRight x = injF "isRight" [x]

sfromLeft :: Expr -> Expr
sfromLeft x = injF "fromLeft" [x]

sfromRight :: Expr -> Expr
sfromRight x = injF "fromRight" [x]

-- Boolean Algebra
(#==#) :: Expr -> Expr -> Expr
(#==#) a b = injF "eq" [a, b]

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


compile :: CompilerConfig -> Program -> Either CompilerError IREnv
compile conf p = do
  validateProgram p
  printIfVerbose conf "=== Parsed Program ==="
  pPrintIfMoreVerbose conf p
  printIfVerbose conf (pPrintProg p)
  printStage conf "After Parsing (no annotations)" p

  let preAnnotated = annotateEnumsProg p
  printIfMoreVerbose conf "\n=== Annotated Program (1) ==="
  pPrintIfMoreVerbose conf preAnnotated
  printStage conf "After Enum Annotation" preAnnotated

  let forwardChained = annotateProg preAnnotated
  printIfMoreVerbose conf "\n=== Chain named Program ==="
  pPrintIfMoreVerbose conf forwardChained
  printStage conf "After Forward Chaining (chain names)" forwardChained

  typed <- addTypeInfo forwardChained
  printIfMoreVerbose conf "\n=== Typed Program ==="
  pPrintIfMoreVerbose conf typed
  printStage conf "After Type Inference (RType + PType)" typed

  let annotated = (annotateAlgsProg . annotateConditionalProg) typed
  printIfMoreVerbose conf "\n=== Annotated Program (2) ==="
  pPrintIfMoreVerbose conf annotated
  printStage conf "After Algorithm Annotation (tags include Alg)" annotated

  let unoptimized = envToIRUnoptimized conf annotated
  printStageIR conf "After IR Compilation (pre-optimization)" unoptimized
  let stripped = if countBranches conf then unoptimized else stripBranchCount unoptimized

  let compiled = optimizeEnv conf stripped
  printIfVerbose conf "\n=== Compiled Program ==="
  pPrintIfMoreVerbose conf compiled
  printIfVerbose conf (pPrintIREnv compiled)
  printStageIR conf "After Optimization" compiled
  return compiled

runGen :: (RandomGen g) => CompilerConfig -> Program -> [IRValue] -> Either CompilerError (Rand g IRValue)
runGen _ p _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runGen conf p args = do
  compiled <- compile conf p
  let Just (gen, _) = genFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst args
  Right $ generateRand (neurals p) compiled constArgs gen

runProb :: CompilerConfig -> Program -> [IRValue] -> IRValue -> Either CompilerError IRValue
runProb _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runProb conf p args x = do
  compiled <- compile conf p
  let Just (prob, _) = probFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst (x:args)
  generateDet (neurals p) compiled constArgs prob

runInteg :: CompilerConfig -> Program -> [IRValue] -> IRValue -> Either CompilerError IRValue
runInteg _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runInteg conf p args sample = do
  compiled <- compile conf p
  let Just (integ, _) = integFun (lookupIREnv "main" compiled)
  let constArgs = map IRConst (sample:args)
  generateDet (neurals p) compiled constArgs integ

-- | Run the encode function for the first neural declaration in the program.
-- outerArgs mirrors main's outer parameter list: pass one IRValue per outer lambda in main,
-- or an empty list for closed-form programs with no outer parameters.
runEncode :: CompilerConfig -> Program -> [IRValue] -> Either CompilerError IRValue
runEncode _ p _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runEncode conf p outerArgs = do
  compiled <- compile conf p
  let IREnv groups _ _ = compiled
  case filter (isJust . encodeFun) groups of
    [] -> Left "No encode function found in compiled program"
    (grp:_) ->
      let Just (enc, _) = encodeFun grp
          constArgs = map IRConst outerArgs
      in generateDet (neurals p) compiled constArgs enc

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

-- Print a labeled intermediate compilation stage showing the full annotated AST tree.
-- Each node shows: constructor name :: TypeInfo {rType, pType, chainName, tags=[..., Alg ...]}
printStage :: (Monad m) => CompilerConfig -> String -> Program -> m ()
printStage CompilerConfig {showIntermediates=True} label prog =
  trace (unlines (stageHeader label ++ prettyPrintProg prog ++ [""])) (return ())
printStage _ _ _ = return ()

printStageIR :: (Monad m) => CompilerConfig -> String -> IREnv -> m ()
printStageIR CompilerConfig {showIntermediates=True} label ir =
  trace (unlines (stageHeader label ++ lines (pPrintIREnv ir) ++ [""])) (return ())
printStageIR _ _ _ = return ()

stageHeader :: String -> [String]
stageHeader label =
  [ replicate (length decorated) '='
  , decorated
  , replicate (length decorated) '='
  ]
  where decorated = "=== " ++ label ++ " ==="