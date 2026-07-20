module SPLL.Prelude
  ( ifThenElse
  , injF
  , (#*#)
  , (#/#)
  , (#+#)
  , (#-#)
  , (#<*>#)
  , (#<+>#)
  , (#<->#)
  , negF
  , negIF
  , recipF
  , expF
  , letIn
  , var
  , constF
  , constI
  , constB
  , constL
  , (#->#)
  , apply
  , uniform
  , normal
  , bernoulli
  , binomial
  , dice
  , theta
  , subtree
  , cons
  , (#:#)
  , nul
  , isNull
  , lhead
  , ltail
  , tuple
  , tfst
  , tsnd
  , unit
  , left
  , right
  , observe
  , sisLeft
  , sisRight
  , sfromLeft
  , sfromRight
  , sfromLeftPartial
  , sfromRightPartial
  , (#==#)
  , (#>#)
  , (#<#)
  , (#&&#)
  , (#||#)
  , (#!#)
  , readNN
  , fix
  , compile
  , runGen
  , runProb
  , runInteg
  , runEncode
  , runGenC
  , runProbC
  , runIntegC
  , runGenNamedC
  , runProbNamedC
  , runIntegNamedC
  , runEncodeC
  , printIfVerbose
  , printIfMoreVerbose
  , pPrintIfVerbose
  , pPrintIfMoreVerbose
  , printStage
  , printStageIR
  ) where

import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo, GenericValue (..), CompilerError)
import SPLL.AutoNeural (validateEncodeGaussian)
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.Typing.Infer (addModalityInfo)
import SPLL.Typing.RInfer (addRTypeInfo)
import SPLL.Validator (validateProgram)
import IRInterpreter (generateRand, generateDet)
import Control.Monad.Random (Rand, RandomGen)
import SPLL.IRCompiler
import SPLL.IROptimizer (optimizeEnv)
import Debug.Trace
import Data.Either
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Typing.Determinism (knownAnchors)
import qualified Data.Set as Set
import Text.PrettyPrint.Annotated.HughesPJClass()
import PrettyPrint (pPrintProg, pPrintIREnv)
import Debug.Pretty.Simple
import Data.Maybe (isJust)
import Data.List (find)

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

-- Distributions are prelude primitives: nullary named leaves bound to a primitive
-- generator, represented as reserved-name Vars rather than dedicated constructors.
uniform :: Expr
uniform = Var makeTypeInfo "Uniform"

normal :: Expr
normal = Var makeTypeInfo "Normal"

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
cons h t = injF "Cons" [h, t]

(#:#) :: Expr -> Expr -> Expr
(#:#) = cons

nul :: Expr
nul = Constant makeTypeInfo (constructVList [])

isNull :: Expr -> Expr
isNull e = injF "isNull" [e]

lhead :: Expr -> Expr
lhead x = injF "head" [x]

ltail :: Expr -> Expr
ltail x = injF "tail" [x]

tuple :: Expr -> Expr -> Expr
tuple a b = injF "TCons" [a, b]

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

-- Partial (crash-on-mismatch) extractors, used only by the `let left a = ...`/
-- `let right b = ...` letIn-destructuring sugar (Parser.letInDestructor), which
-- is always guarded by construction (the pattern dictates which side is taken)
-- and is a distinct feature from the total, Maybe-returning `fromLeft`/`fromRight`.
sfromLeftPartial :: Expr -> Expr
sfromLeftPartial x = injF "fromLeftPartial" [x]

sfromRightPartial :: Expr -> Expr
sfromRightPartial x = injF "fromRightPartial" [x]

-- Boolean Algebra
(#==#) :: Expr -> Expr -> Expr
(#==#) a b = injF "eq" [a, b]

(#>#) :: Expr -> Expr -> Expr
(#>#) = GreaterThan makeTypeInfo

(#<#) :: Expr -> Expr -> Expr
(#<#) = LessThan makeTypeInfo

(#&&#) :: Expr -> Expr -> Expr
(#&&#) a b = injF "and" [a, b]

(#||#) :: Expr -> Expr -> Expr
(#||#) a b = injF "or" [a, b]

(#!#) :: Expr -> Expr
(#!#) x = InjF makeTypeInfo (Named "not") [x]

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

  -- RType inference now runs first, directly on the freshly parsed program --
  -- it needs no chain names or enum tags (SPLL.Typing.RInfer reads only the
  -- Expr shape and PredefinedFunctions' contracts). Running it here, rather
  -- than after enum annotation/forward chaining as before, means: (1) ill-typed
  -- programs (e.g. fromRightPartial applied to a non-Either value) are rejected
  -- before discretesTags forward-evaluates any InjF application and can hit a
  -- partial-function crash on genuinely ill-typed input; (2) every later pass
  -- -- enum annotation, forward chaining, the modality pass -- sees real RType
  -- instead of NotSetYet, in case any of them can make use of it.
  rtyped <- addRTypeInfo p
  printIfMoreVerbose conf "\n=== RType-inferred Program ==="
  pPrintIfMoreVerbose conf rtyped
  printStage conf "After RType Inference" rtyped

  let preAnnotated = annotateEnumsProg rtyped
  printIfMoreVerbose conf "\n=== Annotated Program (1) ==="
  pPrintIfMoreVerbose conf preAnnotated
  printStage conf "After Enum Annotation" preAnnotated

  let forwardChained = annotateProg preAnnotated
  printIfMoreVerbose conf "\n=== Chain named Program ==="
  pPrintIfMoreVerbose conf forwardChained
  printStage conf "After Forward Chaining (chain names)" forwardChained

  -- Stage 1 of the modality pipeline (modality-typesystem-port §4): the forward
  -- determinism dataflow whose known-anchor set ForwardChaining will consume in
  -- place of its Constant-only approximation (the wiring is milestone 3). It
  -- slots here, after chain naming and before the modality pass, per the §4 order.
  let anchors = knownAnchors forwardChained
  printIfMoreVerbose conf ("\n=== Determinism (known anchors) ===\n"
                            ++ unwords (Set.toList anchors))

  -- Stage 2 of the modality pipeline (modality-split-forwardchaining): the
  -- ForwardChaining certificate is built ONCE, inside addModalityInfo -- from
  -- the already-RType'd, chain-named program, feeding the modality pass, which
  -- consults its witnessed-binding verdict for the let rule
  -- (modality-witnessed-inference, milestone 2). The same FCData is returned
  -- here and threaded to both remaining consumers (conditional annotation and
  -- IR codegen).
  (typed, fcData) <- addModalityInfo forwardChained
  printIfMoreVerbose conf "\n=== Typed Program ==="
  pPrintIfMoreVerbose conf typed
  printStage conf "After Modality Inference (PType)" typed

  let annotated = annotateConditionalProg fcData typed
  printIfMoreVerbose conf "\n=== Annotated Program (2) ==="
  pPrintIfMoreVerbose conf annotated
  printStage conf "After Conditional Annotation (IsConditional tags)" annotated

  let unoptimized = envToIRUnoptimized conf fcData annotated
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
  Right $ runGenC p compiled args

runProb :: CompilerConfig -> Program -> [IRValue] -> IRValue -> Either CompilerError IRValue
runProb _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runProb conf p args x = do
  compiled <- compile conf p
  runProbC p compiled args x

runInteg :: CompilerConfig -> Program -> [IRValue] -> IRValue -> Either CompilerError IRValue
runInteg _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runInteg conf p args sample = do
  compiled <- compile conf p
  runIntegC p compiled args sample

-- | Run the encode function of the named function group (e.g. "decA_auto" for a
-- decoder declaration `decA :: Symbol -> ...`).
-- outerArgs mirrors main's outer parameter list: pass one IRValue per outer lambda in main,
-- or an empty list for closed-form programs with no outer parameters.
runEncode :: CompilerConfig -> Program -> String -> [IRValue] -> Either CompilerError IRValue
runEncode _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runEncode conf p target outerArgs = do
  compiled <- compile conf p
  runEncodeC p compiled target outerArgs

-- Variants of the run* functions that take an already-compiled IREnv, so that
-- callers issuing many queries against the same program pay for compilation once.

runGenC :: (RandomGen g) => Program -> IREnv -> [IRValue] -> Rand g IRValue
runGenC p compiled = runGenNamedC p compiled "main"

runProbC :: Program -> IREnv -> [IRValue] -> IRValue -> Either CompilerError IRValue
runProbC p compiled = runProbNamedC p compiled "main"

-- | Like 'runGenC'/'runProbC'/'runIntegC', but selects the compiled function
-- group by name instead of always using @main@. Every top-level definition is
-- compiled into its own 'IRFunGroup' keyed by its name, so these drive any
-- definition directly -- used by the showcase drift guard to freeze the
-- behaviour of individual documented definitions, not just @main@.
runGenNamedC :: (RandomGen g) => Program -> IREnv -> String -> [IRValue] -> Rand g IRValue
runGenNamedC p compiled name args =
  let Just (gen, _) = genFun (lookupIREnv name compiled)
  in generateRand (neurals p) (encodeDecls p) compiled (map IRConst args) gen

runProbNamedC :: Program -> IREnv -> String -> [IRValue] -> IRValue -> Either CompilerError IRValue
runProbNamedC p compiled name args x =
  let Just (prob, _) = probFun (lookupIREnv name compiled)
      -- topK-compiled prob functions take an accumulated-probability parameter
      -- right after the sample; seed it with 1.0 at the query root.
      args' = if compiledWithTopK compiled then x : VFloat 1.0 : args else x : args
  in generateDet (neurals p) (encodeDecls p) compiled (map IRConst args') prob

-- The IRCompiler emits the TOP_K_CUTOFF constant iff topKThreshold was set,
-- so a compiled IREnv carries its own marker for the extra acc_prob parameter.
compiledWithTopK :: IREnv -> Bool
compiledWithTopK (IREnv _ _ consts) = isJust (lookup "TOP_K_CUTOFF" consts)

runIntegC :: Program -> IREnv -> [IRValue] -> IRValue -> Either CompilerError IRValue
runIntegC p compiled = runIntegNamedC p compiled "main"

runIntegNamedC :: Program -> IREnv -> String -> [IRValue] -> IRValue -> Either CompilerError IRValue
runIntegNamedC p compiled name args sample =
  let Just (integ, _) = integFun (lookupIREnv name compiled)
  in generateDet (neurals p) (encodeDecls p) compiled (map IRConst (sample:args)) integ

-- | Run the encode function of the function group named `target`. Each decoder
-- declaration `name :: Symbol -> X` contributes a group `<name>_auto` whose encode
-- is independently scoped to that declaration's own target type, so the target name
-- selects which decoder's encode to run (rather than relying on declaration order).
runEncodeC :: Program -> IREnv -> String -> [IRValue] -> Either CompilerError IRValue
runEncodeC p compiled target outerArgs = do
  validateEncodeGaussian (adts p) (encodeDecls p) (neurals p) compiled
  let IREnv groups _ _ = compiled
  case find ((== target) . groupName) groups of
    Nothing  -> Left ("No function group named " ++ show target ++ " in compiled program")
    Just grp -> case encodeFun grp of
      Nothing       -> Left ("Function group " ++ show target ++ " has no encode function")
      Just (enc, _) -> generateDet (neurals p) (encodeDecls p) compiled (map IRConst outerArgs) enc

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
-- Each node shows: constructor name :: TypeInfo {rType, pType, chainName, tags=[...]}
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