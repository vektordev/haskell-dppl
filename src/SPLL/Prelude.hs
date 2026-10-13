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
  , sqrtF
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
  , observeBound
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
  , compileRTyped
  , compileUnoptimized
  , admissionTyped
  , rtypedProgram
  , chainNamedProgram
  , batchedRefusal
  , CodeGenTarget(..)
  , codeGenToLang
  , emitCompiled
  , runGen
  , runProb
  , runInteg
  , runWriteLogits
  , runGenC
  , runProbC
  , runIntegC
  , runGenNamedC
  , runProbNamedC
  , runIntegNamedC
  , withTopKCutoff
  , runWriteLogitsC
  , runWriteLogitsRandC
  , printIfVerbose
  , printIfMoreVerbose
  , pPrintIfVerbose
  , pPrintIfMoreVerbose
  , printStage
  , printStageIR
  , FnMarginals(..)
  , MaskTable(..)
  , marginalReport
  , maskTable
  , renderMarginalReport
  , marginalBudgetWarnings
  ) where

import SPLL.ReservedNames (topKCutoffName, accProbInitName)
import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo, GenericValue (..), CompilerError, TypeInfo(..), ADTDecl, FnDecl)
import SPLL.Typing.PType (PType(..))
import SPLL.ObservationMask
import SPLL.MaskVariants
import SPLL.AutoNeural (validateWriteLogitsGaussian)
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.Typing.Infer (addModalityInfo)
import SPLL.Typing.RInfer (addRTypeInfoAt, addRTypeInfo)
import SPLL.Validator (validateProgram)
import SPLL.CalleeNormalize (normalizeCallees)
import SPLL.DrawSinking (sinkEnumerableDraws)
import SPLL.PerValue (validateSignatures, expandPerValue, perValuePlans, checkSignatureTypes, dropSlotProbes, installPerValue)
import IRInterpreter (generateRand, generateDet, generateRandE)
import Control.Monad.Random (Rand, RandomGen, evalRand)
import System.Random (mkStdGen)
import SPLL.IRCompiler
import SPLL.IROptimizer (optimizeEnvWith)
import SPLL.IRSelectPass (selectPassEnv)
import SPLL.CodeGenPyTorchBatched (generateFunctionsBatched)
import qualified SPLL.CodeGenPyTorch
import qualified SPLL.CodeGenJulia
import Debug.Trace
import Data.Either
import SPLL.Typing.ForwardChaining (annotateProg, FCData)
import SPLL.Typing.Determinism (knownAnchors)
import qualified Data.Set as Set
import Text.PrettyPrint.Annotated.HughesPJClass()
import PrettyPrint (pPrintProg, pPrintIREnv)
import Text.Pretty.Simple (pShow)
import qualified Data.Text.Lazy as TL
import Data.Char (toUpper)
import Data.Maybe (isNothing, fromMaybe, maybeToList)
import Data.List (find, intercalate)

-- | Build an AST node with a blank annotation. All the smart constructors
-- below are annotation-free by construction; the inference passes fill them in.
mkExpr :: ExprF Expr -> Expr
mkExpr = Expr makeTypeInfo

-- Flow control
ifThenElse :: Expr -> Expr -> Expr -> Expr
ifThenElse c t e = mkExpr (IfThenElse c t e)

injF :: String -> [Expr] -> Expr
injF name args = mkExpr (InjF (Named name) args)

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

sqrtF :: Expr -> Expr
sqrtF x = injF "sqrt" [x]

-- Variables

letIn :: String -> Expr -> Expr -> Expr
-- We can not infer probabilities on letIns. So we rewrite them as lambdas
letIn s val body = apply (s #-># body) val

var :: String -> Expr
var n = mkExpr (Var n)

constF :: Double -> Expr
constF x = mkExpr (Constant (VFloat x))

constI :: Int -> Expr
constI x = mkExpr (Constant (VInt x))

constB :: Bool -> Expr
constB x = mkExpr (Constant (VBool x))

constL :: [Value] -> Expr
constL lst = mkExpr (Constant (constructVList lst))

(#->#) :: String -> Expr -> Expr
(#->#) n b = mkExpr (Lambda n b)

apply :: Expr -> Expr -> Expr
apply f x = mkExpr (Apply f x)

-- Distributions

-- Distributions are prelude primitives: nullary named leaves bound to a primitive
-- generator, represented as reserved-name Vars rather than dedicated constructors.
uniform :: Expr
uniform = mkExpr (Var "Uniform")

normal :: Expr
normal = mkExpr (Var "Normal")

bernoulli :: Double -> Expr
bernoulli p = uniform #<# constF p

binomial :: Int -> Double -> Expr
binomial n p = ifThenElse (bernoulli p) (constI 1) (constI 1) #+# binomial (n-1) p

dice :: Int -> Expr
dice 1 = constI 1
dice sides = ifThenElse (bernoulli (1/fromIntegral sides)) (constI sides)  (dice (sides-1))

-- Parameters

theta :: Expr -> Int -> Expr
theta e i = mkExpr (ThetaI e i)

subtree :: Expr -> Int -> Expr
subtree e i = mkExpr (Subtree e i)

-- Product Types

cons :: Expr -> Expr -> Expr
cons h t = injF "Cons" [h, t]

(#:#) :: Expr -> Expr -> Expr
(#:#) = cons

nul :: Expr
nul = mkExpr (Constant (constructVList []))

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
unit = mkExpr (Constant VUnit)

-- Sum types

left :: Expr -> Expr
left x = injF "left" [x]

right :: Expr -> Expr
right x = injF "right" [x]

-- | @observe binder base pred@ -- the desugaring of the surface @observe@
-- primitive (design mar-sum-types-observe): @observe base pred@ has type
-- @a -> (a -> Bool) -> Maybe a@ and yields @Just base@ where the predicate
-- holds, @Nothing@ where it does not. @Maybe a@ is @Either () a@ with the
-- Haskell-side convention @Just x = right x@, @Nothing = left ()@
-- (observe-partials-umbrella N3).
--
-- The binder is not cosmetic: @base@ occurs twice in the result (once under the
-- predicate, once as the payload), and a probabilistic @base@ spliced in twice
-- would be two independent draws rather than one observed value. Callers supply
-- a fresh name (the parser uses 'demandUniqueNumber').
observe :: String -> Expr -> Expr -> Expr
observe binder base predicate = observeBound binder base (apply predicate (var binder))

-- | 'observe' with the predicate already applied to the binder -- i.e. the
-- beta-reduced form @let binder = base in if cond then right binder else
-- left ()@, where @cond@ mentions @binder@ directly. Inference can invert such
-- a condition onto the binding, which it cannot do through an unreduced
-- @Apply (Lambda ...)@; see 'SPLL.Parser.pObserve'.
observeBound :: String -> Expr -> Expr -> Expr
observeBound binder base cond =
  letIn binder base (ifThenElse cond (right (var binder)) (left unit))

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
(#>#) a b = injF "gt" [a, b]

(#<#) :: Expr -> Expr -> Expr
(#<#) a b = injF "lt" [a, b]

(#&&#) :: Expr -> Expr -> Expr
(#&&#) a b = injF "and" [a, b]

(#||#) :: Expr -> Expr -> Expr
(#||#) a b = injF "or" [a, b]

(#!#) :: Expr -> Expr
(#!#) x = mkExpr (InjF (Named "not") [x])

-- Other

readNN :: String -> Expr -> Expr 
readNN n e = mkExpr (ReadNN n e)

-- This is a Z-Combinator
-- TODO: Our typesystem is not ready for that yet 
fix :: Expr
fix = "f" #->#
  apply ("u" #-># apply (var "f") ("n" #-># apply (apply (var "u") (var "u")) (var "n")))
    ("v" #-># apply (var "f") ("n" #-># apply (apply (var "v") (var "v")) (var "n")))


-- | Settle every neural declaration's output annotation into the one resolved
-- 'MultiValue' its consumers read ('resolveNeuralAnnotation'): no @of@ is
-- @of _@, and each @_@ is auto-derived in place. Done once, before anything
-- reads an annotation, so the plan engine's layout and Analysis's enumeration
-- tag cannot disagree, and a placeholder auto-derivation refuses (an @Int@ or
-- @Symbol@ slot, a recursive type with no depth) is a diagnostic here rather
-- than an uncaught 'error' wherever the plan happens to be forced first (task
-- of-annotation-and-auto-derived-enumeration-divergence).
resolveNeuralDecls :: Program -> Either CompilerError Program
resolveNeuralDecls p = do
  resolved <- mapM resolveOne (neurals p)
  return p{neurals = resolved}
  where
    resolveOne decl@(name, ty, _) = case resolveNeuralAnnotation (adts p) (writeLogitsDecls p) decl of
      Right mv -> Right (name, ty, Just mv)
      Left err -> Left ("Compiler Error: " ++ err)

compile :: CompilerConfig -> Program -> Either CompilerError IREnv
compile conf p0 = frontEnd conf p0 >>= compileRTyped conf

-- | 'compile' up to and including RType inference: validation, neural
-- annotation resolution, callee normalisation, RInfer.
frontEnd :: CompilerConfig -> Program -> Either CompilerError Program
frontEnd conf p0 = do
  validateProgram p0
  validateSignatures p0
  -- Per-value queries (task per-value-query-over-enumerated-slot): a function
  -- whose signature marks a result slot Enumerated gets its helper
  -- definitions here, before anything is inferred, so they are typed and
  -- compiled like any other definition. See "SPLL.PerValue".
  p <- expandPerValue (isNothing (topKThreshold conf)) <$> resolveNeuralDecls p0
  printIfVerbose conf "=== Parsed Program ==="
  pPrintIfMoreVerbose conf p
  printIfVerbose conf (pPrintProg p)
  printStage conf "After Parsing (no annotations)" p

  -- Callee normalisation (task modality-arrow-apply-crashes): resolve a
  -- function *value* in callee position back to the lambda literal it denotes,
  -- and distribute an application over an `if` that chooses between two of
  -- them. Probability mode inverts an observation through the callee's body, so
  -- it needs a lambda forward chaining can name; a tuple-projected, list-taken
  -- or if-selected lambda has none, and crashed the compiler (or, for a
  -- randomly selected one, multiplied a branch weight by a closure at runtime).
  -- Purely syntactic, so it runs here, on the unannotated program: every node
  -- it builds is annotated by the stages below like any other.
  normalized <- case normalizeCallees p of
    Nothing -> return p
    Just rewritten -> do
      printIfMoreVerbose conf "\n=== Callee normalisation rewrote the program ==="
      printStage conf "After Callee Normalization" rewritten
      return rewritten

  -- RType inference now runs first, directly on the freshly parsed program --
  -- it needs no chain names or enum tags (SPLL.Typing.RInfer reads only the
  -- Expr shape and PredefinedFunctions' contracts). Running it here, rather
  -- than after enum annotation/forward chaining as before, means: (1) ill-typed
  -- programs (e.g. fromRightPartial applied to a non-Either value) are rejected
  -- before discretesTags forward-evaluates any InjF application and can hit a
  -- partial-function crash on genuinely ill-typed input; (2) every later pass
  -- -- enum annotation, forward chaining, the modality pass -- sees real RType
  -- instead of NotSetYet, in case any of them can make use of it.
  rtyped <- addRTypeInfoAt (verbose conf) normalized
  printIfMoreVerbose conf "\n=== RType-inferred Program ==="
  pPrintIfMoreVerbose conf rtyped
  printStage conf "After RType Inference" rtyped
  return rtyped

-- | 'compile' from the post-RInfer seam onwards: enum annotation, chain naming,
-- the modality pass, conditional annotation, IR compilation, the select pass and
-- the optimizer.
--
-- Split out because a **pruned** program (design
-- @witnessed-per-query-capability@; 'SPLL.ObservationMask.pruneObservation')
-- enters the pipeline exactly here — it carries the RTypes its holes were built
-- from, and it cannot re-enter at the top, since 'validateProgram' forbids the
-- @Constant VAny@ the hole is spelled with. Everything below runs on it
-- unchanged, which is the design's central claim.
compileRTyped :: CompilerConfig -> Program -> Either CompilerError IREnv
compileRTyped conf rtypedWithSigs = do
  -- Signatures are consumed here: checked against the inferred types, and
  -- each per-value function planned. Cleared before compiling, so the
  -- per-mask variants, which re-enter this function with a pruned program,
  -- never plan a per-value function again.
  checkSignatureTypes rtypedWithSigs
  let perValue = perValuePlans conf rtypedWithSigs
      rtyped = (dropSlotProbes rtypedWithSigs) { signatures = [] }
  unoptimized <- irUnoptimized conf rtyped
  printStageIR conf "After IR Compilation (pre-optimization)" unoptimized
  -- The per-value bodies are installed after branch-count stripping, because
  -- they are built for the result encoding the point queries end up with.
  let stripped = installPerValue conf perValue
                   (if countBranches conf then unoptimized else stripBranchCount unoptimized)

  -- Batched mode (design pytorch-tensorizer): retag elementwise-eligible ifs to
  -- selects before the optimizer, which would otherwise fold the conditionals
  -- away and obscure the transformation. Runs only under --batched; in M1 it is
  -- a scalar no-op, so the default pipeline is byte-identical.
  --
  -- A separate tensor-lowering stage used to sit here, rewriting the enum-sum
  -- family into 'BReduce'/'BMap'/'BTensor' (design ir-tensor-values). Task
  -- retire-irenumsum deleted the family, and 'SPLL.Semiring' now builds that
  -- form directly, so there is nothing left to lower and the stage is gone.
  let selected = if batched conf then selectPassEnv stripped else stripped
  printStageIR conf "After Select Pass" selected

  let compiled = optimizeEnvWith conf (Set.fromList [n | (n, _, _) <- neurals rtyped]) selected
  printIfVerbose conf "\n=== Compiled Program ==="
  pPrintIfMoreVerbose conf compiled
  printIfVerbose conf (pPrintIREnv compiled)
  printStageIR conf "After Optimization" compiled
  return compiled

-- | IR compilation of an RType-inferred program, before the optimizer: the
-- typed stages, 'envToIRUnoptimized', and the per-mask inference variants
-- with their dispatchers (task per-mask-variants-by-pruning), spliced in here
-- so they go through every later pass like any other group.
irUnoptimized :: CompilerConfig -> Program -> Either CompilerError IREnv
irUnoptimized conf rtypedWithProbes = do
  let rtyped = dropSlotProbes rtypedWithProbes
  (annotated, fcData) <- typedStages conf rtyped
  baseIR <- envToIRUnoptimized conf fcData annotated
  return (withMaskVariants conf rtyped baseIR)

-- | 'compile' stopped before the select pass and the optimizer: the IR exactly
-- as IR compilation produced it. For tests that pin the compiled IR itself
-- (the all-concrete body under a mask dispatcher is today's body, byte for
-- byte), which the optimizer would otherwise rewrite.
compileUnoptimized :: CompilerConfig -> Program -> Either CompilerError IREnv
compileUnoptimized conf p = frontEnd conf p >>= irUnoptimized conf

-- | The program exactly as 'envToIRUnoptimized' receives it: every annotation
-- IRCompiler dispatches on, @pType@ included, plus the forward-chaining
-- certificate. The admission-totality oracle reads its verdicts here
-- ('admissionTyped'), so it can never read a different program from the one
-- the variant gate reads.
typedStages :: CompilerConfig -> Program -> Either CompilerError (Program, FCData)
typedStages conf rtyped = do
  let enumAnnotated = annotateEnumsProg rtyped
  printIfMoreVerbose conf "\n=== Annotated Program (1) ==="
  pPrintIfMoreVerbose conf enumAnnotated
  printStage conf "After Enum Annotation" enumAnnotated

  -- Draw sinking (task shared-enumerated-latent-loses-per-slot-factorization):
  -- move each enumerable `draw` down into the one InjF operand that reads it,
  -- so stacked draws that only a shared latent ties together are enumerated
  -- per operand rather than jointly. It needs the DiscreteValues tags just
  -- computed to know which bindings are enumerable, and the moved bindings'
  -- new nodes carry none, so a rewritten program is annotated again.
  preAnnotated <- case sinkEnumerableDraws enumAnnotated of
    Nothing -> return enumAnnotated
    Just sunk -> do
      let reannotated = annotateEnumsProg sunk
      printStage conf "After Draw Sinking" reannotated
      return reannotated

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
  return (annotated, fcData)

-- | The fully annotated program 'compile' hands to IR compilation, without
-- compiling it: the modality engine's verdicts, read where IRCompiler reads
-- them. A top-level binding whose own @pType@ is one of the four admitted
-- rungs gets a probability and an integrate function, and a 'Bottom' one gets
-- only @generate@ (see 'envToIRUnoptimized'). Used by the admission-totality
-- fuzz oracle (task @admission-totality-property@), which has to know what was
-- admitted even when the compile it is checking crashes.
admissionTyped :: CompilerConfig -> Program -> Either CompilerError Program
admissionTyped conf p = frontEnd conf p >>= fmap fst . typedStages conf

-- | Would batched mode (@--batched@) take this program? 'Nothing' if it would,
-- @Just diag@ otherwise, carrying the same diagnostic the batched backend would
-- have refused with.
--
-- This is the fragment guard ('SPLL.CodeGenPyTorchBatched.batchedGuard' +
-- @checkCallGraph@ + @hasGenCycle@) run *ahead of* a decision to batch, so a
-- user compiling normally can be told whether flipping @--batched@ would work
-- instead of finding out by trying it (task
-- @batched-scalar-mode-eligibility-warning@). It re-runs the whole pipeline
-- with @batched = True@ — the select pass changes which 'IRIf's are 'IRSelect's,
-- and the guard reads exactly that — so it is not free, which is why the CLI
-- only asks for it under @-v@.
--
-- The re-compile is silenced ('verbose', 'showIntermediates' and 'optStats'
-- forced off): the caller has just compiled this program for real and must not
-- see every stage dumped a second time.
--
-- Note the diagnostic names the *first* offending construct the guard walk
-- finds, not all of them: fixing it may reveal more behind it. That is the
-- deliberate scope (review 2026-08-28) — reporting all offenders is a different
-- traversal, and the guard's contract is refusal, not enumeration.
batchedRefusal :: CompilerConfig -> Program -> Maybe CompilerError
batchedRefusal conf p =
  case compile quiet p >>= generateFunctionsBatched True of
    Left err -> Just err
    Right _  -> Nothing
  where
    quiet = conf{batched = True, verbose = 0, showIntermediates = False, optStats = False}

-- | A backend 'codeGenToLang' emits source for.
data CodeGenTarget = TargetPython | TargetJulia deriving (Show, Eq, Enum, Bounded)

-- | The CLI's @compile@ subcommand: compile, then emit the target's source, as
-- one string. @truncOut@ is the CLI's truncation flag (the backends' "emit the
-- full runtime" argument is its negation). Python under @batched conf@ goes to
-- the batched emitter, which may refuse; the scalar backends first refuse a
-- program whose IR still holds an @ANY@ they cannot emit
-- ('anyExceptCodegenRefusal').
--
-- Library code rather than part of @app/Main.hs@ so that the fuzz
-- crash-freedom properties drive the path the CLI takes, guard included.
codeGenToLang :: CodeGenTarget -> Bool -> CompilerConfig -> Program -> Either CompilerError String
codeGenToLang target truncOut conf prog = compile conf prog >>= emitCompiled target truncOut conf

-- | The emitting half of 'codeGenToLang', for an 'IREnv' already compiled under
-- @conf@. Pure string building: it needs no Python or Julia installed.
emitCompiled :: CodeGenTarget -> Bool -> CompilerConfig -> IREnv -> Either CompilerError String
emitCompiled target truncOut conf compiled = case target of
  TargetPython
    | batched conf -> intercalate "\n" <$> generateFunctionsBatched (not truncOut) compiled
    | otherwise    -> do
        anyExceptCodegenRefusal "Python" compiled
        Right $ intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions (not truncOut) compiled)
  TargetJulia -> do
    anyExceptCodegenRefusal "Julia" compiled
    Right $ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions compiled)

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

-- | Run the writeLogits function of the named function group (e.g. "decA_auto" for a
-- read-logits declaration `decA :: Symbol -> ...`).
-- outerArgs mirrors main's outer parameter list: pass one IRValue per outer lambda in main,
-- or an empty list for closed-form programs with no outer parameters.
runWriteLogits :: CompilerConfig -> Program -> String -> [IRValue] -> Either CompilerError IRValue
runWriteLogits _ p _ _ | isLeft (validateProgram p) = fmap (error "Impossible case") (validateProgram p)
runWriteLogits conf p target outerArgs = do
  compiled <- compile conf p
  runWriteLogitsC p compiled target outerArgs

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
  case genFun (lookupIREnv name compiled) of
    Just (gen, _) -> generateRand (neurals p) (writeLogitsDecls p) compiled (map IRConst args) gen
    -- Unlike the prob/integ runners there is no error channel in the return
    -- type to report this through.
    Nothing -> error (missingVariant "generate" "gen" (lookupIREnv name compiled))

runProbNamedC :: Program -> IREnv -> String -> [IRValue] -> IRValue -> Either CompilerError IRValue
runProbNamedC p compiled name args x =
  case probFun (lookupIREnv name compiled) of
    Nothing -> Left (missingVariant "probability" "prob" (lookupIREnv name compiled))
    Just (prob, _) -> generateDet (neurals p) (writeLogitsDecls p) compiled (map IRConst args') prob
      -- topK-compiled prob functions take an accumulated-probability parameter
      -- right after the sample; seed it with the semiring's multiplicative
      -- identity at the query root -- linear 1.0, or log-space 0.0. Hardcoding
      -- 1.0 here silently discarded all probability mass under logSpace, since
      -- the compiled cutoff comparisons expect a log-space accumulator
      -- (task topk-logspace-unsound).
      -- The runtime cutoff follows it, read from the env's TOP_K_CUTOFF (the
      -- compiled-in default, or whatever 'withTopKCutoff' set).
      where args' = case topKCutoff compiled of
              Just cutoff -> x : accProbInit compiled : cutoff : args
              Nothing     -> x : args

-- The IRCompiler emits the TOP_K_CUTOFF constant iff topKThreshold was set,
-- so a compiled IREnv carries its own marker for the extra acc_prob and
-- top_k_cutoff parameters, and the cutoff value to pass for the latter.
topKCutoff :: IREnv -> Maybe IRValue
topKCutoff (IREnv _ _ consts) = lookup topKCutoffName consts

-- | Re-threshold a topK compile without recompiling it (task
-- runtime-parametric-topk-threshold): every pruning guard compares against
-- the runtime @top_k_cutoff@ parameter, so replacing the TOP_K_CUTOFF default
-- the run* entry points pass for it is all a new threshold takes. The
-- threshold is linear, as in 'topKThreshold'; it is moved into the compile's
-- space here (@log t@ under logSpace, recognised by ACC_PROB_INIT being the
-- log semiring's one, 0). Calling it on a compile without topK is a caller
-- bug -- that compile has no guards to re-threshold -- and is an error.
withTopKCutoff :: Double -> IREnv -> IREnv
withTopKCutoff thresh env@(IREnv funcs adtDecls consts) = case topKCutoff env of
  Nothing -> error "withTopKCutoff: the IREnv was compiled without topKThreshold, so it has no cutoff to set"
  Just _  -> IREnv funcs adtDecls [ if n == topKCutoffName then (n, VFloat cutoff) else (n, v) | (n, v) <- consts ]
  where
    cutoff = case accProbInit env of
      VFloat one | one == 0 -> log thresh
      _                     -> thresh

-- The IRCompiler emits ACC_PROB_INIT alongside TOP_K_CUTOFF, in the same
-- space (linear 1.0 / log-space 0.0), so the caller never has to know
-- separately whether the compilation was log-space.
accProbInit :: IREnv -> IRValue
accProbInit (IREnv _ _ consts) = fromMaybe (VFloat 1.0) (lookup accProbInitName consts)

runIntegC :: Program -> IREnv -> [IRValue] -> IRValue -> Either CompilerError IRValue
runIntegC p compiled = runIntegNamedC p compiled "main"

runIntegNamedC :: Program -> IREnv -> String -> [IRValue] -> IRValue -> Either CompilerError IRValue
runIntegNamedC p compiled name args sample =
  case integFun (lookupIREnv name compiled) of
    -- A topK-compiled integrate function takes the runtime cutoff right
    -- after the sample (no acc_prob: its root seeds its own).
    Just (integ, _) -> generateDet (neurals p) (writeLogitsDecls p) compiled (map IRConst (sample : maybeToList (topKCutoff compiled) ++ args)) integ
    Nothing -> Left (missingVariant "integrate" "integ" (lookupIREnv name compiled))

-- | Modality inference decides per definition which of the three variants are
-- tractable, and the --noGenerate/--noProbability/--noIntegrate flags suppress
-- them outright, so asking a compiled group for a variant it does not have is a
-- normal outcome rather than an internal inconsistency. When the compiler
-- itself refused the variant (an unsupported shape, recorded on the group by
-- 'IRCompiler.envToIRUnoptimized'; task static-refusals-become-absent-variants),
-- the message says why.
missingVariant :: String -> String -> IRFunGroup -> CompilerError
missingVariant variant lbl grp = case lookup lbl (refusedVariants grp) of
  Just r ->
    "'" ++ name ++ "' has no compiled " ++ variant ++ " function: NeST refused to compile it:\n"
    ++ showRefusal r
  Nothing ->
    "'" ++ name ++ "' has no compiled " ++ variant ++ " function: it is either "
    ++ "intractable for that mode or was suppressed by the --no" ++ capitalise variant ++ " flag"
  where name = groupName grp
        capitalise (c:cs) = toUpper c : cs
        capitalise []     = []

-- | Run the writeLogits function of the function group named `target`. Each read-logits
-- declaration `name :: Symbol -> X` contributes a group `<name>_auto` whose writeLogits
-- is independently scoped to that declaration's own target type, so the target name
-- selects which read-logits network's writeLogits to run (rather than relying on
-- declaration order).
--
-- A writeLogits vector is exact except in the slots of a dead arm (a constructor of
-- probability exactly zero), which hold iid noise (task writelogits-dead-arm-nan).  This
-- runner draws that noise from a fixed seed, so it is a pure function of its arguments;
-- 'runWriteLogitsRandC' draws it from the caller's generator.
runWriteLogitsC :: Program -> IREnv -> String -> [IRValue] -> Either CompilerError IRValue
runWriteLogitsC p compiled target outerArgs =
  evalRand (runWriteLogitsRandC p compiled target outerArgs) (mkStdGen 0)

-- | 'runWriteLogitsC' with the dead-arm noise drawn from the caller's generator.
runWriteLogitsRandC :: (RandomGen g) => Program -> IREnv -> String -> [IRValue] -> Rand g (Either CompilerError IRValue)
runWriteLogitsRandC p compiled target outerArgs =
  case validateWriteLogitsGaussian (adts p) (writeLogitsDecls p) (neurals p) compiled >> findEnc of
    Left err  -> return (Left err)
    Right enc -> generateRandE (neurals p) (writeLogitsDecls p) compiled (map IRConst outerArgs) enc
  where
    IREnv groups _ _ = compiled
    findEnc = case find ((== target) . groupName) groups of
      Nothing  -> Left ("No function group named " ++ show target ++ " in compiled program")
      Just grp -> case writeLogitsFun grp of
        Nothing       -> Left ("Function group " ++ show target ++ " has no writeLogits function")
        Just (enc, _) -> Right enc

printIfVerbose :: (Monad m) => CompilerConfig -> String -> m ()
printIfVerbose CompilerConfig {verbose=v} s | v >= 1 = trace s (return ())
printIfVerbose _ _ = return ()

printIfMoreVerbose :: (Monad m) => CompilerConfig -> String -> m ()
printIfMoreVerbose CompilerConfig {verbose=v} s | v >= 2 = trace s (return ())
printIfMoreVerbose _ _ = return ()

pPrintIfVerbose :: (Monad m, Show a) => CompilerConfig -> a -> m ()
pPrintIfVerbose CompilerConfig {verbose=v} s | v >= 1 = trace (TL.unpack (pShow s)) (return ())
pPrintIfVerbose _ _ = return ()

pPrintIfMoreVerbose :: (Monad m, Show a) => CompilerConfig -> a -> m ()
pPrintIfMoreVerbose CompilerConfig {verbose=v} s | v >= 2 = trace (TL.unpack (pShow s)) (return ())
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
-- ---------------------------------------------------------------------------
-- The observation-mask report (task observation-mask-analysis)
-- ---------------------------------------------------------------------------

-- | The per-mask capability table of one function, or why there isn't one.
data MaskTable
  = NoEnumeratedSlots
    -- ^ Every leaf slot is self-contained, so the existing per-field @anySafe@
    -- guard is already exact and no variant is needed.
  | OverBudget Int Int
    -- ^ @OverBudget k budget@: the function has more enumerated slots than
    -- @--marginalSlots@ allows, so it is not analysed per mask. It compiles as
    -- today.
  | MaskTable [(Mask, PType)]
    -- ^ The projected 'PType' of each masked program, all-concrete mask first.
  deriving (Eq, Show)

-- | What the @--marginals@ report says about one function.
data FnMarginals = FnMarginals
  { fmName       :: String
  , fmSlots      :: [(Slot, SlotVerdict)]
  , fmClasses    :: [[Slot]]
  , fmEnumerated :: [Slot]
  , fmTable      :: MaskTable
  } deriving Show

-- | The program as the mask analysis reads it: validated, callee-normalised and
-- RType-inferred, but not yet enum-annotated, chain-named or modality-typed.
--
-- This is the stage pruning runs at, per the design: a leaf's 'RType' is
-- available to carry onto its hole, and everything after it — enum annotation,
-- forward chaining, modality inference — then runs on the pruned program
-- unchanged.
rtypedProgram :: Program -> Either CompilerError Program
rtypedProgram p0 = do
  validateProgram p0
  p <- resolveNeuralDecls p0
  addRTypeInfo (fromMaybe p (normalizeCallees p))

-- | Enum annotation plus chain naming. The analysis needs chain names because
-- latent identity is keyed by them.
chainNamedProgram :: Program -> Program
chainNamedProgram = annotateProg . annotateEnumsProg

-- | The modality pass on an RType-inferred program, returning it typed.
modalityTyped :: Program -> Either CompilerError Program
modalityTyped rtyped = fst <$> addModalityInfo (chainNamedProgram rtyped)

-- | The observation-mask analysis for every function of a program: its leaf
-- slots and why each is enumerated or self-contained, its correlation classes,
-- and its per-mask capability table.
--
-- The table is produced by typing the masked program — there is no separate
-- mask-verdict computation that could disagree with it, which is the whole
-- point of the pruning route (design @witnessed-per-query-capability@, "Why the
-- previous cut of this design was wrong").
marginalReport :: CompilerConfig -> Program -> Either CompilerError [FnMarginals]
marginalReport conf p = do
  rtyped <- rtypedProgram p
  let named = chainNamedProgram rtyped
      decls = adts named
      fenv  = functions named
  mapM (oneFunction conf rtyped decls fenv) (functions named)

oneFunction :: CompilerConfig -> Program -> [ADTDecl] -> [FnDecl] -> FnDecl
            -> Either CompilerError FnMarginals
oneFunction conf rtyped decls fenv decl@(fname, _) = do
  table <- case () of
    _ | k == 0                    -> return NoEnumeratedSlots
      | k > marginalSlots conf    -> return (OverBudget k (marginalSlots conf))
      | otherwise                 -> MaskTable <$> mapM row (masksOver enums)
  return FnMarginals { fmName = fname, fmSlots = verdicts, fmClasses = classes
                     , fmEnumerated = enums, fmTable = table }
  where
    tree     = observationTree decls decl
    verdicts = slotVerdicts decls fenv tree
    classes  = correlationClasses (slotLatents decls fenv tree)
    enums    = [ s | (s, v) <- verdicts, v /= SelfContained ]
    k        = length enums
    row m    = (,) m <$> maskedPType rtyped decls fname m

-- | The projected 'PType' of one masked program: prune, then run the rest of
-- the typing pipeline on it exactly as an unpruned program would be.
maskedPType :: Program -> [ADTDecl] -> String -> Mask -> Either CompilerError PType
maskedPType rtyped decls fname m = do
  typed <- modalityTyped pruned
  case find ((== fname) . fst) (functions typed) of
    Just (_, body) -> return (pType (getTypeInfo body))
    Nothing        -> Left ("maskedPType: function vanished: " ++ fname)
  where
    pruned = rtyped
      { functions = [ if n == fname then pruneObservation decls m d else d
                    | d@(n, _) <- functions rtyped ] }

-- | The task's headline entry point: for every function with at least one
-- enumerated slot and at most @marginalSlots@ of them, the projected 'PType' of
-- each masked program.
maskTable :: CompilerConfig -> Program -> Either CompilerError [(String, [(Mask, PType)])]
maskTable conf p = do
  report <- marginalReport conf p
  return [ (fmName r, t) | r <- report, MaskTable t <- [fmTable r] ]

-- | The @--marginals@ report, rendered.
renderMarginalReport :: [ADTDecl] -> [FnMarginals] -> String
renderMarginalReport decls = unlines . concatMap fn
  where
    fn r =
      [ fmName r ]
      ++ [ "  slots:" ]
      ++ [ "    " ++ padTo 24 (prettySlot decls s) ++ " " ++ verdict v
         | (s, v) <- fmSlots r ]
      ++ [ "  correlation classes:" ]
      ++ [ "    { " ++ intercalate ", " (map (prettySlot decls) c) ++ " }"
         | c <- fmClasses r ]
      ++ [ "  enumerated slots: "
             ++ (if null (fmEnumerated r) then "none"
                 else intercalate ", " (map (prettySlot decls) (fmEnumerated r))) ]
      ++ tbl r
      ++ [ "" ]

    tbl r = case fmTable r of
      NoEnumeratedSlots -> [ "  mask table: none needed (every slot self-contained)" ]
      OverBudget k b    -> [ "  mask table: declined -- " ++ show k
                             ++ " enumerated slots exceeds --marginalSlots " ++ show b ]
      MaskTable rows    -> "  mask table:"
                           : [ "    " ++ padTo 24 (prettyMask (fmEnumerated r) m)
                                 ++ " -> " ++ show pt | (m, pt) <- rows ]

    verdict SelfContained         = "self-contained"
    verdict (SharesLatents ss)    = "enumerated: shares a latent with "
                                      ++ intercalate ", " (map (prettySlot decls) ss)
    verdict (ReadsOuterLatents _) = "enumerated: reads a latent drawn outside it"

    padTo n str = str ++ replicate (n - length str) ' '

-- ---------------------------------------------------------------------------
-- Per-mask inference variants (task per-mask-variants-by-pruning)
-- ---------------------------------------------------------------------------

-- | What the mask analysis decides for one function, as compilation reads it.
data MaskPlan
  = NoMasks
    -- ^ The observation is not a constructor tree, or every slot is
    -- self-contained: nothing to dispatch on.
  | MasksOverBudget Int
    -- ^ @k@ enumerated slots, over @--marginalSlots@.
  | Masks [Slot]
    -- ^ The enumerated slots, in tree order.

-- | The mask plan of every function of an RType-inferred program.
--
-- Chain naming is what latent identity is keyed by, so the analysis reads the
-- chain-named program, exactly as the @--marginals@ report does. That costs one
-- extra enum annotation and forward-chaining pass, so it is skipped outright
-- when no function's observation is a constructor tree at all (a root that is
-- a single leaf has nothing to mask: an @ANY@ there is the root unit factor).
maskPlans :: CompilerConfig -> Program -> [(String, MaskPlan)]
maskPlans conf rtyped
  | not (any (isTree . observationTree (adts rtyped)) (functions rtyped)) =
      [ (n, NoMasks) | (n, _) <- functions rtyped ]
  | otherwise = map plan (functions named)
  where
    named = chainNamedProgram rtyped
    decls = adts named
    fenv  = functions named
    isTree ObsCon{} = True
    isTree _        = False
    plan decl@(n, _)
      | not (isTree tree) = (n, NoMasks)
      | null enums        = (n, NoMasks)
      | k > marginalSlots conf = (n, MasksOverBudget k)
      | otherwise         = (n, Masks enums)
      where
        tree  = observationTree decls decl
        enums = enumeratedSlots decls fenv tree
        k     = length enums

-- | One compile-time warning per function over the @--marginalSlots@ budget,
-- naming the function and the flag. Empty when the program does not type (the
-- compile itself reports that).
marginalBudgetWarnings :: CompilerConfig -> Program -> [String]
marginalBudgetWarnings conf p = case rtypedProgram p of
  Left _ -> []
  Right rtyped ->
    [ "Warning: " ++ overBudgetNote n k (marginalSlots conf)
    | (n, MasksOverBudget k) <- maskPlans conf rtyped ]

-- | Compile every function's per-mask variants and turn its probability and
-- integrate functions into dispatchers over them.
--
-- For each function with @1..marginalSlots@ enumerated slots, and each mask
-- over them other than all-concrete, the masked program
-- ('pruneObservation') goes through the ordinary pipeline from the post-RInfer
-- seam, and the function's probability and integrate bodies from that compile
-- become the variant @f__m\<bits\>@ ('withDispatcher'). Which masks have a
-- variant is the masked program's own modality verdict -- the same gate
-- 'envToIRUnoptimized' applies to a whole function -- so the lattice decides,
-- and a mask it declines is a runtime refusal in the dispatcher. A mask it
-- admits but an engine then refuses compiles to a variant whose body is that
-- refusal. Nothing here can fail the base compile.
--
-- The variant bodies are not forced here (see 'MaskVariant'): only the typing
-- of each masked program is.
--
-- Skipped wholesale under @--pruneAnyChecks@ (the dispatcher would collapse to
-- the all-concrete body anyway, and the variants would be dead code), and when
-- both probability and integrate are suppressed.
withMaskVariants :: CompilerConfig -> Program -> IREnv -> IREnv
withMaskVariants conf rtyped env@(IREnv groups decls consts)
  | pruneAnyChecks conf || (noProbability conf && noIntegrate conf) = env
  | null work && null overBudget = env
  | otherwise = IREnv (concatMap expand groups) decls consts
  where
    plans = maskPlans conf rtyped
    existing = Set.fromList (map groupName groups)
    work = [ (n, slots) | (n, Masks slots) <- plans
                        , not (any (`Set.member` existing)
                                   [ variantGroupName n slots m | m <- drop 1 (masksOver slots) ]) ]
    overBudget = [ (n, k) | (n, MasksOverBudget k) <- plans ]

    expand g
      | Just slots <- lookup (groupName g) work =
          withDispatcher decls slots [ variantFor (groupName g) m | m <- drop 1 (masksOver slots) ] g
      | Just k <- lookup (groupName g) overBudget =
          [ g { groupDoc = groupDoc g ++ "\n" ++ overBudgetNote (groupName g) k (marginalSlots conf) } ]
      | otherwise = [g]

    -- Masked compiles are silent and single-semiring: they must not dump every
    -- stage a second time under -d/-v, and an extra-semiring group is a base
    -- function's endpoint, not a variant's.
    quiet = conf { verbose = 0, showIntermediates = False, optStats = False, extraSemirings = [] }

    variantFor fname m = case typedStages quiet pruned of
      -- The masked program does not even type: no mode is admitted.
      Left _ -> MaskVariant m Nothing Nothing
      Right (typedPruned, fc) ->
        let admitted = maybe False (admittedPType . pType . getTypeInfo . snd)
                         (find ((== fname) . fst) (functions typedPruned))
            -- Lazy: forced only when a variant body is read.
            compiled = envToIRUnoptimized quiet fc typedPruned
            body lbl field = case compiled of
              Left err -> Left err
              Right menv -> case find ((== fname) . groupName) (irGroups menv) of
                Nothing -> Left ("the masked compile has no group " ++ fname)
                Just mg -> case field mg of
                  Just d -> Right d
                  Nothing -> Left (maybe "the variant is absent" showRefusal (lookup lbl (refusedVariants mg)))
        in MaskVariant m
             (if admitted && not (noProbability conf) then Just (body "prob" probFun) else Nothing)
             (if admitted && not (noIntegrate conf) then Just (body "integ" integFun) else Nothing)
      where
        pruned = restrictToCallees fname rtyped
          { functions = [ if n == fname then pruneObservation (adts rtyped) m d else d
                        | d@(n, _) <- functions rtyped ] }

    irGroups (IREnv gs _ _) = gs

    -- The four rungs a probability and an integrate function are compiled for
    -- (IRCompiler's 'admittedPT', the variant gate).
    admittedPType pt = pt `elem` [Deterministic, Integrate, PNormal, PLogNormal]

-- | The program cut down to one function and everything it (transitively)
-- references, so a masked compile does not recompile the rest of the program.
restrictToCallees :: String -> Program -> Program
restrictToCallees root p = p { functions = [ d | d@(n, _) <- functions p, n `Set.member` reach ] }
  where
    names = Set.fromList (map fst (functions p))
    callees n = case lookup n (functions p) of
      Just b  -> Set.toList (Set.intersection names (containedVars varsOfExpr b))
      Nothing -> []
    reach = go Set.empty [root]
    go seen [] = seen
    go seen (n : ns)
      | n `Set.member` seen = go seen ns
      | otherwise = go (Set.insert n seen) (callees n ++ ns)
