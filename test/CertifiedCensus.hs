-- | Which IR constructs the backend-agreement fuzzers certify, and which a
-- corpus program uses (docs-repo task @impact-analysis-m2-drop-runtime-from-key@,
-- impact analysis M2).
--
-- Under M2 the interpreter is the corpus's only oracle: every @.tst@ row is
-- checked there. Whether the scalar Python and Julia backends agree with the
-- interpreter is the agreement fuzzers' question
-- ('TestFuzz.prop_Fuzz_BackendsAgree', 'TestFuzz.prop_Fuzz_IRBackendsAgree'),
-- not the corpus's. That argument holds for a program only when every
-- construct it emits is one the fuzzers put through both backends. So a
-- corpus program keeps its per-program Python and Julia checks, keyed with the
-- runtime fingerprint as under M1, exactly when 'uncertifiedConstructs' of its
-- 'programCensus' is non-empty.
--
-- The census is taken over every body a program emits, generate included
-- (since the IR fuzz generator's M4 its generate bodies, draws and all, are
-- compared on both backends by replaying each backend's draws through the
-- interpreter), of the compiles the text backends are run on (-O2 and -O0).
-- It is not taken per compiler config (IR fuzz generator M5): certification
-- is a statement about the backends alone, a construct is certified if the
-- IR generator reaches it whichever config emitted it, and the other configs
-- are only checked on the interpreter. That the generator reaches everything
-- the compiler emits under them is a guard of its own
-- ('BackendCoverage.generatorGuardConfigs').
--
-- This is a leaf module: "End2EndTesting" needs it and the fuzz modules import
-- "End2EndTesting", so it cannot live with them.
module CertifiedCensus
  ( irConstructs
  , irEnvConstructs
  , inferenceBodies
  , deterministicBodies
  , allBodies
  , samplingConstructs
  , certifiedConstructs
  , programCensus
  , uncertifiedConstructs
  , batchedCertifiedConstructs
  , batchedProgramCensus
  , batchedUncertifiedConstructs
  , structureSplitLabel
  , lineSpillLabel
  ) where

import Data.Char (isDigit, isSpace)
import Data.List (isPrefixOf, nub, sort, (\\))

import SPLL.IntermediateRepresentation
import SPLL.CodeGenPyTorchBatched (usesStructureSplit, generateFunctionsBatched)
import SPLL.Lang.Types (GenericValue(..), GenericList(..))

-- | Every IR construct a body uses, as a label naming its kind:
-- @IRExpr:IRIf@, @Operand:OpPlus@, @UnaryOperand:OpExp@, @Builtin:BReduce ROpAdd@,
-- @Distribution:IRNormal Log@ (density/cumulative leaves, with their log-space
-- flag), @Sample:IRUniform@, @ConTag:TgCons@, @Accessor:AcHead@. These are the
-- axes along which the two text backends' lowerings differ case by case.
irConstructs :: IRExpr -> [String]
irConstructs e = nub (go e)
  where
    go x = here x ++ concatMap go (getIRSubExprs x) ++ inValues x
    here x = ("IRExpr:" ++ ctor (show x)) : case x of
      IROp op _ _ -> ["Operand:" ++ show op]
      IRUnaryOp op _ -> ["UnaryOperand:" ++ show op]
      IRBuiltin b _ -> ["Builtin:" ++ builtinLabel b]
      IRDensity d ls _ -> ["Density:" ++ show d ++ " " ++ show ls]
      IRCumulative d ls _ -> ["Cumulative:" ++ show d ++ " " ++ show ls]
      IRSample d -> ["Sample:" ++ show d]
      IRConstruct t _ -> ["ConTag:" ++ show t]
      IRDestruct a _ -> ["Accessor:" ++ ctor (show a)]
      -- A non-empty list constant is its own axis: the batched backend spells
      -- it as a cons structure over broadcast leaves (task
      -- batched-refuses-list-constants-with-data), and its equality against a
      -- batched list (an ANY tail included) is runtime code no other
      -- 'IRExpr:IRConst' exercises. Without the label a program holding one
      -- counted as certified whether or not a fuzzer ever compared one.
      IRConst (VList (ListCont _ _)) -> ["Const:VList ListCont"]
      _ -> []
    -- A closure or a lambda-valued constant carries IR of its own.
    inValues (IRConst v) = concatMap go (valueExprs v)
    inValues _ = []
    ctor = takeWhile (not . isSpace)
    builtinLabel b = case b of
      BReduce op _ -> "BReduce " ++ show op
      BZip op -> "BZip " ++ show op
      _ -> ctor (show b)

valueExprs :: IRValue -> [IRExpr]
valueExprs v = case v of
  VTuple a b -> valueExprs a ++ valueExprs b
  VEither (Left a) -> valueExprs a
  VEither (Right b) -> valueExprs b
  VList l -> listExprs l
  VADT _ fs -> concatMap valueExprs fs
  VClosure _ _ body -> [body]
  _ -> []
  where
    listExprs (ListCont x xs) = valueExprs x ++ listExprs xs
    listExprs _ = []

-- | The probability and integrate bodies of every group: what
-- 'prop_Fuzz_BackendsAgree' actually evaluates in both backends.
inferenceBodies :: IREnv -> [IRExpr]
inferenceBodies (IREnv gs _ _) = [ b | g <- gs, Just (b, _) <- [probFun g, integFun g] ]

-- | The probability, integrate, writeLogits and normal bodies of every group:
-- every body that has a value the backends can agree on. The corpus side of
-- 'BackendCoverage''s census.
deterministicBodies :: IREnv -> [IRExpr]
deterministicBodies (IREnv gs _ _) =
  [ b | g <- gs, Just (b, _) <- [probFun g, integFun g, writeLogitsFun g, normalFun g] ]

-- | Every emitted body, generate and writeLogits included: what a corpus
-- program asks of the backends.
allBodies :: IREnv -> [IRExpr]
allBodies (IREnv gs _ _) =
  [ b | g <- gs, Just (b, _) <- [genFun g, probFun g, integFun g, writeLogitsFun g, normalFun g] ]

irEnvConstructs :: (IREnv -> [IRExpr]) -> IREnv -> [String]
irEnvConstructs which env = sort (nub (concatMap irConstructs (which env)))

-- | The sampling primitives: the draws themselves, and the inverse-CDF
-- categorical index a neural read's sampler is built on (pure given its
-- uniform, but it exists only to turn a uniform into a categorical draw, and
-- appears only in generate bodies). Each has its own runtime function per
-- backend (@rand@, @randn@, @categorical_index@), with a distribution test
-- per backend in "TestSamplingPrimitives".
samplingConstructs :: [String]
samplingConstructs =
  [ "IRExpr:IRSample", "Sample:IRNormal", "Sample:IRUniform", "Builtin:BCategoricalIndex" ]

-- | The constructs the agreement fuzzers compare across the interpreter,
-- scalar Python and Julia: what the IR fuzz generator's fixed-seed sample
-- reaches ('IRFuzz.irGeneratorConstructs', the sample
-- 'TestFuzz.prop_Fuzz_IRBackendsAgree' draws from), the sampling primitives
-- included since M4.
-- A static list so the default tier need not draw the sample; kept exact by
-- @Slow.IRGeneratorCoverage@, so a construct the generator stops reaching
-- leaves it (and the programs using it get their Python and Julia checks
-- back), and one it starts reaching must be added.
--
-- Only the IR generator's reach is counted. It reaches every construct the
-- corpus emits under any config ('BackendCoverage.irGeneratorDeferred' is
-- empty), so the typed-program fuzzer's sample, which is costly to draw,
-- would add nothing a corpus program uses.
certifiedConstructs :: [String]
certifiedConstructs =
  -- Measured 2026-10-13 (IRFuzz's fixed-seed sample of 600 cases, after M4):
  -- 81 constructs; "Const:VList ListCont" labelled separately since
  -- 2026-10-21 (task batched-refuses-list-constants-with-data).
  [ "Accessor:AcFromLeft", "Accessor:AcFromRight", "Accessor:AcFst", "Accessor:AcHead",
    "Accessor:AcIsLeft", "Accessor:AcIsRight", "Accessor:AcSnd", "Accessor:AcSubtree",
    "Accessor:AcTail", "Accessor:AcTheta",
    "Builtin:BCategoricalIndex", "Builtin:BIndex", "Builtin:BListIndex", "Builtin:BMap", "Builtin:BMapList",
    "Builtin:BReduce ROpAdd", "Builtin:BReduce ROpLogSumExp", "Builtin:BReduce ROpMax",
    "Builtin:BTensor", "Builtin:BZip OpAnd", "Builtin:BZip OpApprox", "Builtin:BZip OpDiv",
    "Builtin:BZip OpEq", "Builtin:BZip OpGreaterThan", "Builtin:BZip OpLessThan",
    "Builtin:BZip OpMax", "Builtin:BZip OpMult", "Builtin:BZip OpOr", "Builtin:BZip OpPlus",
    "Builtin:BZip OpSub",
    "ConTag:TgCons", "ConTag:TgLeft", "ConTag:TgRight", "ConTag:TgTuple",
    "Const:VList ListCont",
    "Cumulative:IRNormal Linear", "Cumulative:IRNormal Log", "Cumulative:IRUniform Linear",
    "Cumulative:IRUniform Log",
    "Density:IRNormal Linear", "Density:IRNormal Log", "Density:IRUniform Linear",
    "Density:IRUniform Log",
    "IRExpr:IRApply", "IRExpr:IRBuiltin", "IRExpr:IRConformsTo", "IRExpr:IRConst",
    "IRExpr:IRConstruct", "IRExpr:IRCumulative", "IRExpr:IRDensity", "IRExpr:IRDestruct",
    "IRExpr:IRError", "IRExpr:IRIf", "IRExpr:IRIsPossible", "IRExpr:IRLambda", "IRExpr:IRLetIn",
    "IRExpr:IROp", "IRExpr:IRSample", "IRExpr:IRSelect", "IRExpr:IRUnaryOp", "IRExpr:IRVar",
    "Operand:OpAnd", "Operand:OpApprox", "Operand:OpDiv", "Operand:OpEq", "Operand:OpGreaterThan",
    "Operand:OpIntDiv", "Operand:OpLessThan", "Operand:OpMax", "Operand:OpMod", "Operand:OpMult",
    "Operand:OpOr", "Operand:OpPlus", "Operand:OpSub",
    "UnaryOperand:OpAbs", "UnaryOperand:OpExp", "UnaryOperand:OpIsAny", "UnaryOperand:OpLog",
    "UnaryOperand:OpNeg", "UnaryOperand:OpNot", "UnaryOperand:OpSign",
    "Sample:IRNormal", "Sample:IRUniform"
  ]

-- | A program's census: the constructs of every body of each of the compiles
-- the text backends run (-O2 and -O0; a compile the compiler refuses
-- contributes nothing, since nothing of it is run).
programCensus :: [Either e IREnv] -> [String]
programCensus envs =
  sort (nub (concat [ irEnvConstructs allBodies env | Right env <- envs ]))

-- | The constructs of a census the fuzzers do not certify.
uncertifiedConstructs :: [String] -> [String]
uncertifiedConstructs census = census \\ certifiedConstructs

-- | The batched counterpart of 'certifiedConstructs' (docs-repo task
-- @batched-backend-reference-compliance@): the constructs the two batched
-- fuzz arms put through the batched backend and compare with the
-- interpreter, in the probability and integrate bodies they call. Those are
-- the typed-program fuzzer's batched arm ('TestFuzz.prop_Fuzz_BackendsAgree',
-- over the fixed-seed sample of 'BackendCoverage') and the IR fuzz
-- generator's ('IRFuzz.irGeneratorBatchedConstructs'). The typed arm carries
-- nearly all of it: the IR generator's batched cases are few, and a body that
-- calls a helper or holds a theta constant is refused there. Kept exact by
-- @Slow.BackendAgreementCoverage@.
--
-- A corpus program declaring @batched@ has its @batched-vs-expected@ value
-- check (its @.tst@ rows on the batched backend) exactly when
-- 'batchedUncertifiedConstructs' of its 'batchedProgramCensus' is non-empty.
-- Only that check: the arm compares @forward@ and @integrate@ at query
-- points, never gradients, batched generate or the dense entry points, so
-- @gradients-nan-free@, @generate-density-matches-expected@ and the dense and
-- topK checks run regardless.
batchedCertifiedConstructs :: [String]
batchedCertifiedConstructs =
  -- Measured 2026-10-13: the typed fuzzer's sample (1000 draws, 344
  -- batched-compared) reaches 54 constructs, the IR generator's (600 cases,
  -- 28 batched-compared) 49; together 58. "Const:VList ListCont" since
  -- 2026-10-21, when batched mode admitted non-empty list constants (task
  -- batched-refuses-list-constants-with-data).
  [ "Accessor:AcFromLeft", "Accessor:AcFromRight", "Accessor:AcFst", "Accessor:AcHead",
    "Accessor:AcIsLeft", "Accessor:AcIsRight", "Accessor:AcSnd", "Accessor:AcTail",
    "Builtin:BIndex", "Builtin:BListIndex", "Builtin:BMap", "Builtin:BReduce ROpAdd",
    "Builtin:BReduce ROpLogSumExp", "Builtin:BTensor",
    "ConTag:TgCons", "ConTag:TgLeft", "ConTag:TgRight", "ConTag:TgTuple",
    "Const:VList ListCont",
    "Cumulative:IRNormal Linear", "Cumulative:IRNormal Log", "Cumulative:IRUniform Linear",
    "Density:IRNormal Linear", "Density:IRUniform Linear",
    "IRExpr:IRApply", "IRExpr:IRBuiltin", "IRExpr:IRConformsTo", "IRExpr:IRConst",
    "IRExpr:IRConstruct", "IRExpr:IRCumulative", "IRExpr:IRDensity", "IRExpr:IRDestruct",
    "IRExpr:IRError", "IRExpr:IRIf", "IRExpr:IRIsPossible", "IRExpr:IRLambda",
    "IRExpr:IRLetIn", "IRExpr:IROp", "IRExpr:IRSelect", "IRExpr:IRUnaryOp", "IRExpr:IRVar",
    "Operand:OpAnd", "Operand:OpApprox", "Operand:OpDiv", "Operand:OpEq",
    "Operand:OpGreaterThan", "Operand:OpLessThan", "Operand:OpMax", "Operand:OpMult",
    "Operand:OpOr", "Operand:OpPlus", "Operand:OpSub",
    "UnaryOperand:OpAbs", "UnaryOperand:OpExp", "UnaryOperand:OpIsAny", "UnaryOperand:OpLog",
    "UnaryOperand:OpNeg", "UnaryOperand:OpNot", "UnaryOperand:OpSign"
  ]

-- | A program's batched census: the constructs of the probability and
-- integrate bodies of its batched compile (after the select pass), which is
-- what @batched-vs-expected@ calls. A refused compile contributes nothing.
--
-- Plus 'structureSplitLabel' when the batched backend splits a body at a
-- structure select ('SPLL.CodeGenPyTorchBatched.usesStructureSplit'): the
-- split is runtime code (@split_retry@) that no IR construct names, so the
-- census has to name it itself. The fuzz arms' reach is counted from IR
-- constructs alone, so the label is never in 'batchedCertifiedConstructs',
-- and a program that splits always has its batched-vs-expected check.
--
-- Likewise 'lineSpillLabel' when the emitted module spilled a line too deep for
-- CPython into statements (@_sN = ...@, 'SPLL.PythonNesting'). Whether a line
-- is that deep depends on the program's scale (a 250-value domain, 24 nested
-- ifs), which no IR construct names and the fuzz arms' small programs never
-- reach, so a census of constructs alone would certify a module that does not
-- even import (task batched-enum-comprehension-exceeds-parser-nesting).
batchedProgramCensus :: Either e IREnv -> [String]
batchedProgramCensus = either (const []) census
  where census env = sort (nub (irEnvConstructs inferenceBodies env
                                ++ [ structureSplitLabel | usesStructureSplit env ]
                                ++ [ lineSpillLabel | spillsALine env ]))
        spillsALine env = either (const False) (any isSpillLine . concatMap lines)
                                 (generateFunctionsBatched True env)
        isSpillLine l = case dropWhile isSpace l of
          '_' : 's' : rest@(c : _) | isDigit c -> " = " `isPrefixOf` dropWhile isDigit rest
          _ -> False

-- | The batched census label of a per-structure split (task
-- batched-value-dependent-structure-select).
structureSplitLabel :: String
structureSplitLabel = "Batched:structure split"

-- | The batched census label of a line spilled for CPython's bracket limit.
lineSpillLabel :: String
lineSpillLabel = "Batched:deep line spill"


-- | The constructs of a batched census the batched arm does not certify.
batchedUncertifiedConstructs :: [String] -> [String]
batchedUncertifiedConstructs census = census \\ batchedCertifiedConstructs
