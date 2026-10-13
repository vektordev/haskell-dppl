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
-- The census is taken over every body a program emits (generate included:
-- the sampling primitives aside, a generate body is built from the same
-- constructs as the inference bodies, and the primitives have runtime tests of
-- their own, "TestSamplingPrimitives") and over every config the corpus checks
-- it under ('corpusCensusConfigs').
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
  , corpusCensusConfigs
  , certifiedConstructs
  , programCensus
  , uncertifiedConstructs
  ) where

import Data.Char (isSpace)
import Data.List (nub, sort, (\\))

import SPLL.IntermediateRepresentation
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

-- | The compiler configs the corpus checks a program under (default, log
-- space, the plan engine at materialization budget 0 in both spaces, branch
-- counting, topK in both spaces, the unoptimized pipeline). Each emits
-- different IR, so a census meant to cover what the corpus checks is taken
-- over all of them: the IR fuzz generator's ('BackendCoverage') and M2's
-- per-program one ('programCensus').
corpusCensusConfigs :: [(String, CompilerConfig)]
corpusCensusConfigs =
  [ ("default", defaultCompilerConfig)
  , ("log space", defaultCompilerConfig { logSpace = True })
  , ("budget 0", defaultCompilerConfig { materializationCardinality = 0 })
  , ("budget 0, log space", defaultCompilerConfig { materializationCardinality = 0, logSpace = True })
  , ("branch counts", defaultCompilerConfig { countBranches = True })
  , ("topK", defaultCompilerConfig { topKThreshold = Just 0.05 })
  , ("topK, log space", defaultCompilerConfig { topKThreshold = Just 0.05, logSpace = True })
  , ("-O0", defaultCompilerConfig { optimizerLevel = 0 })
  ]

-- | The constructs the agreement fuzzers compare across the interpreter,
-- scalar Python and Julia: what the IR fuzz generator's fixed-seed sample
-- reaches ('IRFuzz.irGeneratorConstructs', the sample
-- 'TestFuzz.prop_Fuzz_IRBackendsAgree' draws from), sampling primitives aside.
-- A static list so the default tier need not draw the sample; kept exact by
-- @Slow.IRGeneratorCoverage@, so a construct the generator stops reaching
-- leaves it (and the programs using it get their Python and Julia checks
-- back), and one it starts reaching must be added.
--
-- Only the IR generator's reach is counted. It reaches every construct the
-- corpus emits under any config but the sampling primitives
-- ('BackendCoverage.irGeneratorDeferred'), so the typed-program fuzzer's
-- sample, which is costly to draw, would add nothing a corpus program uses.
certifiedConstructs :: [String]
certifiedConstructs =
  -- Measured 2026-10-13 (IRFuzz's fixed-seed sample of 600 cases, after M3):
  -- 78 constructs.
  [ "Accessor:AcFromLeft", "Accessor:AcFromRight", "Accessor:AcFst", "Accessor:AcHead",
    "Accessor:AcIsLeft", "Accessor:AcIsRight", "Accessor:AcSnd", "Accessor:AcSubtree",
    "Accessor:AcTail", "Accessor:AcTheta",
    "Builtin:BIndex", "Builtin:BListIndex", "Builtin:BMap", "Builtin:BMapList",
    "Builtin:BReduce ROpAdd", "Builtin:BReduce ROpLogSumExp", "Builtin:BReduce ROpMax",
    "Builtin:BTensor", "Builtin:BZip OpAnd", "Builtin:BZip OpApprox", "Builtin:BZip OpDiv",
    "Builtin:BZip OpEq", "Builtin:BZip OpGreaterThan", "Builtin:BZip OpLessThan",
    "Builtin:BZip OpMax", "Builtin:BZip OpMult", "Builtin:BZip OpOr", "Builtin:BZip OpPlus",
    "Builtin:BZip OpSub",
    "ConTag:TgCons", "ConTag:TgLeft", "ConTag:TgRight", "ConTag:TgTuple",
    "Cumulative:IRNormal Linear", "Cumulative:IRNormal Log", "Cumulative:IRUniform Linear",
    "Cumulative:IRUniform Log",
    "Density:IRNormal Linear", "Density:IRNormal Log", "Density:IRUniform Linear",
    "Density:IRUniform Log",
    "IRExpr:IRApply", "IRExpr:IRBuiltin", "IRExpr:IRConformsTo", "IRExpr:IRConst",
    "IRExpr:IRConstruct", "IRExpr:IRCumulative", "IRExpr:IRDensity", "IRExpr:IRDestruct",
    "IRExpr:IRError", "IRExpr:IRIf", "IRExpr:IRIsPossible", "IRExpr:IRLambda", "IRExpr:IRLetIn",
    "IRExpr:IROp", "IRExpr:IRSelect", "IRExpr:IRUnaryOp", "IRExpr:IRVar",
    "Operand:OpAnd", "Operand:OpApprox", "Operand:OpDiv", "Operand:OpEq", "Operand:OpGreaterThan",
    "Operand:OpIntDiv", "Operand:OpLessThan", "Operand:OpMax", "Operand:OpMod", "Operand:OpMult",
    "Operand:OpOr", "Operand:OpPlus", "Operand:OpSub",
    "UnaryOperand:OpAbs", "UnaryOperand:OpExp", "UnaryOperand:OpIsAny", "UnaryOperand:OpLog",
    "UnaryOperand:OpNeg", "UnaryOperand:OpNot", "UnaryOperand:OpSign"
  ]

-- | A program's census: the constructs of every body of each of its compiles
-- (one per config it is checked under; a compile the compiler refuses
-- contributes nothing, since nothing of it is run), sampling primitives aside.
programCensus :: [Either e IREnv] -> [String]
programCensus envs =
  sort (nub (concat [ irEnvConstructs allBodies env | Right env <- envs ])) \\ samplingConstructs

-- | The constructs of a census the fuzzers do not certify.
uncertifiedConstructs :: [String] -> [String]
uncertifiedConstructs census = census \\ certifiedConstructs
