# Pipeline, key types and the AST

Stage order, the core data types, and the `-d` stage dump.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec) → AST (Lang/Lang.hs, Lang/Types.hs)
  → Validator.hs → CalleeNormalize.hs (function values in callee position)
  → Typing/RInfer.hs (return types)
  → Analysis.hs (DiscreteValues tags) → DrawSinking.hs (per-operand draws)
  → Typing/ForwardChaining.hs (chain names)
  → Typing/ModalityInfer.hs (PTypes) → Analysis.hs (IsConditional tags)
  → IRCompiler.hs → IR (IntermediateRepresentation.hs)
     Three compilation branches: generate, probability, integrate
  → IRSelectPass.hs (batched only) → IROptimizer.hs (const folding, CSE, let-in)
  → CodeGenPyTorch.hs, CodeGenPyTorchBatched.hs, or CodeGenJulia.hs
```

`SPLL.Prelude`'s `compile` is the authority on stage order; `-d` dumps the
program after each one.

Every SPLL program compiles into three function variants — **generate**
(forward sampling), **probability** (density/mass at a point), and
**integrate** (probability over a range) — whose availability depends on
tractability, as determined by ModalityInfer. Runtime execution:
`IRInterpreter.hs` (`generateRand` for random sampling, `generateDet` for
deterministic).

## Key Types

- **Expr** (`src/SPLL/Lang/Types.hs`): Main AST. `ExprF` is a small closed
  set — `IfThenElse`, `InjF` (injected functions like plus/mult), `Var`,
  `Constant`, `Lambda`, `Apply`, `ThetaI`, `Subtree`, `ReadNN`. Everything
  else is sugar assembled from those by `SPLL.Prelude`: `letIn x v b` is
  `Apply (Lambda x b) v`, `Uniform`/`Normal` are `Var`s, `cons`/`tCons` are
  `InjF`s.
- **IRExpr** (`src/SPLL/IntermediateRepresentation.hs`): IR after
  compilation — `IRIf`, `IROp`, `IRLetIn`, `IRLambda`, `IRDensity`,
  `IRSample`, etc., plus `IRBuiltin Builtin [IRExpr]` for the tensor
  operations (see `enumeration.md`, "Tensors in the IR").
- **TypeInfo**: `rType` (return type: `TFloat`, `TBool`, `TInt`, `TSymbol`,
  `ListOf`, `Tuple`, `TEither`, `TADT`, `TArrow`, `TTensor Shape RType`
  (see `neural.md`, shaped neural inputs), etc.), `pType`
  (probabilistic: `Deterministic`, `PNormal`, `PLogNormal`, `Integrate`,
  `Bottom`, and `NotSetYet` before inference runs), `chainName`, and `tags`
  (`DiscreteValues`, `IsConditional`). `PType`'s `PArr`/`TVar` are dead code.
- **Value** (`= GenericValue Expr`): Runtime values — `VFloat`, `VInt`,
  `VBool`, `VSymbol`, `VUnit`, `VList`, `VTuple`, `VEither`, `VADT`,
  `VClosure`, `VThetaTree`, `VError`, plus `VAny`/`VAnyExcept` (used only for
  marginal queries).
- **MultiValue**: Structured set of possible values for neural network
  output annotation — `MultiDiscretes [Value]`,
  `MultiTuple MultiValue MultiValue`, `MultiEither MultiValue MultiValue`,
  `MultiADT [(String, [MultiValue])]`, `MultiTypeRef String`,
  `MultiContinuous` (a `Real` leaf), `MultiAuto` (the `_` placeholder).
- **CompilerConfig**: Controls verbosity, optimization level, top-K
  threshold, branch counting, the marginal-materialization cardinality budget
  (`materializationCardinality`, default 10000 — see `enumeration.md`), the per-function enumerated-slot budget (`marginalSlots`, default 4 —
  see `observation-masks.md`), plus flags `pruneAnyChecks`, `noIntegrate`,
  `noProbability`, `noGenerate`, `batched`, `logSpace`.

## Internal Details

Every AST node carries a `TypeInfo` record (`rType` from RInfer, `pType`
from ModalityInfer, `chainName`, and enum/algorithm `tags` from Analysis),
held in a record wrapper around a parametric base functor rather than as
a field on each constructor:

```haskell
data Expr = Expr { ann :: TypeInfo, node :: ExprF Expr }
data ExprF a = IfThenElse a a a | InjF InjFName [a] | Var String | Constant Value | ...
               deriving (Show, Eq, Functor, Foldable, Traversable)
```

A node is written/matched as `Expr ti (IfThenElse c t f)`. The derived
`Functor`/`Foldable`/`Traversable` are what let `SPLL.Lang.Lang`'s
traversals (`tMap`, `getSubExprs`, `setTypeInfo`, etc.) be generic
one-liners. `Constant` deliberately holds a concrete `Value`, not a
`GenericValue a`, since a `Value` can embed `Expr`s inside a `VClosure`
that must stay out of derived traversals. Smart constructors in
`SPLL.Prelude` build nodes through `mkExpr :: ExprF Expr -> Expr`.

`PType` classifies how uncertainty flows through a node, forming a partial
order:

```
Deterministic  >  PNormal, PLogNormal  >  Integrate  >  Bottom
```

`PNormal`/`PLogNormal` are incomparable siblings (different distribution
families) whose meet is `Integrate`. Deterministic values need no
inference; `PNormal`/`PLogNormal` allow closed-form Gaussian shortcuts;
`Integrate` values have a known CDF (via trusted special functions like
`erf`); `Bottom` values offer nothing better than sampling. Each PType
implies the semantics of lower types are available.

## Debug: Intermediate Stage Dump (`-d`)

`showIntermediates :: Bool` (CLI `-d`/`--debugIntermediates`) prints the
fully-annotated AST after each pipeline stage to stderr via
`prettyPrintProg`, showing the progressive accumulation of annotations:

| Stage | What becomes visible |
|---|---|
| After Parsing | All fields `NotSetYet`, tags empty |
| After Callee Normalization | printed **only** when a callee was rewritten — still unannotated (see `callee-normalization.md`) |
| After RType Inference | `rType` populated; `pType` still `NotSetYet` |
| After Enum Annotation | `DiscreteValues` tags appear |
| After Draw Sinking | printed **only** when a `draw` was moved (see `enumeration.md`, "Stacked draws are sunk into their operands") |
| After Forward Chaining | `chainName` fields filled |
| After Modality Inference | `pType` populated |
| After Conditional Annotation | `IsConditional` tags appear on conditioned distributions |
| After IR Compilation (pre-optimization) | Pseudo-code IR before any optimizer passes |
| After Select Pass | `IRIf` → `IRSelect` retagging (a no-op unless `--batched`) |
| After Optimization | Pseudo-code IR after constant folding, CSE, let-in optimization |

Use this to identify which stage introduced a defect when a program
compiles incorrectly. `IRCompiler` selects the inference algorithm per
node directly from the `pType`/`DiscreteValues` annotations visible after
Modality Inference.
