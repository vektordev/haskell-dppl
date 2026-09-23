# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository. If ever you notice that information here is outdated
or substantially incomplete, you are requested to edit this file.

## Project

NeST (Neuro-Symbolic Transpiler) — a compiler for SPLL (Sum-Product Loop
Programming), a probabilistic programming language. Compiles probabilistic
programs to Python or Julia, supporting neural network integration and
probabilistic inference (sampling, exact probability, integration).

## Build & Run

```bash
stack build                    # Build
stack test                     # Run all tests
stack run -- -i file.ppl compile -o output.py -l python   # Compile to Python (-o is required)
stack run -- -i file.ppl compile -o output.jl -l julia    # Compile to Julia
stack run -- -i file.ppl generate                         # Forward sampling
stack run -- -i file.ppl probability -x 0.5               # Query P(X=0.5)
stack run -- -i file.ppl cumulative -x 0.5                # CDF query P(X<=0.5)
# Test selection (tasty patterns; `--ta '-l'` lists every group and test name).
# `stack test` runs TWO test-suites (haskell-dppl-test and, separately,
# haskell-dppl-test-corpus for the Corpus group -- see Test Structure below);
# a bare `stack test --ta PATTERN` applies PATTERN to both processes, and a
# pattern that matches nothing in one of them just reports "All 0 tests
# passed" there, not an error. Target one binary explicitly to skip the other
# process entirely, e.g. `stack test haskell-dppl-test-corpus --ta '-p ...'`.
stack test --ta '-p Spec'                # run one group
stack test --ta '-p "!/End2End/"'        # everything except a group
stack test --ta '-p TopK'                # any test whose name matches a substring
stack test --ta '-p "/End2End.Interpreter/ && /dice/"'   # one .ppl test case
stack test --ta '-l'                     # list all test names
# Output is quiet-on-success by default; show every test (with per-test timings) via:
TASTY_HIDE_SUCCESSES=false stack test
```

Global flags (before the subcommand): `-v` verbosity, `-O LEVEL`
optimization (0-2), `-k CUTOFF` top-K threshold, `-c` count branches, `-d`
debug intermediates (see below), and the long-form `--pruneAnyChecks`,
`--noIntegrate`/`--noProbability`/`--noGenerate`, `--noTypeCheck`,
`--batched`, `--logSpace`, `--marginals`, `--marginalSlots N`.
Per-subcommand flags: `--help`.

To prevent having to run `stack test` repeatedly, e.g. to grep for specific
failures, always store the test output to a temporary file and grep that.

### Compiler warnings

`src/` and `app/` build under `-Wall -Wcompat -Wincomplete-record-updates
-Wredundant-constraints -Werror` (set in `package.yaml`; the `.cabal` is
hpack-generated and gitignored) with **zero warnings**, and so does `test/`
under the same flags. The backlog is empty: there are no `-Wno-*` flags in
`package.yaml` and none may be added. Fix the code instead, or -- for a genuine
false positive -- scope an `OPTIONS_GHC` pragma to the one module and say why.

Exactly one module does that today: `test/ArbitrarySPLL.hs` carries
`-Wno-orphans`, because its `Arbitrary` instances for `Program`/`Expr`/`Value`/
`TypeInfo` are test fixtures, and the only way to un-orphan them would be to
declare them in `SPLL.Lang.*` -- putting a QuickCheck dependency on the
library.

The last five to go were three `-Woverlapping-patterns` and two
`-Wdeprecations`, each a real defect rather than noise:

- `juliaUnaryOps` / `RInfer`'s `apply` / `toIRGenerate` each ended in an
  unreachable `error` catch-all over an already-exhaustive match. Deleted:
  `-Wincomplete-patterns` flags a future missing constructor at compile time,
  which strictly beats the runtime `error` the catch-all offered. (The
  neighbouring `juliaOps` catch-all is *not* redundant and stays.)
- `Prelude`'s `pPrintIfVerbose`/`pPrintIfMoreVerbose` used
  `Debug.Pretty.Simple.pTraceShow`, which is `DEPRECATED` precisely to nag
  about leftover debug traces. These are real `-v` functionality, so they now
  compose the non-deprecated pieces directly: `trace (TL.unpack (pShow s))`.

and the two `unused-top-binds`: `IRCompiler`'s `findLambdaVars`, live only via
a commented-out block that referenced three functions (`findBoundVariable`,
`getUnappliedLambdas`, `applyLambdas`) which no longer exist anywhere -- block
and function both deleted; and `PlanWorld`'s `pwFactor`, whose field was only
ever read positionally, so `planWorldMass` now reads its world through the
selectors.

The `test/` pass (168 warnings) was mostly mechanical, but four findings were
not:

- `TestParser`'s `testExpressions`, a table of hand-written lambda/apply
  expressions, had no driver at all -- the module's tests are `$(allProperties)`
  and nothing referenced the table. It now has one
  (`prop_ListedExpressionsRoundtrip`), which passes; that is the 1484th test.
- `TestFuzz`'s `$(allProperties)` was silently skipping
  `prop_Fuzz_SamplingMatchesPDF`, which is defined *after* the splice and so is
  not in scope at it. That exclusion is wanted (the property is a SuperSlow
  tier registered by hand), but it was load-bearing on definition order. The
  binding is now `fuzzSamplingMatchesPDF`, excluded by not matching the `prop_`
  prefix, with the tasty-visible name unchanged.
- `TestParser`'s `programToString` never rendered `data` declarations, and the
  two helpers written for that (`adtDeclToString`/`adtConstructorToString`)
  were unreachable. That is *currently* harmless -- `Arbitrary Program` always
  builds an empty ADT list -- so the helpers are gone and the constraint is
  now a comment on `programToString` instead of silent dead code.
- `ArbitrarySPLL`'s `exprGens` had four entries commented out with three of
  their generators (`mkThetaI`/`mkMultI`/`mkPlusI`) left defined-but-unused --
  and a fourth, `mkGreaterThan`, whose commented entry had outlived its
  definition entirely. All four are retired, with a comment recording that
  re-enabling any of them means writing the generator again.

Two module-wide idioms did most of the mechanical work: `TestCaseParser`'s
`symbol` now returns `()` rather than the matched text no caller wanted (23
`-Wunused-do-bind`s at once), and the shadowing of `Test.QuickCheck`'s
`sample`/`total`/`label`/`collect` and `System.Process`'s `env`/`cwd` was
fixed at the import (`hiding`, or an explicit import list) rather than by
renaming ~50 local bindings.

The two incomplete-pattern categories were retired by filling in the missing
cases, mostly as named helpers that state the invariant and `error` with the
offending value (`soleOutputVar`/`inversionFor`/`lookupFPair` in
`PredefinedFunctions`, `binaryInputVars`/`equivalentLambda`/`inverseDerivative`
in `IRCompiler`, `asLambda` in `ForwardChaining`, `mockLogits` in `MockNN`),
and in a few places by routing a genuine failure into an existing error channel
instead (`Prelude`'s `runProb`/`runIntegNamedC` now answer `Left` when a
definition has no compiled variant for that mode; the `Parser` builder maps
answer `Left` on a wrong argument count). `IRCompiler` carries an
`OPTIONS_GHC -fmax-pmcheck-models=1000` pragma: the coverage checker exceeds
its default 30-model budget on two `Maybe (RType, Bool)` cases and then reports
those exhaustive matches as incomplete.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec) → AST (Lang/Lang.hs, Lang/Types.hs)
  → Validator.hs → CalleeNormalize.hs (function values in callee position)
  → Typing/RInfer.hs (return types)
  → Analysis.hs (DiscreteValues tags) → Typing/ForwardChaining.hs (chain names)
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
  operations (see Tensors in the IR below).
- **TypeInfo**: `rType` (return type: `TFloat`, `TBool`, `TInt`, `TSymbol`,
  `ListOf`, `Tuple`, `TEither`, `TADT`, `TArrow`, etc.), `pType`
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
  (`materializationCardinality`, default 10000 — see Marginal Materialization
  below), the per-function enumerated-slot budget (`marginalSlots`, default 4 —
  see Observation masks below), plus flags `pruneAnyChecks`, `noIntegrate`,
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

### Modality: the layer `PType` projects from

`PType` is not the probabilistic type system but a flat, lossy projection of
one: `Typing/Modality.hs` carries a capability lattice (subsets of
`{CanSample, CanDensity, CanIntegrate, CanExact}`) crossed with orthogonal
support-finiteness and distribution-family axes, and `Typing/ModalityInfer.hs`
infers it bottom-up before `projectGround` flattens it onto the five `PType`
rungs. Read those two modules before changing what an expression is allowed to
do — notably, `PNormal` and `Integrate` are the same capability rung differing
only by family, and `Bottom` is a collapse of four distinct levels.

### An `if`'s arms see a gated variable's conditioned law

`ModalityInfer` infers the two arms of an `IfThenElse` under an environment in
which every *random* let-bound variable the condition reads is rebound to its
law **given the condition** (`conditionEnv`/`conditionI`). In
`let s = Normal in if s < 0.0 then x else y`, the `s` that `x` sees is the
Normal's negative part: a truncated law that keeps every capability the
standalone law had (its density is the original restricted and renormalised,
its CDF the original shifted and rescaled) but belongs to **no family** and is
**no longer witnessed** on that arm (`IWit` says the observation determines
the value on every path; inside one arm it does so only if that arm recovers
it). The condition itself is inferred under the unrefined environment, and a
deterministic condition conditions nothing.

Without this, the arm occurrences were bound at the standalone witnessed
`PNormal`, so `tryNormalClosure` typed `s + Normal` inside an arm as `PNormal`
and `sim_fpi s2 thetas` (a recursive call threading `s2` into a further draw)
as `Integrate`: the program was admitted, the set-witness engine refused it at
compile time ("draws fresh randomness"), and because that refusal is eager it
took the `generate` variant down with it. The sum of a truncated Normal and a
Normal has no closed form any engine implements (one level is an `erf`
expression; the nested stopping-time shape is an orthant integral), so the
honest verdict is `Bottom`: `generate` compiles, `probability` is declined by
`missingVariant`. The shapes that *do* have an engine — the gated value
returned as itself, an affine image of it, a tuple of such parts — keep
`Integrate` and their existing set-witness answers
(`test/cases/distributions/gatedContinuousTruncated`, `letProbAbsNormal`).

The refinement keys off the condition's free variables, not off the
`v < bound` spelling, so `if isNeg s`, `if s * s < 1.0` and `if s < w` all
condition `s`. Pinned by the `conditioning` group in `test/TestModalityInfer.hs`
and `Rejection.GatedContinuousFeedsFreshDraw`.

The same task fixed the Lambda rule's annotation: a curried `f x y = …` node
projected its body — the inner lambda's Dirac closure — as `Deterministic`
whatever the result was, and IRCompiler's variant gate reads exactly that
node's `pType`, so a two-parameter function with a `Bottom` body still had a
probability function compiled (and crashed in it) where its one-parameter
twin was declined. `projectNode` now recurses down the arrow spine, as it
already did for a `Var` referencing the function; IRCompiler's `pt` and
`ptUnderLambdas` therefore agree.

### Inference for non-invertible observations

Two IRCompiler engines handle `let`-bindings whose observation can't be
point-inverted onto the bound variable: **plan-guided lazy enumeration**
(`planWitnessApply`, for observations over a neural network's structured
output) and **set-valued witnesses** (`setWitnessApply`, for observations
that cross a comparison or `if`). Plan enumeration is tried *before*
forward-chaining point inversion, whose inverses would otherwise crash on
those shapes; set-valued witnesses are the fallback *after* it, taken when
no occurrence of the bound variable is point-invertible at all. Full
mechanism, examples, and the `test/cases/plan-enumeration/planEnum*` pointers:
`docs/witness-inversion-engines.md`.

A plan world can carry **independent factors** (`PlanWorld`'s `pwFactors`):
a body subtree mentioning no plan-bound variable is independent of the plan,
so the joint factorizes — the subtree is compiled by the ordinary probability
compiler against the same target and multiplied in with `prodP` (dims and
branch counts add). `planFactorFree` handles a whole plan-free subtree,
`planFactorBool` a plan-free `if`-condition (its two polarity masses become
the branches' mixture weights). Before this, the traversal accepted a
plan-free subtree only when it was `Deterministic`, so a neural declaration
and any fresh randomness could not appear in one probability-mode body.
Corpus `test/cases/plan-enumeration/planFreeStochastic*`. Still refused as genuinely
non-factorizable: value enumeration of a plan-free stochastic subtree, and a
comparison operand convolving a plan leaf with fresh noise
(`snd o + Normal * 0.5 > 2.0`).

Independence there is not assumed, it is **checked**. Occurrence-freedom makes
a subtree independent of the *plan*, whose randomness is the net's alone; it
does not make two factors of the same world independent of *each other*. Fresh
distribution leaves and top-level calls are per-occurrence draws, so the only
shared source reachable from the traversal is a variable bound by an enclosing
`let` — which SPLL's `let` makes a single shared draw
(`designs/let-binding-semantics.md`: the existing form is the eager one). The
traversal cannot descend into a `let` (`collectApply` declines a Lambda callee,
`classifyArg` declines a non-deterministic argument), but an *enclosing* one
puts its variable in scope, so `planFactorExternals` refuses any factor reading
a non-`Deterministic` local of the ambient scope. That shape has no end-to-end
spelling today — the outer engine refuses every such binding first — so the
guard is pinned white-box in `TestInternals`
(`plan factorization independence guard`) rather than by a corpus program.

A set-witness world can carry **residue factors** (`WWorld [guard] WSet
[PResult]`): when `transportDirect` inverts a single-occurrence subtree
through a field constructor (`(x, e)`, `x : e`, a user ADT constructor, also
under `right`), the deconstructing inverse (`fst s`) never consults the
sibling `e`, so the subtree is additionally compiled against its target with
the bound variable fixed at its witness (`residueFactor`, the point-witness
body-factor fold per world) — a dim-0 consistency indicator for a
deterministic sibling, the sibling's own density for a fresh draw. Without
it `if x > 0.5 then (x, 1.0) else (x, 0.0)` answered `1.0` at `(0.7, 0.0)`.
Corpus `test/cases/set-witness/setWitnessSibling*`.

An interval constraint reaching the bound variable through a chain of
monotone `InjF` steps is transported by `toSeededMonotoneInvExpr` (direction
table `stepMonotonicity`), with each step's input first clamped into that
step's forward image (`injFImage`/`clampToImage`, same module) — an
endpoint the forward function can never produce, like the `-1` in
`exp x > -1.0`, must not reach the partial inverse (`log(-1) = NaN`, which
the empty-interval clamp then turned into a silent zero). The plan engine's
`planPeelSlice` reads the same table (`peelBound` clamps, `peelPoint`
guards). Adding a monotone step whose inverse is partial means adding its
image there too. Details in the doc above; corpus
`test/cases/set-witness/setWitnessTransport*`, `test/cases/plan-enumeration/planEnumContExp*`.

### Callee Normalization

Probability mode compiles `Apply l v` by inverting the observation through
`l`'s body, which presupposes `l` names a lambda the compiler can see:
`ForwardChaining.findEquivalentExpression` has to resolve `l`'s chain name to a
`LambdaInfo`. That holds for a lambda literal and for a bare name (a top-level
function, or a `let`-bound one -- FC's equivalence classes walk through a
variable). It fails for every *other* way a program can produce a function
value, and the failures were not graceful: a lambda projected out of a tuple or
taken from a list hit an internal "should resolve to a lambda" `error`, and one
chosen by an `if` compiled a mixture that multiplied a branch weight by a
closure and died in the interpreter with a type error at run time.

`SPLL.CalleeNormalize` removes the selection rather than teaching each engine to
see through it. Two purely syntactic rewrites, run by `Prelude.compile` on the
freshly parsed program (before RInfer, so every node it builds is annotated by
the rest of the pipeline like any other, needing no re-chain-naming round of its
own):

- **An `if` in callee position is distributed into its arms**:
  `(if c then f else g) v` becomes `if c then f v else g v`. The arms are
  alternatives, so no draw in `v` is duplicated -- only one arm is ever realised
  -- and the result is the ordinary mixture the `IfThenElse` rules already
  compile, over the two applications' *probabilities* rather than over closures.
  This is what makes a probabilistic function value a real capability
  (`test/cases/higher-order/arrowApplyRandomFunction`) instead of a runtime crash.
- **A callee denoting a lambda literal is replaced by it**: `fst`/`snd` of a
  tuple literal, `head`/`tail` of a list literal, and `let`-bound names standing
  for either, reduced until a `Lambda` falls out. Only a reduction that bottoms
  out at a lambda is taken, so nothing else is ever moved.

The one selection it deliberately leaves alone is a **bare name** in callee
position, precisely because that is the one FC already resolves. An earlier
draft substituted those too and moved two working programs onto a different
path: `hoProbValueLambda` (`(\x -> x 1.0) (\y -> Uniform + y)`) became a dead
binding whose arrow-typed probabilistic argument arm generates rather than
infers, tripping the central generate-backed-body guard, and `twiceApplication`
stopped being refused by batched mode. It also would not terminate on a
recursive function. Descending under a binder drops every environment entry
whose value mentions that name, so a lambda is never moved into a scope where
one of its free variables means something else.

Corpus: `arrowApply*` (the probe table of investigation
`modality-function-space-test-coverage`, rows 1-6 and 8). Row 7,
`(\x -> x + x) Normal`, is a *wontfix* precision gap -- the family layer is
right that `2X` of a Gaussian is Gaussian, but the set-witness engine cannot
propagate an observation onto a variable occurring on both sides of its own
sum -- and is pinned as a refusal by `TestRejection`'s `ArrowApplySelfSum`.

A second, independent half of the same task: the `PNormal`/`PLogNormal`
catch-alls in `IRCompiler` now also decline a **local `Var`** and an
**`IfThenElse`**, neither of which `toIRNormalParams` has any `(mu, sigma)` to
read off, so the catch-all could only ever reach its fallthrough `error`.
A local `Var` is reached by a nested `let` (`let x = Normal in let y = x + 1.0
in y`: the body-factor fold retypes `x + 1.0` Deterministic but leaves `y`
labelled `PNormal`), and `hasOwnInferenceHandler` now asks the type environment
the same `Just (_, False)` question the `Var` equation itself dispatches on. An
`IfThenElse` is a mixture -- of two Gaussians it is not a Gaussian -- and its
own equation measures the arms and mixes them, which is right whether the
condition is deterministic (`ifSelectNormalDet`, which `TestModalityInfer`
already typed `PNormal` while the pipeline crashed on it) or probabilistic
(`ifSelectNormalMixture`, an even mixture of `N(1,1)` and `N(0,2)` that now
answers exactly). `isNormalExtractable`, the mirror predicate gating whether a
top-level function gets a `normalFun` at all, excludes `IfThenElse` for the same
reason. Corpus: `letChainNormalVar`, `letChainNormalVarTuple`,
`ifSelectNormalDet`, `ifSelectNormalMixture`.

### An arrow-typed `if`-mixture is lifted pointwise, not multiplied

`CalleeNormalize`'s `if`-distribution rule only reaches a selection *syntactically
in callee position*; a probabilistic function value reached any other way --
notably `let f = if Uniform < 0.5 then g else h in f v`, where `f` is a bare
name applied elsewhere -- still compiled a mixture that multiplied a branch
weight by a `VClosure` (`Mult can only multiply numbers ...: VClosure`), since
`toIRInference`'s `IfThenElse` equation treated each arm's `rProb` (itself a
closure, `detP (IRLambda ...)`, for an arrow-typed arm) as a scalar to
`prodP`/`mixP`.

Before that arithmetic is ever reached, `ForwardChaining.constructEquivalenceClauses`
builds a certificate for *every* `Apply` node unconditionally, and its `TArrow`
branch (the per-invocation tagging machinery for a function-valued binding)
assumed the bound value always resolves to exactly one lambda body via
`getEquivCN` -- an if-selected mixture has no such single body, so this crashed
first, one layer earlier than the arithmetic bug ("Found no equivalent chain
name to: ..."). `getEquivCNMaybe` makes that lookup recoverable; when it fails,
the branch degrades to just the Apply-is-equivalent-to-its-body clause (no
tagging) rather than erroring -- sound because nothing on the mixture's own
compilation path below ever consults that tagging for this shape.

`toIRInference`'s `IfThenElse` equation now dispatches on the arms' `rType`: for
`TArrow`, it builds a **new closure** over a fresh argument, whose body opens
each arm's own closure at that argument (`unpackResult (IRApply armClosure z)`,
let-bound once each to avoid `unpackResult`'s four-way destructuring
duplicating a possibly-expensive call) and runs the *ordinary* scalar
`weighByCond`/`mixP` combinators on the opened, scalar results --
`mix(p_c, t, g) == \z -> mix(p_c, unpack(t z), unpack(g z))`. `shareResult`'s
existing dead-arm guard carries over unchanged, so an arm whose condition
cannot hold is still never evaluated. topK pruning is not implemented on this
path (it always computes the exact, unpruned mixture -- a valid refinement of
what pruning would have approximated, never a regression from the pre-fix
crash) and the scalar path is untouched. Corpus:
`arrowApplyLetBoundRandomFunction`.

Two closely related shapes are deliberately **not** covered yet and are filed
separately, since they turned out to be blocked by different bugs, not by this
mechanism: a curried multi-argument selection in callee position (blocked by
`CalleeNormalize`'s own curried-spine gap) and a *named function's* call
resolving to an if-selected lambda, even with no randomness involved (a
different `ForwardChaining` crash, in the `l`-side resolution of the same
`constructEquivalenceClauses` function). See task
`arrow-lifted-mixture-for-function-values` and its `depends_on`.

### Forward chaining never re-derives a chain name it already has

`ForwardChaining.solveHCSet` fulfils, per clause group, the first clause whose
premises are all known **and whose conclusion is not already derived**. The
second half of that test is what keeps the fulfilled clause set acyclic, and it
is a correctness requirement, not an optimisation.

A chain name reachable by two routes makes it bite. In an over-determined
observation — `let x = Uniform in let y = Uniform in (x, (x+y+3, x+y+2))`, where
both inner slots recover `y` and hence `x` — each occurrence of `x` sits in its
own bidirectional equivalence group with the binding. Chaining reaches the
binding through slot 1, walks all the way round through the second slot's
occurrence, and (without the test) fulfils a *second* clause concluding the same
binding, closing a cycle. `topSortDAG` has no defined behaviour on a cycle and
`cutList` then truncates, so codegen emitted a shadowing `let ast18 = ast14`
over an `ast14` no earlier clause binds — `Variable ast14 not declared` at run
time, on every backend, with the query having type-checked and compiled
cleanly.

Dropping the second derivation loses nothing: forward chaining's premise
throughout (`mergeExpr`'s candidate merge says so explicitly) is that two routes
to a name are semantically equal. The redundancy is still *paid for* — the
observation's manifold constraint is carried by the deterministic-slot
consistency check IRCompiler emits for the query as a whole, a dim-0 indicator
factor, so `p((a,(b,c)))` above is `p(a)·p(b−a−3)·[c−b == −1]` at dim 2.
Corpus: `overDeterminedSharedLatent`, `degenerateSameLatentSum`.

### Enumerated branches are compiled forward, and that premise is checked

`toIREnumerate` compiles the condition and both arms of an enumerated
conditional with `toIRGenerate` and compares the result against the sample. That
is exact only while the operand is **deterministic given the enumerated
latents** — the premise its own fallback equation states. Where the premise
failed, the same code emitted a fresh random draw compared against the query
value: a "probability" returning a different number on every call with the same
argument, with no crash and no diagnostic on the Python and Julia backends.

The reachable shape is unbounded self-recursion with no decreasing argument
(`main = let a = genA in let b = genB in if a == b then a else main` — resample
and retry on disagreement), which spliced `main_gen()` into `main_prob`.
`dice.ppl`-style recursion is unaffected: it recurses on `x + (-1.0)`, which
statically decreases.

`requireDeterministicUnderEnum` now checks each generated operand and refuses at
compile time, naming the generator it would have called — matching the sibling
witness-construction failures, which fail loudly. Solving the fixed point
algebraically (the marginal *is* closed-form for that program) was declined: it
would make "does my program infer?" unpredictable from the source. The refusal
is lazy and lives inside the prob/integ bodies, so `generate` and
`--noProbability --noIntegrate` compiles of such a program still work.

The purity verdict is the optimizer's own `isPureGiven` (an `IRSample`, or a
`_gen` reference not proven deterministic), told which generators are
deterministic by `CompilerMetadata.detGenNames` — built once per compile from
`Typing/Determinism.functionSummaries`. `isEffectfulVar` alone is a name test
that calls *every* `_gen` reference random, and an enumerated inference body is
written almost entirely in terms of deterministic helper calls, so a name test
would refuse the whole corpus.

Two things this is **not**. It is the local guard for the enumeration path only;
the central "no `generate` call in any probability-mode body" invariant is the
docs-repo investigation `generate-backed-inference-sweep`. And it needed a
soundness fix in `Determinism` first: a *nullary* top-level function is
referenced as a bare `Var` with no `Apply` node, so `genA` in `let a = genA`
fell through to the unbound-name `True` default and a whole random draw was
reported as a known anchor. `detExpr`'s `Var` rule now consults the call-graph
summary, which can only move `True → False` and so under-approximates in the
direction the module already documents as safe.

### `observe` (Maybe-valued conditioning)

`observe base pred` is parser sugar, not a dedicated `Expr` constructor —
it desugars to `let v = base in if pred v then right v else left ()`
(`Just x = right x`, `Nothing = left ()`), giving
`p(Just v) = p(base = v) · p(pred v)` and, via structural `ANY`
marginalisation, a proper `Maybe`-valued distribution for free
(`p(Just ANY) + p(Nothing) = 1`). Conditioning is
`p(Just v) / p(Just ANY)`.

The base must be let-bound, not spliced in twice (else a probabilistic
base becomes two independent draws), and a literal lambda predicate is
beta-reduced at parse time — otherwise the bound variable is invisible to
inversion and compilation fails.

On a **continuous** observation the denominator `p(Just ANY)` is answered by
the set-witness engine: a wildcard in a constructor slot leaves the tag pinned
but the payload unconstrained, so the point constraint is dropped and the
observation's interval kept, measured as a CDF difference (dim 0) rather than
a density. `intersectSet` spells that as `WChoice`, a *runtime* choice of
constraint set — the wildcard is a property of the query sample and has no
static trace in the witness template.

`invertToWorlds` has cases for the boolean connectives (`and`/`or`/`not`), so
`(v > lo) && (v < hi)` compiles the same as the nested-if spelling: each leaf
is inverted at both canonical polarities (`invertBoolToWorlds`, reusing
`invertToWorlds` itself the same way the `IfThenElse` condition case already
does), then recombined. `and`/`or` at their "natural" polarity (and+True,
or+False) intersect directly; the other polarity needs a disjoint
decomposition (`not(a&&b) = not(a) or (a&&not(b))`, `a||b = a or
(not(a)&&b)`) so the two possibly-overlapping sets of worlds are never both
measured — getting that wrong double-counts the overlap. `not` just swaps
which list is which. Mirrors the plan-guided engine's analogous
`planInvert`/`planInvertBool` fold over (True-worlds, False-worlds) pairs.
Corpus: `observeTwoSidedIntervalAnd` (the `&&` twin of `observeTwoSidedInterval`)
and `observeDisjointTails` (`||`, the double-counting canary).

## Additional Features

### topK Branch Pruning

`topKThreshold :: Maybe Double` in `CompilerConfig` enables
probability-based branch pruning. The compiler threads an `accProb` (the
probability of reaching the current point) through inference; each
`IfThenElse` arm in probability mode is guarded on its *accumulated* path
probability (`accProb * p_cond`) against `TOP_K_CUTOFF`, and an arm below
the cutoff is dropped. The same threshold filters enumerable `InjF`
branches by `accProb * p_left`.

Pruning is **lossy** — a dropped branch's mass is simply gone. Hence the
one-sided invariants: topK never *inflates* a probability
(`Corpus.TopKNeverInflates`, its CDF twin `Corpus.TopKNeverInflatesCdf`, and
the fuzz property `prop_Fuzz_TopKNeverInflates`), and only threshold 0 is
exact (`Corpus.TopKZeroThreshMatchesExact`).

"Never inflates" holds only at equal dimension. Pruning removes alternatives
from a mixture, and the mixture reports the *lowest* dim among the
alternatives it still has, so the pruned dim can only rise — and a pruned
point mass can leave a sibling density behind
(`test/cases/topk-pruning/topKPrunesMassArm`: exact `(0.05, dim 0)` at `1.0`, pruned
`(0.95, dim 1)`). A mass and a density are not comparable, so the properties
compare values at equal dim and otherwise require the pruned dim to be the
higher one.

### A pruned probability is a lower bound — and complements are not

A pruned result is a **lower bound** on the exact one, and lower bounds
compose under products, sums and the lowest-dim-wins mixture — but not under a
complement or a subtraction: `1 − lower` and `a − lower` are *upper* bounds.
`IRCompiler.unpruned` (accumulated probability seeded with `∞`, which fails
every "below cutoff" test in both semirings and crosses a call boundary as a
plain argument) therefore compiles the operand of every such site with pruning
off, and any new `srComplement`/`srMinus`/CDF-difference site must do the
same:

- an `IfThenElse` *condition* (its False-weight is the complement of its
  True-probability — `test/cases/topk-pruning/topKComplementCondition`, the minimized shape
  of the fuzz counterexample this was found by: a condition that is itself an
  `if` had its True-probability pruned to `0`, so its else-weight became `1`);
- the integral behind a `gt`/`lt` against a deterministic bound
  (`topKComplementBound`);
- both operands of the `AnyExcept` subtraction `p(ANY) − p(v)`
  (`topKComplementAnyExcept`; a pruned marginal could even go negative);
- an inverted operand in cumulative mode whose transform is not statically
  increasing, since `scaleCoV` then flips its CDF through a complement
  (`topKComplementCdfFlip`; `covOperandMeta`/`staticallyIncreasing` — `plus`
  declares a literal `1` and stays pruned, `neg`'s `-1` and `mult`'s runtime
  `1/a` do not);
- both bounds of a set-witness interval measure (`cdfAtBound`).

The alternative — inferring a condition at both polarities, each pruned — was
rejected: it is the O(2^d) double compile the `IfThenElse` case retreated from,
and it would not have helped the subtraction sites anyway.

Separately, an `_integ` function takes no `acc_prob` parameter, so a
cumulative-mode call into another definition passes only the sample
(`inferenceCall`); passing the accumulator there applied the callee's result
tuple to a second argument, and every topK CDF query through a call crashed
with "Expression is not a closure" until `TopKNeverInflatesCdf` reached
`varAlias`.

### Marginal Materialization

A point query on a nested enumerable `InjF` chain (`readMNist(a) ++
readMNist(b) ++ …`) re-descends into its left operand once per enumerated
value, and that descent is *eager* — so an n-term chain costs
`T(n) = |D(n-1)|·T(n-1)`, super-exponential. No optimizer pass recovers
it: the recomputation is a runtime loop re-entry, not duplicated IR.

**Tier 0 materialization** replaces it with a streaming convolution. When
an *operand* is itself such a chain, its marginal is tabulated once over
its finite domain — one let-bound scalar cell per value, each cell an
unrolled convolution over the operand grid — and the loop body reads a
cell instead of re-descending. Measured on n-term digit addition (emitted
Python): 14x faster at n=4, 87x at n=5, 626x at n=6, ~3900x at n=7
(52.8s → 0.014s), with neural-cell evaluations going from ×10 per added
term to exactly quadratic.

Three things make it cheap, and each is load-bearing:

- Cells are **let-bound scalars, not an IR table**. `IRExpr` has no dense
  array and `IRIndex` is an O(n) cons-cell walk, so a runtime table would
  turn the `O(n·range)` DP into `O(n·range²)` on the path the whole
  corpus runs on.
- Only an operand that is **itself** a nested enumerable `InjF` is
  tabulated; the queried node keeps the ordinary path. Tabulating the
  queried node would be a pessimization for an invertible op (its point
  query costs `O(|D_left|)`, its table `|D_left|·|D_node|`, and one cell
  is read). A two-term program's emitted IR is therefore unchanged.
- Tables are built by evaluating the InjF's **forward** function at
  compile time over the operand grid (`propagateValues`, the same
  evaluator Analysis uses for the domains), never by inverting — so
  forward-only ops (`and`/`or`/`max`) need no special case, and cell terms
  accumulate in the same order the enumeration loop does, making the
  result bit-identical to the path it replaces rather than merely close.

`topK` is preserved exactly: `accProb` is only modified at an
`IfThenElse`, so every level of a chain shares one `accProb` and the
per-term guard is the same test on the same value, dropping exactly the
terms the in-loop cutoff drops. `rImposs` is deliberately not tracked per
cell — the enumeration paths already discard a sub-result's dim, branch
count and flag, deriving the node's own flag from the summed mass via
`opaqueMass`.

Two preconditions gate it, and both refuse rather than analyse:

- **Decomposability** (`materializationVerdicts`): tabulating two
  operands separately is wrong if they share an enumerated latent
  (`test/cases/let-bindings/letThreadEnumerable` is the canary,
  `test/cases/let-bindings/sharedLatentNestedChain` the nested one). Unlike
  `injFLatentVerdicts`, this walk binds lambda parameters, each to a
  latent identity of its own.
- **Cardinality** (`materializationCardinality :: Int`, default 10000, in
  `CompilerConfig`): `Analysis.materializationDomain` is a total
  predicate over a node's tags returning the domain to tabulate or
  `Nothing`; anything unannotated, non-finite, or over budget answers
  `Nothing`, since over-refusing costs performance while under-refusing
  costs correctness silently. The same budget bounds the operand *grid* a
  convolution unrolls — "the domain is small" and "the unrolling is
  affordable" are one question, not two, and a change to either has to be
  made on both. Per-node, deliberately not cumulative across nesting
  levels. Set it to 0 to disable materialization entirely (the
  differential tests' off-switch).

A leaf cell holds a whole compiled sub-inference rather than a few
references, so it is the one place materialization multiplies IR instead
of rearranging it. `pointQueryTable` compiles the first value as a probe,
measures it, and declines the table unless the copy is small
(`maxTabulatedLeafNodes`) and the total fits the budget — a `ReadNN`
digit read is 10 IR nodes, while an arbitrary enumerable if-tree can be
thousands, where copying per value cost 14x the IR and turned a 0.17s
compile into 16s.

### Agreement fusion: two categoricals multiply in O(V)

Combining two categorical variables by **agreement** — `let a = camNN i in
let b = depthNN d in if a == b then right a else left ()` — is the
product-of-experts shape: the kept mass is `P_a(k)·P_b(k)` per class and
`Z = Σ_k P_a(k)·P_b(k)` is the fusion evidence. It compiled to a *joint*
enumeration, O(V²), evaluating the second expert's marginal V times per
outer value. Correct, and unusable at the vocabulary scale it exists for.

`IRCompiler.enumerateAgreement` rewrites the double sum into dense vector
algebra over the shared domain. Writing `T`/`E` for the two arms' masses
against the query and `Sb = Σ_k pb(k)`:

```
Σ_j pa(j) · Σ_k pb(k) · ( [j==k]·T(j) + [j≠k]·E(j) )
  = Σ_j pa(j)·pb(j)·T(j)          -- the diagonal: the elementwise product
  + Σ_j pa(j)·(Sb − pb(j))·E(j)   -- everything off it
```

Four `BMap`s build the `[V]` vectors, `BZip` (with the semiring's *own*
multiply — `OpMult` linear, `OpPlus` in log space, which is why `Semiring`
gained `srTimesOp` alongside `srReduceOp`) is the elementwise product, and
`BReduce` sums. Measured on emitted Python over two decades of domain size,
against the same source compiled the old way: V=10 0.028ms vs 0.305ms,
V=100 0.229ms vs 25.5ms, V=1000 2.20ms vs 2551ms — fused time grows 78x
across a 100x domain, the joint path 8366x. Bit-identical on the diagonal,
within 9e-16 on the complement.

The off-diagonal subtraction is **forced, not chosen**: any O(V) form of
"sum over everything but the diagonal" is the total minus the diagonal,
because summing those terms directly is the O(V²) being removed. It is
spelled with `srMinus` (so log space gets `logSubExpIR`) and loses precision
only as agreement approaches certainty — the same cancellation the
`AnyExcept` site already accepts.

Six refusals, each falling back to the ordinary enumeration so behaviour is
exactly as before:

- **branch counting** (`-c`) and **topK**. The fused artifact traverses
  fewer leaves, so its `bc` is legitimately not the enumerated path's, and
  topK's per-branch cutoff has no per-branch site to hang on. Refusing keeps
  every existing `-c`/topK number intact — and turns the corpus's own
  "branch counting doesn't change the probability" property into a
  differential test of fused against unfused, which is how the fusion is
  covered at every corpus query point rather than only where a `.tst` says so.
- **the max-product semiring**, whose `srMinus` is `mapHasNoExcept` for the
  same reason the algebra above is sum-product-only.
- **an arm that reads the inner variable**, where the off-diagonal sum does
  not factor and no O(V) form exists.
- **unequal domains**, a shape error for the product.
- **operands that may share an enumerated latent** — the correctness gate,
  and the only one whose failure would be a silent wrong number. Answered by
  `latentVerdicts`, the decomposability analysis (design
  `materialize-discrete-marginals`) which until now had *no consumer*: it is
  keyed by binary-`InjF` chain name and the agreement condition `a == b` is
  a binary `InjF`, so the scope-correct verdict for exactly these two
  operands is already computed. Canary: `test/cases/neural/agreementSharedLatent`.

Corpus: `categoricalProductFusion` (hand-derived posteriors, non-uniform on
both operands, including the zero-product impossibility rows),
`agreementSharedLatent` (the refusal), and the pre-existing
`showcase_poe_discrete`/`observeDiscretePoE`, whose pinned values are
unchanged by the rewrite. Structural coverage is
`TestInternals.agreementFusesToElementwiseProduct`, which asserts the fused
body has no reduction inside a loop body while the same source under `-c`
does — a shape assertion rather than a wall-clock one, since the timing
belongs in `benchmarks/stressAgreementProduct.ppl`.

**Not yet fused**: a *conjunction* of agreements, `if (v == c) && (v == d)`,
which is how `showcase_poe_with_prior` and `showcase_poe_three_sensors`
spell three-way fusion. Those stay O(V²)/O(V³).

### Tensors in the IR

`IRBuiltin Builtin [IRExpr]` carries five operations over a **tensor** — a
statically-shaped, flat, homogeneous block of values (`VTensor Shape [Value]`,
row-major, outermost axis first), as against `VList`'s cons spine:

| builtin | shape | means |
|---|---|---|
| `BTensor sh` | variadic, `shapeNumel sh` args | build a tensor from its elements |
| `BMap` | `[IRLambda v body, t]` | elementwise map, shape-preserving |
| `BReduce op axis` | `[t]` | fold along `axis` with `op`, dropping it |
| `BIndex axis` | `[t, key]` | read along `axis` at a runtime key, dropping it |
| `BZip op` | `[a, b]` | elementwise binary `op` over two same-shaped tensors |

`Shape`/`Extent` live in `Typing/RType.hs`, because the typed surface tensor of
the `tensors-in-core-language` design is `TTensor Shape RType` over the same
type. `Extent` is a one-constructor sum (`EFixed Int`) deliberately: admitting
shape *variables* later is then a new constructor rather than an arity change
to every shape pattern.

**The map binds its variable by taking an `IRLambda` argument**, not by
carrying a `Varname` field. That keeps the flat argument list, and most generic
passes then need no new case at all — `freeVarsIR`, `binderOf`, CSE scoping and
`allNamesIR` already handle `IRLambda`. Three places *do* need to see through
it, because they would otherwise refuse or mis-scope a compile-time unroll:
`IRSelectPass.isTensorFragment`, `CodeGenPyTorchBatched`'s `batchedGuard`, and
`IROptimizer.loopBinder` (which is also the one place listing which forms
iterate, so the loop-invariance analyses stop re-matching a constructor set).

**An enumerated sum is built in this form and no other.**
`SPLL.Semiring`'s `enumSumNode` emits `reduce op (map (\v -> body) domain)`,
where `op` is `srReduceOp` — so a new reduction is a `ReduceOp` case, not a
constructor. `enumSumP`'s branch-counting path emits **one** let-bound map
reduced **twice**, once for the probability and once for the branch count,
which is the loop-body sharing that needs no second traversal of the body.

There used to be three `IRExpr` constructors here — `IREnumSum`,
`IRLogEnumSum`, `IREnumSumPaired` — plus a whole pipeline stage
(`SPLL.IRTensorPass`) lowering them into the above. Task `retire-irenumsum`
deleted all four: the producers build the tensor form directly, so there is
nothing left to lower. `IRExpr` went from 23 constructors to 20, and the
`-d` dump lost its "After Tensor Lowering" row because the stage is gone.
Emitted code is byte-identical for a default compile; a `-c` (branch-counting)
compile differs only in generated variable names, the loop axis now being named
by `mkVariable` rather than by the pass's own counter.

`IRIsPossible` is the deliberate **residue**: it also carries a `MultiValue`,
but it is a membership *test*, not a loop, emitted as a single
runtime-library call (`isPossible`) that walks the value against the domain
description. Putting it on the dense axis would mean materialising the domain
as a tensor and reducing an equality map with a boolean OR — a reduction
operator existing for no other purpose — so it stays as it is.

Only **rank 1 and axis 0** are emitted. The representation admits any rank and
the interpreter implements it (`fibres`/`rewrap` do the stride arithmetic, and
`Internals/tensor builtins` pins the layout); the three backends refuse higher
rank with a named diagnostic rather than emitting something plausible. Nothing
produces a rank > 1 tensor today.

One refusal this form does **not** preserve: `--batched --logSpace`.
`CodeGenPyTorchBatched`'s `emittable` used to have no `IRLogEnumSum` case (and
refused the log variant of `IREnumSumPaired` explicitly), so a log-space
batched compile was rejected at the guard. There is no such node to reject any
more — a log-space enumerated sum is a `BReduce ROpLogSumExp`, which
`emittable`'s blanket `IRBuiltin{} -> True` admits and which `tensor_logsumexp`
in `pythonLibBatched.py` implements. The combination compiles and gives correct
answers, so this reads as a capability gained for free rather than a hole; but
nothing in the suite covers it (no `.tst` carries a log-space token).

The non-scalar `MultiValue` gate those cases also carried is *not* lost. A
domain's values are now ordinary `IRConst` children of a `BTensor`, and
`batchedVal` refuses each composite one for the same reason
`scalarDiscreteMulti` did — so the refusal is per-constant rather than
per-node. `IRIsPossible` keeps its own `scalarDiscreteMulti` gate, and the
synthetic rows in `TestInternals.batchedRefusalUnitTests` (which had no corpus
trigger) now cover that node alone.

Measured when the lowering first landed, against the compiler before it:
emitted scalar Python is 0–4% *smaller* and 1.09x faster with bit-identical
results; batched Python is
byte-identical in size and 1.00–1.04x, bit-identical at two enumeration terms
and within 7.5e-9 at four (the reduce reassociates). The larger speedups the
design predicts belong to the `BIndex` consumer, which nothing wires up yet.

### Dimension Counting

Every probability-mode result is a
`PResult { rProb, rDim, rBranches, rImposs }` whose `rDim` tracks
dimensionality: `0` for a discrete mass, `1` for a univariate density, `n`
for multivariate. This determines whether the change-of-variables
correction applies when a value passes through an invertible `InjF`
(multiply by `|derivative of inverse|` when `dim > 0`, nothing when
`dim = 0`). Dimensions **add** under multiplication (independent
continuous variables); under mixture, the **smaller dimension wins** among
possible alternatives. Base cases: `Normal`/`Uniform` emit `dim = 1`;
discrete/deterministic expressions emit `dim = 0`.

### Probability internals (`PResult` / `Semiring`)

`PResult` is built from a combinator vocabulary in `SPLL.Semiring`
(`density`/`mass`/`detP`/`prodP`/`mixP`/`mixSubP`/`enumSumP`/`scaleCoV`/
`shareResult`) rather than hand-written per case, and `rProb` can only be
constructed by routing through it — or one of two escape hatches,
`unsafeLinearP` and `sealP`, for subsystems that assemble bespoke
`IRExpr` formulas (grepping `unsafeLinearP` finds them). Every
probability is computed through a `Semiring` record that's either linear
or log-space (`logSpace` in `CompilerConfig`, CLI `--logSpace`), fixed for
the whole compile. **Never hand-write a linear identity on a
probability** — use `srComplement`/`srZero`, not raw arithmetic, since
under log space those are silently different numbers. Full vocabulary,
the rest of the log-space gotchas, and the `shareResult` zero-guard
placement bug: `docs/semiring-presult-internals.md`.

`anySafe` guards each of the four `PResult` fields with its own `isAny` test
and wraps each in the sub-result's let-in block, so a block **two** fields read
was emitted twice — and for an enumerated sum that block holds the most
expensive node in the program. `opaqueMass` let-binds the sum precisely so the
impossibility flag reads the value rather than recomputing it; the per-field
wrap then undid exactly that, handing `rProb` one copy of the enumeration and
`rImposs` (only `that value == srZero`) another. CSE cannot merge them and
should not: the copies sit in the else-arms of two different `isAny` ifs, so
sharing them means hoisting the enumeration above the guard whose job is to
skip it on a marginal query.

`anySafeShared` binds the packed result once instead, on `shareResult`'s rules
— only the fields that actually read the block go into the tuple, so a
statically-known dim or flag stays the constant it is rather than being hidden
from folding. It is gated on `blockIterates`: share only when the block
contains a **loop** (`IRMap`, `BMap`, or `BReduce`). That gate is
a claim about run time, not size — what makes a second copy cost anything is
that it is a second traversal, and a block of constants and arithmetic folds to
a few literals whether copied or not. A pre-optimization node count was tried
first and is the wrong question: `test/cases/arithmetic/equalsCoin` builds ~100 nodes that
fold to four literals, passing any size gate with nothing worth sharing.

Measured over the corpus: emitted scalar Python totals 68% of its former size
(`clevrEqualLargeMetalSphere*` 2.8x smaller, the `mNistAdd` family 1.6–1.8x),
`mNistAdd4`'s probability function goes from two enumeration passes and 62
neural-forward call sites to one and 31, CLEVR compiles in 0.84s against 1.5s,
and the whole test suite runs in 89s against 128s. Twenty-five small programs
grow by up to 18% — the tuple ceremony against a small loop — which is the
intended trade: bytes for a halved loop.

### Impossibility flag

The fourth `PResult` field, `rImposs :: IRExpr`, answers "is this result
structurally impossible?" (wrong `Either` arm, unmatched indicator, failed
applicability guard, off-support sample). `mixP`/`mixSubP` need this fact
to pick the winning alternative — inferring it by comparing probability to
zero is wrong both ways: a deep-tail density can underflow to a true `0.0`
while still possible, and an approximate zero test can discard merely-tiny
densities. `mixWith` branches on the flag alone.

Leaves are possible; `indicatorP`/`guardP` set it on failure; `prodP` ORs;
`mixWith` consumes it (impossible only if every alternative is).
`impossibleWhen`, which folds a *fresh* condition onto an existing flag,
spells that as an `IRIf` rather than an `OpOr`: both operands of an IR
boolean op are evaluated, and the guarded-against condition is often what
makes evaluating the other side safe or terminating. Combining two
already-computed flags (`prodP`, `mixWith`) uses plain `orIR`/`andIR`. The
compiled result shape is
`(prob, (dim, imposs))`, or with `countBranches`, `(prob, (dim, (bc,
imposs)))`; consumers match it through the `VProbDim`/`VProbDimBC` pattern
synonyms and `resultImpossible`, never the raw tuple shape.

### Branch Counting

`countBranches :: Bool` controls whether the result's third field,
`branchCount`, survives into emitted code (`stripBranchCount` removes it
otherwise). It records how many leaf resolutions the *compiled* evaluation
actually traverses, anchored on one rule: **every terminal leaf counts 1,
deterministic or random** — a distribution primitive, or a
deterministically-known value compared against the sample, whichever AST
constructor spells it (`Constant`, `ThetaI`, a bound `Var`, a deterministic
`Apply`, an `InjF` with no probabilistic parameter). Only results that
resolve to no value at all — closures and lambdas — count 0. Combinators
add nothing for the act of dispatching: an `IfThenElse` is the sum of its
two arms' counts (no term for the condition), an enum-sum is the sum over
its enumerated values, and a call forwards the callee's own count
unmodified, so a recursive program's count is its traversed recursion
depth. An arm whose condition has probability exactly zero contributes 0
and — via `IRIf`, not a strict multiply — is never evaluated; that
short-circuit is what makes a recursive program's branch count terminate.
A pruned `topK` branch likewise contributes 0.

`bc` measures the compiled artifact's leaf-evaluation cost, not an
invariant of the distribution: it is stable under respelling the same leaf
(`x` vs `x+0.0`), but not under rewrites that change the number of explicit
branch points — `Uniform < 0.5` gives 1 while the extensionally identical
`if Uniform < 0.5 then True else False` gives 2, because the latter really
does compile to two leaf indicators.

### Query-Type Guard

`checkQueryType :: Bool` (default `True`, CLI opt-out `--noTypeCheck`)
wraps every prob/integ function root in a guard checking the query value
structurally conforms to the program's return type (`IRConformsTo`,
consumed by the three scalar backends; batched mode strips the root guard
instead) — without it, a wrong-typed query either silently returns a bogus
number or hits a deep panic. The marginal wildcard (`VAny`) is accepted at
every level so marginal queries aren't penalized.

### Observation masks: which `ANY` queries a function can answer

A query with `ANY` holes is not a point query with a wildcard value — it is an
observation of a **different shape**, so a different density is the answer.
`SPLL.ObservationMask` is the analysis that says what those shapes are, and the
rewrite that turns one into an ordinary program (design
`witnessed-per-query-capability`, task 2; task 3 compiles the variants and the
dispatcher, and is not landed).

The **observation tree** of a declaration strips parameter lambdas, descends
`let` bodies, follows a root `Var` to its bound value *when that variable has
exactly one occurrence*, and stops at a constructor application (`TCons`,
`Cons`, `left`/`right`, user ADT constructors), whose fields it descends in
turn. Everything else is a **leaf slot**, identified by its accessor path from
the root (`fst`, `snd.fromLeft`, a field name). A root that is not a constructor
tree — an `if`, a call, a comparison — has exactly one leaf, the root itself,
and nothing here applies to it.

A slot's **latents** are the random sources it reaches through `let` bindings.
Identity is per *occurrence*, keyed by chain name, which is what makes SPLL's
eager `let` come out right: two slots reading the same bound variable reach one
`Expr` node and so one latent, while two syntactic `Uniform`s are two draws.
A `ReadNN` contributes one latent **per `PartitionPlan` leaf it is read
through**, so `fst o` and `snd o` off one neural read are independent — and
that is why the plan-guided corpus gets no variants and keeps its per-leaf
wildcard handling. Overlap is equality for draws and *prefix* comparison for
neural paths (reading the whole output and reading one field of it are the same
source; two distinct fields are not). No `MultiValue` is consulted: an accessor
chain can only go as deep as the plan's own structure, so distinct incomparable
paths cannot name one leaf.

A slot is **self-contained** when it shares no latent with another slot *and*
every draw it depends on happens inside its own sub-expression; a deterministic
slot is self-contained trivially. For those the existing per-field `anySafe`
guard is already exact. Every other slot is **enumerated**, and masks range over
those. Slots partition into **correlation classes** (connected components under
shared latents) — the trigger `warn-correlated-slots` wants is "some class has
two or more slots", and it falls out here for free.

`pruneObservation mask decl` replaces each masked leaf's sub-expression by a
**hole**: `Constant VAny` carrying the leaf's `rType`. That marker is
unambiguous because `Validator.hs` forbids `Constant VAny` in a user program.
Everything below pruning then runs on an ordinary program: a hole is `Exact` in
the modality lattice, a premise-free clause in forward chaining, and
deliberately carries **no** `DiscreteValues` tag (its domain is *absent*, not
the singleton `{ANY}` — tagging it would make the enumerated sum range over a
wildcard). A latent that only fed masked slots loses its last occurrence and the
existing dead-binding arm drops it; a latent recovered from a masked slot is
re-witnessed from the remaining slots by ordinary forward chaining.

**The per-mask capability is therefore the projected `pType` of the masked
program** — there is no second computation to disagree with it. `Prelude`'s
`maskTable`/`marginalReport` produce it, and `compile` is split at the
post-RInfer seam (`compileRTyped`) precisely because a pruned program enters
there: it cannot re-enter at the top, since validation forbids its holes.

`--marginals` prints the report (slots and their accessor paths, correlation
classes, which slots are enumerated and why, and the mask table).
`--marginalSlots N` (default 4, `CompilerConfig.marginalSlots`) bounds the
enumerated slots per function — `k` of them means `2^k` masks — and a function
over budget is reported as over budget and compiles exactly as it does today.
The budget is a cost ceiling the user may raise, not a correctness gate, which
is why it sits beside `materializationCardinality`.

Verified against the design's programs: `W`/`O`/`N`/`C`/`B` come out one
correlation class each, `I` two singletons, and `let x = Uniform in (x, Uniform)`
two classes with slot 1 enumerated and slot 2 self-contained. The mask tables
reproduce the design's hand-verified rows — W `(ANY, _) -> Bottom` (a
convolution) with `(_, _)` and `(_, ANY)` `Integrate`; C `(_, (ANY, concrete))`
`Bottom` while `(_, (ANY, ANY))` is admitted. Tests:
`test/TestObservationMask.hs`.

### Debug: Intermediate Stage Dump (`-d`)

`showIntermediates :: Bool` (CLI `-d`/`--debugIntermediates`) prints the
fully-annotated AST after each pipeline stage to stderr via
`prettyPrintProg`, showing the progressive accumulation of annotations:

| Stage | What becomes visible |
|---|---|
| After Parsing | All fields `NotSetYet`, tags empty |
| After Callee Normalization | printed **only** when a callee was rewritten — still unannotated (see Callee Normalization below) |
| After RType Inference | `rType` populated; `pType` still `NotSetYet` |
| After Enum Annotation | `DiscreteValues` tags appear |
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

### Enumerability across a function call

`SPLL.Analysis.annotateEnumsProg` derives a node's `DiscreteValues` tag from
its shape (`Constant`, `InjF` via `propagateValues`, `IfThenElse` as the union
of its arms). An arrow-typed function cannot carry one fixed tag in the
environment -- what its result enumerates over depends on what its argument
enumerates over -- so `applyTags` computes the tag **per call site**: it
resolves the application's head to a lambda (a literal one, or a top-level
function looked up in the raw function environment), binds the argument's tags
to the parameter, and re-annotates the callee's body under that environment.
`f x ++ f y` then selects the same enumerate clause the hand-inlined body does.
The directly-applied-lambda (`let`) case likewise binds the parameter before
annotating the body, so a `let`-bound enumerable is visible inside it.

Three refusals, each answering "no tag" -- the status quo before this existed:

- **Curried spines of two or more arguments.** In `f a b`, `a` sits where
  IRCompiler's enumerate path cannot reach it: `enumerateAppliedLambda`
  marginalises the argument of the single `Apply` node it is handed, and the
  partial application `f a` is not even tagged `IsConditional` (only `Var` and
  `Lambda` nodes are). Deciding it per argument position would need `pType`,
  and **this pass runs before ModalityInfer, so every `pType` still reads
  `NotSetYet` here** -- `rType` is available, `pType` is not.
- **Recursion.** A function already being looked through is refused; unrolling
  has no termination story and the enclosing tag fixpoint would not converge.
- **An empty propagated domain.** No values at all is an *absence* of a domain,
  not an empty one; tagging it would make downstream inference sum over nothing
  and report probability zero.

Enumerating an ADT domain through a **field accessor or constructor test** is
partial -- `b1` has nothing to say about an `A`, and `implicitFunctionImpl`
answers that with an `error`, not a `Left`. `propagateValues` asks
`implicitFunctionApplicable` first and drops the tuples the function is
undefined on, so an accessor's enumerated domain is its own constructor's
values rather than a compiler crash. Before applied helpers were tagged, a
multi-constructor domain never reached an accessor at compile time.

Corpus: `applyEnum*` (the four shapes plus the no-application control) and
`clevrEqualLargeMetalSphereSplit` (one neural read per object, contributions
summed through a shared helper -- the split sibling of
`clevrEqualLargeMetalSphereNatural`, which reads the whole scene at once).

A **non-conditional** helper (`bump x = x ++ 1`, no `if`) now compiles where it
used to be rejected, but its emitted probability function is generate-backed
and therefore not a probability function at all -- a pre-existing defect
reachable at HEAD by `bump coin ++ 1`, tracked by the docs-repo investigation
`generate-backed-inference-sweep`, not by the tag.

### Neural Declarations

Neural networks are declared separately as
`NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type
environment before inference; `ReadNN name param` calls the named network
at runtime. A `MultiValue` annotation on the declaration becomes a
`DiscreteValues` tag (`Analysis.hs`), which is what lets `IRCompiler` pick
enum-aware algorithms for downstream comparisons — except that an
annotation containing a continuous leaf anywhere (`Real`, incl. `_` on a
`Float` slot) is declined entirely, since enumerating only the discrete
residue would silently drop continuous mass.

The `of ...` clause mirrors the output `RType`:

```
multival ::= _     -- MultiAuto: auto-derive from RType
           |  Real -- Float leaf
           |  [value1, value2]      -- MultiDiscretes: explicit enumeration
           |  (multival, multival)  -- MultiTuple
           |  '(' multival '|' multival ')'              -- MultiEither
           |  '{' ctor multival* ('|' ctor multival*)* '}' -- MultiADT
           |  ident                                      -- MultiTypeRef: recursive self-reference
           |  int ident '.' multival                     -- depth-limited recursion: unroll <int> levels, binding the self-reference name <ident> — e.g. `3x.{A [0,1,2] | B x}` (the `x` is the binder, not a keyword)
```

Auto-derivation (`_`, or an omitted clause) fills slots from the RType
(`Float`→`Real`, `Bool`→`[True, False]`, `Tuple`/`Either`/non-recursive
`ADT`→recurse); `Int`/`Symbol` need an explicit enumeration, and a
recursive `ADT` only auto-derives with a default depth on its `data`
declaration (`data T = … depth N`) — otherwise give a depth-bounded
override (`3x.{...}`) or compilation errors. Only *direct* self-recursion
is auto-detected.

### AutoNeural naming: `readLogits` / `writeLogits`

Two independent directions live in `SPLL.AutoNeural`, and both are named for
the data flow rather than for "encode"/"decode" — those words used to collide
(both nominally "produce logits"), which made the actual opposite pair
(reading a logit vector vs. writing one) unreadable from the names alone.

- **`readLogits`** (`makeReadLogitsFunGroup`, `neuralReadLogitsSuffix =
  "_auto"`): a neural declaration `name :: Symbol -> target` forward-declares
  a network (NN1) whose logit-vector output SPLL *reads* into a
  value/distribution. Emits the `<name>_auto` group's `gen`/`prob` readers;
  it never hosts a `writeLogits` function itself.
- **`writeLogits`** (`makeWriteLogits`, `makeTopLevelWriteLogitsFun`,
  `IRFunGroup`'s `writeLogitsFun` field, generated as a `_writeLogits`
  suffix / `writeLogits` Python method): the compiler-generated inverse —
  it derives a logit vector from a value-producing SPLL function's own
  compiled `_prob`/`_normal` functions, for a hypothetical downstream
  network (NN2). Built per function endpoint (task
  `encode-per-function-endpoints`), not per neural declaration.
- The registry keyword is `neural writeLogits :: T of M`
  (`SPLL.Lang.Types.writeLogitsDecls`), and the `.tst` probes are
  `writeLogits_len`/`writeLogits_at` (`TestCaseParser`).
- A third, historical direction (`source -> Symbol`, once called "Encoder")
  named an external network with no SPLL call site; it has been removed and
  is rejected at validation (`SPLL.Validator.validateNeuralShape`).

## Test Structure

The suite runs under tasty (`tasty-quickcheck` for properties, `tasty-hunit`
for unit tests). It is split across **two cabal test-suites**, each its own
executable/OS process: `haskell-dppl-test` (`test/Spec.hs`, everything below
except Corpus) and `haskell-dppl-test-corpus` (`test-corpus/SpecCorpus.hs`,
just the `Corpus` group, module `TestCorpus`). `stack test` builds and runs
both automatically; `--ta` patterns only reach whichever one you invoke
directly (`stack test haskell-dppl-test-corpus --ta '-p ...'`), since each
process gets its own tasty CLI. This split exists because `Corpus` compiles
the whole `test/cases/` corpus 8 times over (once per config it needs to
cross-check), and tasty holds its whole `TestTree` — including those
compiled-program closures — alive for a process's entire run; sharing a
process with the rest of the suite meant that ~1.4GB+ never got released
before End2End/Fuzz/etc. piled their own allocations on top, which is what
drove a combined `stack test` to an OOM kill (`SIGKILL`/`-9`, no assertion
failure) on a memory-constrained machine. See `TestCorpus`'s module haddock
for the measurements. `TestSupport.hs` holds the handful of compile/query
helpers (`topKConf`, `irDensity`, `reasonablyClose`, ...) both suites need,
since they can't import each other's `main-is` module.

Each module exports a `TestTree` which `Spec.hs` (or, for Corpus,
`SpecCorpus.hs`) assembles into the top-level groups (`--ta '-l'` prints the
current list for whichever binary you run):

- `test/Spec.hs` — main entry and the static `Spec` properties.
- `test-corpus/SpecCorpus.hs` / `test/TestCorpus.hs` — the `Corpus` group of
  metamorphic properties generated from `test/cases/` (validation,
  sampling-vs-PDF, topK, branch counting, P(ANY)=1, log-space vs linear, and
  `-O0` vs the default `-O2` — the optimizer is a rewrite, so the two levels
  must agree exactly on every corpus query point; a `.tst` expectation alone
  would not have caught a dangling chain-name reference that constant
  folding happened to delete). Four of its eight compiled-config variants
  differ only in `topKThreshold` (or `topKThreshold` + `logSpace`) — see the
  filed follow-up task `runtime-parametric-topk-threshold` in
  `NeST_internal_docs/tasks/` for folding those into fewer compiles.
- `test/TestParser.hs` / `TestInternals.hs` — parser and internal-function
  unit tests
- `test/TestRejection.hs` — unhappy-path: invalid or ill-typed programs must
  be rejected with the expected reason
- `test/TestModality.hs` / `TestModalityInfer.hs` — the capability lattice
  and its projection; hand-verified modalities the engine must pin
- `test/TestDeterminism.hs` — the forward determinism dataflow and its
  call-graph fixpoint
- `test/TestWriteLogitsProperties.hs` — AutoNeural writeLogits, plus corpus-driven
  writeLogits/readLogits roundtrip checks on slot layout and semantics
- `test/TestShowcase.hs` — documentation drift guard: `examples/showcase.*`
  (incl. the `.freeze` definitions) and every ` ```spll ` block in
  `README.md` as a doctest
- `test/End2EndTesting.hs` — `.ppl`/`.tst` integration against interpreter,
  Julia and Python, plus the batched groups (see Batched Mode below)
- `test/TestKnownIssues.hs` — drives `test/cases/known-issues/`: pinned
  repros of open compiler bugs, each declaring which of four failure shapes
  it demonstrates (see "Known-issues corpus" below)
- `test/TestFuzz.hs` — `Fuzz`, inside the opt-in `Slow`/`SuperSlow` groups,
  plus `Shrinker` (the typed generator's shrink contract), which is in the
  default suite
- `test/TestCaseParser.hs` / `ArbitrarySPLL.hs` / `TestTolerances.hs` — the
  `.tst` parser, QuickCheck generators, shared numeric tolerances

A `.tst` file may start with three optional header lines, in any order: a
routing header `backends: interpreter, julia, python` (any non-empty
subset; default is all three scalar backends), a standalone `slow`
line, plus two opt-in tokens: `batched` (declares batched-mode
eligibility, asserted by the `BatchedPython` group rather than filtered)
and `dense` (declares a finite query domain, presupposes `batched`); and,
for a `test/cases/known-issues/` file only, `expect-failure: <shape>`
(design testcases-corpus-restructure — see "Known-issues corpus" below).
Comments are only allowed as a leading/trailing block, not interleaved
between test cases; an unparseable line is a hard parse failure naming
the file and line. Beware CRLF files when adding a token by script —
append before the `\r`.

Expected values are compared with `probTolerance` (1e-4). A `p(...)`/
`cdf(...)` expectation has two shapes (`TestCaseParser.Expectation`):

- **`p(x) = (prob, dim)`** or **`p(x) = (prob, dim, imposs)`** — an ordinary
  point. `prob` and `dim` are *both always checked*, by all three scalar
  backends and the interpreter, unconditionally — there is no "probability
  happened to compute to zero so skip the dim check" special case. The
  optional third component is the expected impossibility flag, checked when
  present; omitting it (most pre-existing corpus lines) means "don't check
  the flag". The corpus rows that pin it target its *structural* semantics
  rather than a zero test — notably `normal p(40.0)`, a 40-sigma tail whose
  density underflows to a hard `0.0` while `imposs` must stay `False` and
  `dim` must still state the true `1.0` (it's on-support, just a tiny
  density — dim is meaningful there and is checked like any other row).

- **`p(x) is impossible`** / **`cdf(x) is impossible`** — the dedicated
  shape for a genuinely impossible query point (wrong `Either` arm,
  off-support sample, unmatched indicator, ...). At such a point the dim has
  no fact of the matter (a hard zero is neither a density nor a mass), so
  none is stated or checked; `prob` is asserted `0` and `imposs` is asserted
  `True`, both unconditionally. This is the *only* way to spell a
  zero-probability, impossible point — `TestCaseParser.pTupleExpectation`
  refuses a `(0.0, dim, True)` tuple outright (a hard parse-time error naming
  the file and line), so a `.tst` author can never write a numeric dim that
  silently goes unchecked. Task `tst-dim-unasserted-at-zero-probability`
  closed that gap: an earlier, purely-documentary pass over this same task
  (corpus sweep + a note, no grammar change) was reopened and redone
  properly once a human review pointed out it left the structural hole open;
  the whole corpus was swept mechanically at the time (25 files' worth of
  `(0.0, dim, True)` rows rewritten to `is impossible`) and every remaining
  zero-probability `(prob, dim)` row was verified against the interpreter
  under the new unconditional dim check.

A zero-probability point that is *not* impossible (the rare on-support
underflow case, `normal p(40.0)`-style) still uses the ordinary tuple shape
with an explicit `imposs = False` third component — omitting the third
component on a zero-probability tuple row is legal (means "don't check the
flag") but unusual, since such a row is exactly the case where stating and
checking `imposs` is most informative.

A query point is written in the *value* grammar (`Parser.pValue`), which
covers ADT constructor values by juxtaposition — `p(Leaf)`,
`p(Node Leaf Leaf)`, `p(Node (Node Leaf Leaf) 0.5)`; a field that is itself
an application needs parentheses. Prefer querying an ADT program at a point
over querying a `Bool`/`Float` projection of it: the projection never
reaches a sibling constructor's field accessors, which is how
`forward-missing-constructor-guard` shipped.

### Known-issues corpus (`test/cases/known-issues/`)

A sibling of `test/cases/`'s topic folders (design
testcases-corpus-restructure), holding `.ppl`/`.tst` pairs pinned to a
*specific, still-open compiler bug* rather than a working feature. It is
**excluded** from every ordinary corpus sweep (`TestCaseParser.listCorpusPplFiles`,
so End2End, the batched groups and the `Corpus` properties never see it) —
those all assume a corpus program compiles cleanly, which a known issue by
definition does not. `TestKnownIssues.hs` discovers this folder on its own and
checks each pair's `.tst` against its `expect-failure:` header instead:

```
expect-failure: crash                          -- an uncaught exception, message unpinned
expect-failure: diagnostic "some substring"    -- an uncaught exception whose message contains this
expect-failure: no-code                        -- compiles, but generate/probability/integrate is silently absent
expect-failure: wrong-result                   -- compiles and runs; the p()/cdf() rows below pin the known-wrong value
expect-failure: broken                         -- mechanism unpinned; the p()/cdf() rows below state the idealized value instead
```

`crash`/`diagnostic` are checked against an exception thrown while *forcing*
`compile`'s result — a graceful `Left` (an intended, working refusal) does not
satisfy either; that is what `TestRejection.hs` is for. `wrong-result` needs
no new assertion machinery: the ordinary `p(...)`/`cdf(...)` rows below the
header already pin the value the bug produces, and the corpus's usual tuple
comparison already fails loudly the day a fix changes the computed number.

`broken` is the loose fallback for a repro that was migrated without
characterizing exactly how it currently fails (no exact crash message or
wrong value pinned down by hand). The rows below the header instead state the
*idealized* value -- what the fixed compiler should produce -- and
`TestKnownIssues.hs` runs each row through the interpreter and asserts the
compiled program does **not yet** match it, within the ordinary
`probTolerance`; a runtime crash, a refused compile, a missing variant, or a
merely different number are all "still broken" and pass, while an exact match
fails loudly ("may be fixed now"). This trades away the free "which exact
mechanism regressed" signal `diagnostic`/`wrong-result` give for robustness
against unrelated code churn shifting a pinned message or number -- appropriate
when nobody has run the repro yet to observe its actual failure mode.

This coexists with `TestRejection.hs` rather than replacing it: a genuinely
bespoke, multi-assertion regression (e.g. one that additionally checks a
*different*, unaffected variant) stays a hand-written HUnit group there — this
mechanism is for the common single-diagnostic shape only, and migrating the
existing `TestRejection.hs` groups onto it is out of scope. Seeded with
`correlatedGaussianLetSharesLatent` (task
correlated-gaussian-let-shares-latent), the `diagnostic` shape, whose fuller
multi-assertion sibling is `TestRejection.SetWitnessSharedLatent`.

### Slow tests

**The `Slow` group is currently known-broken** — it is not green, and
failures there are pre-existing rather than caused by whatever change you
are making. Do not treat a red `NEST_SLOW_TESTS=1` run as a regression
without first confirming the same failure on an untouched checkout. The
default (non-slow) suite is the gate.

It does, however, **complete**. Each `Fuzz` property carries a whole-property
wall-clock deadline (120s, `NEST_FUZZ_SCALE`-scalable) on top of its per-case
one, so a property that would otherwise multiply a high discard rate by a
5s-per-draw hang now drains its remaining draws as discards and reports "Gave
up" instead of having to be abandoned. A one-line note on stderr names any
property that hit it. See `docs/fuzz-testing.md`, "Two budgets".

Tests expensive enough to noticeably slow `stack test` but unlikely to
catch regressions elsewhere are skipped by default, run via
`NEST_SLOW_TESTS=1 stack test`: a `.tst` file's `slow` header, a
`TestInternals.hs` case placed in `slowInternalsTests`, and the whole
`Fuzz` group.

### Benchmarks

`benchmarks/` holds compiler-performance stress programs
(`stressPlanEnum.ppl`, `stressContinuous.ppl`). They pin no values and
aren't part of the test suite — run and time them via the CLI:

```bash
stack run -- -i benchmarks/stressContinuous.ppl compile -l python -o /tmp/b.py   # time this
```

Always warm up once before timing: the first invocation after a source
change includes stack's rebuild-and-register, which dwarfs the compile
itself. For the test suite, `TASTY_HIDE_SUCCESSES=false` gives per-test
timings and `--ta '-t 60'` bounds each test.

`benchmarks/batched_vs_scalar.py` instead times the *emitted code*: a
scalar per-point loop against one batched call for the same `ReadNN`
program (needs a torch-enabled Python, same lookup as `BatchedPython`).

### Fuzz tests

`test/TestFuzz.hs` (group `Fuzz`, lives inside `Slow`) runs randomly
generated SPLL programs (`test/ArbitrarySPLL.hs` — scalars, tuples,
`Either`, lists and `let`-bindings, the last of which is what reaches the
set-valued-witness engine) against the same
metamorphic invariants the hand-written corpus checks — P(ANY)=1, topK
never inflates probability, branch counting doesn't change the
probability value, probability is never negative, mixtures follow the
dimension-combination rules — rather than known expected values, plus
crash-freedom on both generators. Typed draws **shrink** (type-preserving,
`shrinkTypedProgram` in `ArbitrarySPLL.hs`; the properties use `forAllShrink`),
and `prop_Fuzz_GeneratorCoverage` `tabulate`s what the generator actually
produced each run so a silent collapse to one shape can't pass green. The
shrinker's own contract is the `Shrinker` group, which is pure and fast and so
lives in the **default** suite rather than in `Slow`. Details, the raw-vs-typed
split, and the `SuperSlow` sampling-vs-PDF tier: `docs/fuzz-testing.md`.

### Batched Mode (PyTorch tensorizer)

`batched :: Bool` (CLI `--batched`) opts into batched inference: instead
of scalar Python evaluated one query point at a time, emit branch-free
elementwise PyTorch that runs a whole `[B]`-shaped batch at once
(`torch.where` instead of a data-dependent `if`, via `SPLL.IRSelectPass`
and `CodeGenPyTorchBatched`). Tested by the `BatchedPython` group, gated
on the `.tst` `batched`/`dense` header tokens and a torch-enabled Python
(`NEST_TORCH_PYTHON` → a venv path → `python3`; repo convention:
`~/.cache/nest/torchvenv`) — skips with a visible note if none is found.
Mechanism, the dense-enumeration mode, and refusal rules:
`docs/batched-mode-pytorch-tensorizer.md`.

A *scalar* `compile` run at `-v` closes with a batched-eligibility advisory
(`SPLL.Prelude.batchedRefusal`, reported by `app/Main.hs`), so you can see
whether `--batched` would take a program without flipping the flag and
reading a refusal. It re-runs the pipeline in batched mode, which is why it
is behind `-v` rather than on by default, and it names the **first**
offending construct only — fixing that one may reveal more behind it. Its
verdict is pinned against the backend's own refusals by the
`BatchedRefusal` test group.

### Emitting float literals

Haskell's `show` renders the non-finite doubles as `Infinity`, `-Infinity` and
`NaN`. **None of those is a Python name, and `-Infinity` is not Julia syntax**,
so a backend that `show`s a `VFloat` straight into its output emits code that
dies with a `NameError` at run time instead of failing the compile. Log space
reaches this constantly — its zero is `-1/0` (`Semiring.negInfIR`), so every
impossible arm of a `--logSpace` program carried one.

All four value renderers therefore go through a per-language helper —
`pyDouble` (`float('inf')`/`float('-inf')`/`float('nan')`, needing no import),
shared by `CodeGenPyTorch`'s `pyVal` and `CodeGenPyTorchBatched`'s `batchedVal`
and `domainVal`, and `juliaDouble` (`Inf`/`-Inf`/`NaN`) for `juliaVal`. Adding a
new site that emits a `Double` means routing it through one of those.

This survived 1507 tests because the corpus's log-space properties compare
against the **interpreter**, which never renders a literal.
`Spec.prop_LogSpace{Python,Julia}RendersInfinity` are the only tests putting a
log-space compile through a text backend, and each asserts both halves — no
bare `Infinity`, *and* the mapped literal present — so neither can go vacuous.

### Unary math must not raise where the interpreter answers

The interpreter is the reference semantics, so a backend's unary math has to be
IEEE-conforming the way Haskell's is: `exp` **saturates** to `inf` past the
representable range, `log 0` is `-inf`, and `log` of a negative is `NaN`.
CPython's `math` module *raises* on all three (`OverflowError` /
`ValueError`), and Julia's `log` throws `DomainError` on a negative.

That is reachable, not hypothetical. An `InjF` inverse's monotonicity-direction
guard evaluates the inverse derivative **eagerly** just to read its sign, so
`cdf(1000.0)` on `main = log Uniform` emitted `math.exp(1000.0) > 0.0` and took
the whole query down with an `OverflowError` before any branch was chosen — a
crash rather than a wrong number, and one nothing in the corpus caught, because
`exp`'s forward `applicability` is unconditionally `True` and so no guard
stands between a large query and the eager call.

`OpExp`/`OpLog` therefore route through `safe_exp`/`safe_log` in `pythonLib.py`
and `safe_log` in `juliaLib.jl` rather than the raw stdlib name
(`CodeGenPyTorch.pyUnaryOps`, `CodeGenJulia.juliaUnaryOps`). Julia needs no
`safe_exp` — its `exp` already saturates. The batched backend was already right
by construction (`torch.exp` saturates, and `safe_log` in `pythonLibBatched.py`
exists for a different reason: gradient safety under `torch.where`, which
evaluates both arms).

`log` is *currently* safe on every reachable path anyway, because each of its
call sites happens to sit behind an inverse's `applicability` guard — but that
is a property of today's set of `InjF` inverses, not an enforced invariant, so
it is wrapped too. Pinned by `test/cases/distributions/uniformLog.tst`'s `cdf(1000.0)` row and
`test/cases/arithmetic/multExp.tst`'s `cdf(-5.0)`.

### Type errors carry the source they came from

A unification failure is reported the way GHC reports one -- a position, the two
types in the vocabulary the *user* writes, and a context chain naming what they
wrote:

```
prog.spll:1:12:
    Couldn't match type '[s]' with '(u, v)'
      In the function 'tail'
      In the pattern: h : t
```

`RInfer`'s `Constraint` carries a `Maybe Provenance` (the originating
expression's `srcPos` plus a description from `describeExpr`). It used to carry
a `Maybe String` holding only the *phase* that emitted the constraint
(`"Apply"`, `"inferResultingType"`), and `solver` discarded even that before
throwing, so `addRTypeInfo` could only print
`UnificationFail (TADT "Scene") (ListOf (TADT "Object"))` followed by 88 lines
of program and constraint dump. That dump still exists and is still useful for
work on `RInfer`; it is behind `-v`.

**There is deliberately no table keyed on pairs of types.** A rule that
recognised, say, an ADT meeting a list and emitted bespoke prose about cons
patterns would improve one program shape and have to be re-derived at the next
site; naming the source improves every unification failure at once. New
diagnostics here should follow that: make the mechanism carry more, do not add
a case. `TestRejection.TypeErrorDiagnostic` includes a case on an unrelated
ill-typed program precisely so this cannot silently degenerate.

Three things keep positions available, and each is load-bearing:

- `TypeInfo.srcPos :: Maybe SourceSpan`, defaulted by `makeTypeInfo`, so adding
  it changed no construction site. It is `Nothing` on everything the parser did
  not build (the prelude, `SPLL.Examples`, anything a later pass synthesizes),
  and every diagnostic degrades gracefully rather than requiring it.
- `Parser.withSpan` wraps `term` and `expr` -- **and the atoms inside
  `application`**, which calls `atom` directly and so would otherwise leave
  every argument position-less. Cross-function type errors had no position at
  all until that was fixed.
- Nodes that are *built* rather than parsed inherit a span through
  `fillMissingSpans`, which only fills where `srcPos` is `Nothing`:
  `stampSynthesized` gives `letInDestructor`'s generated `head`/`tail`
  scaffolding the span of the pattern it came from (plus
  `spanDesugaredFrom`, the `In the pattern: h : t` line), and `keepSpanOf`
  gives `normalizeExpr`'s rebuilt `ReadNN`/`InjF`/projector nodes the span of
  the application they replaced. Without these a message could point at, or
  print, the generated `p_d0` binder -- pinned against by
  `TestRejection.TypeErrorDiagnostic`.

`Eq` on `TypeInfo`/`Expr`/`Program` stays **derived and structural**: two values
from different source positions really are different. The position-blind
comparison is a separate `Equiv`/`(~=)` class in `SPLL.Lang.Types`, identical to
the derived `Eq` on spanless values, used by the parser tests that compare a
parse against a constructed value or two parses of different source strings.
`TestParser`'s `prop_EquivAgreesWithEqWithoutSpans`/`prop_EquivIgnoresSpans` pin
both halves, so the switch neither weakened those tests nor made them vacuous.

**Known limitation**: a failure has two sides and is reported against one --
whichever constraint the solver reached when the contradiction materialised,
which is ordering-dependent. Naming both needs provenance on *types* rather than
constraints; docs-repo task `type-error-blames-one-side-only`. The broader
triage of every other user-facing error site is the docs-repo investigation
`user-facing-error-site-inventory`.

## Runtime Libraries

Generated Python code depends on `pythonLib.py` (scalar) or
`pythonLibBatched.py` (batched mode, see above); generated Julia code
depends on `juliaLib.jl`. These provide runtime helpers for the transpiled
inference functions.
