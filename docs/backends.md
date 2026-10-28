# Code generation backends and runtime libraries

Backend-specific hazards in the emitted Python/Julia and the hand-written runtimes they call.

## Runtime Libraries

Generated Python code depends on `pythonLib.py` (scalar) or
`pythonLibBatched.py` (batched mode, see `batched-mode-pytorch-tensorizer.md`); generated Julia code
depends on `juliaLib.jl`. These provide runtime helpers for the transpiled
inference functions.

## The Python runtimes under torch: gradients and dtype

Both Python runtimes are hand-written code the emitted modules call into, and a
model trained through them passes torch tensors where the value tests pass
floats. Two silent failure classes lived there, each found by an experiment
rather than by this suite (task `python-codegen-silent-precision-traps`):

- **`pythonLib` severed autograd.** `math.erf`/`exp`/`log` convert a tensor
  through `__float__` and return a float with only a `UserWarning`, so
  `cumulative_normal`, `log_cumulative_normal`, `log_cumulative_uniform`,
  `safe_exp`, `safe_log` and `logsumexp` (the log-space enumerated sum) trained
  through a dead gradient. Each now dispatches on `torch.is_tensor` (via
  `_torch_for`, which reads `sys.modules` so the library stays torch-free for
  float callers). Experiments' `torch_math_patch.py` monkey-patches are inert
  now and no longer needed.
- **`pythonLibBatched` built python numbers in torch's global default dtype**
  (float32): a folded constant selected by `torch.where` between two python
  floats lost half its digits while the emitted source showed all of them.
  Every such site now uses the runtime-local `DTYPE = torch.float64`, and the
  emitted select is `where_anchored(c, t, f)` rather than a bare `torch.where`.
  This is deliberately **not** `torch.set_default_dtype`: importing a compiled
  module must not change the dtype of the caller's own networks, and a tensor
  the caller passes keeps its dtype.

`test/TestPythonPrelude.hs` (probes in `test/prelude_numerics_probe.py`) pins
value, gradient and dtype for both runtimes, and **fails on any new public
`pythonLib` function** that is not classified in the probe's tables — adding
one means deciding whether a tensor can reach it. All but that classification
check need a torch-enabled python and fail without one, like `BatchedPython`
(`NEST_SKIP_TORCH=1` skips them).

## Gradients with respect to the sample, export, and Julia AD

Three more gaps blocked gradient or export use of an emitted module without
changing any answer (task `emitted-runtime-differentiability-gaps`):

- **The scalar query-type guard** (`CodeGenPyTorch.pyConforms`) tests a TFloat
  with `pythonLib.isFloat`, which admits a 0-d floating tensor as well as a
  python float, so `p(x)` with `x` a `requires_grad` tensor gives a score
  function without `--noTypeCheck`. A batch-shaped or integer tensor is still
  refused. The Julia guard tests `isa Real && !(isa Integer)` rather than
  `isa AbstractFloat`, which a ForwardDiff `Dual` is not.
- **`pythonLibBatched.check_result`** raises a `ValueError` on a NaN eagerly.
  That test is a data-dependent branch, which `torch.export` refuses, so while
  tracing (`torch.compiler.is_compiling()`) it records the same check as
  `torch._assert_async(no NaN, message)` instead: the exported module raises a
  `RuntimeError` with the same message. The eager path stays a `ValueError`,
  because `_assert_async` on an accelerator is a device-side assert.
- **`juliaLib`'s `cumulative_IRNormal`** keeps the libm `erfc` call for the
  types that convert to `Float64` losslessly (IEEE floats, integers,
  rationals) and sends any other `Real` (an AD number, a `BigFloat`) through
  `_erfc_generic`, CPython's former series / continued-fraction `erfc` in plain
  arithmetic (within 6e-14 of libm). `isclose` takes any `Real`.

`PythonPrelude` pins all three; the Julia one runs `test/julia_ad_probe.jl`,
which carries a minimal dual number since no Julia AD package is a dependency.

## The normal CDF is `erfc(-x / sqrt 2) / 2`

Every runtime, the interpreter (`irCDF`/`irLogCDF`) and the optimizer's
constant folder compute `Phi(x)` as `erfc(-x / sqrt 2) / 2`, not
`(1 + erf(x / sqrt 2)) / 2`. The latter cancels in the lower tail
(`Phi(-8)` came out 6.1e-16 for 6.22e-16), which is where the compiler puts
every upper tail too, as `Phi(-z)` (`Semiring.upperTailComplement`). Python
uses `math.erfc`/`torch.special.erfc`. Julia calls `erfc` from the libm it
already links (`ccall((:erfc, Base.Math.libm), ...)`), because Base has no
`erfc` and SpecialFunctions is not a dependency. It used to carry a 5-term
Abramowitz-Stegun `erf` with ~1.5e-7 absolute error. A batched query passed
as a float32 tensor is still computed in float32 (~1e-7 relative), since a
caller's tensor keeps its dtype (see above).

## Emitting float literals

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

## Python lines deeper than 200 brackets are spilled

CPython's tokenizer refuses to open a 201st bracket level in one line
(`MAXLEVEL`, "too many nested parentheses") -- a constant, not a limit a caller
can raise -- and the scalar Python backend parenthesises every `IROp`, so a
right-nested world sum over ~190 plan worlds (`isbn_checksum` at depth 6, the
`planOverBudget*` programs at up to 3296 levels) compiled to a module that
could not be imported. `CodeGenPyTorch.liftedLine` renders each line as
before, measures it (`pythonNestingDepth`, string-literal aware), and only
past `pythonMaxNesting` regenerates it with its deep subterms let-bound into
`_sN` temporaries first (`spillDeep`, cutting at an estimated depth of 64).
Every module that parsed before is byte-identical (checked across the whole
corpus when this landed).

A subterm moves only if it sits in a **strict** position (operator operands,
an `if`-expression's condition, constructor/accessor/builtin/call arguments --
never an arm, the right operand of `and`/`or`, or anything under a binder) and
is **pure arithmetic** (`spillable`: no draw, no generator reference, no
lambda, and no call except two kinds that draw nothing: a function group's
inference method, `f.forward`/`f.integrate`, which is what `writeLogits`'s
V-deep `ConsInferenceList(main.forward(..)[0], ...)` chain is made of (docs-repo
task `writelogits-cons-chain-nests-v-deep`), and the functions an ADT
declaration emits -- constructors, `is<Ctor>` tests and field accessors
(`adtCallees`)). A whole conditional expression may move, intact with its
guard. The measurement, the
walk and its admission rules live in `SPLL.PythonNesting`, shared with the
batched emitter (below); the Julia emitter has no such pass and was not
checked. Pinned by `End2End`'s
`deep expression spill` group (hand-built IR: a 300-term sum, with a
divide-by-zero arm as the laziness canary).

The batched emitter's one known V-deep line no longer arises: a select chain `x == k0 ? v0 : x == k1 ? v1 : .. : d` with scalar
constant keys and arms and a pure scrutinee -- what `indexOfChain` makes of a
read-logits network's value-to-slot lookup for a non-contiguous domain -- is
emitted as one `table_select(x, keys, vals, d)` (`tableSelect`, from two keys
up), a broadcast compare plus first-match argmax that answers in the arms'
kind as `where_anchored` did. Pinned by `End2End`'s `wide neural domain`
group, batched at 250 values. Docs-repo task
`batched-table-domain-lookup-nests-v-deep`.

A line whose depth is *inside* a comprehension body -- an enumerated `draw`'s
`sum([body for b in xs])`, where nested ifs over the latent render as a
walrus/tuple let chain ~10 brackets per `if` -- has nothing strict outside the
body to cut. There, a `BMap` over a lambda whose body and list are both pure
(`spillable` admits one, though not a bare lambda) is spilled whole as a loop
(`generateSpillStatement`):
`_sN = []`, `for _vM in xs:`, the body as statements into `_eM`,
`_sN.append(_eM)`. Same list, same order, so `sum(_sN)` adds the same floats.
The loop variable is renamed to a fresh `_vM` because a `for` target, unlike a
comprehension's, lands in the function scope. Docs-repo task
`python-emitted-expression-exceeds-parser-nesting`.

Purity is checked recursively, so a comprehension whose body holds another
pure comprehension moves too, and the inner one is spilled from its own line
in the loop body. That is the shape of nested enumerated `draw`s (an
enumerated latent, readings gated on it, answers over pairs of readings):
before, the inner comprehension counted as a lambda, the outer one was not
pure, and the line stayed at 200+ brackets. Pinned by the `deep expression
spill` group (a hand-built nested pair, and the 11-answer chain through the
pipeline). Docs-repo task `chained-answers-exceed-python-paren-depth`.

An answer record's guarded slots read their observations through the record's
field accessors (`a0(sample)`), so before the ADT functions were admitted, the
enumeration comprehension of a large shared answer group (91 AND-pair slots
over 14 coins: 212 brackets) could not move at all. Pinned by the `deep
expression spill` group, scalar and `BatchedPython`. Docs-repo task
`answer-record-group-exceeds-python-paren-depth`.

The batched emitter spills the same way (`CodeGenPyTorchBatched.batchedLine`,
the counterpart of `liftedLine`, running `SPLL.PythonNesting.spillDeep`): its
enumerated `draw` sums `tensor_sum([body for b in xs])`, ~20 nested ifs over
the latent pass 200 brackets, and the comprehension becomes a loop
(`batchedSpillStatement`) appending one `[B]` tensor per domain element, so
`tensor_sum` stacks the same `[E, B]` tensor. Two batched-specific points.
Each spill binding is threaded into the structural environment (`bindS`), and
the loop variable is bound as the comprehension's was (`bindMap`), so a
structural read of the latent is still a Python `if`, not a `torch.where`.
That needs the domain to stay a literal at the `for`: `spillDeep` never cuts a
`BTensor` of constants (one bracket level, nothing to gain). And `IRSelect`
(a `torch.where` call, all three operands evaluated) counts as strict in all
its operands; the scalar emitter never sees one. Pinned by the `deep
expression spill` group's `BatchedPython` case (the 24-if chain). Docs-repo
task `batched-enum-comprehension-exceeds-parser-nesting`.

## Python methods indented past 99 levels hoist their deep blocks

Statement emission trades bracket depth for **indentation** depth, one level
per conditional nested in an arm (and one per spilled loop), and CPython caps
that too: a line indented 100 levels is an `IndentationError` (`MAXINDENT`).
That ceiling was backend-wide: ~97 nested ifs in a method body did not load,
with or without an enumerated `draw` around them.

The fix has the same shape as the bracket spill. `generateMethodBody` renders
a class method as before and measures its deepest line (`blockIndent`); only
past `pythonMaxIndent` (99, counting the class and `def` levels) is the method
regenerated with hoisting on, so every module that loaded before is
byte-identical. While hoisting, `hoistDeepBlock` turns any `if` arm or spilled
loop body nested deeper than `hoistIndentThreshold` (32) into a local function
`_hN` defined at the top of the method body, and the block into one call
(`name = _hN(a, b)`, or `return _hN(a, b)`), so it runs exactly where and when
the block ran. A 100-deep chain costs about three functions.

The functions are **flat** -- all at the method's top level -- because a `def`
body is an indentation level of its own: nesting them would give back one
level per hoist. Being flat, a hoisted block cannot see variables bound in the
block it was cut from, so it is **closure-converted**: each free IR variable
(`irFreeVars`) is a parameter, passed at the call. Dotted method references
and `stCallables` stay globals. Pinned by `End2End`'s `deep indentation hoist`
group (hand-built 150-deep chains in return, let and loop-body position, a
60-deep chain that must not hoist, and the 100-if program through the
pipeline). Docs-repo task `python-nested-conditionals-exceed-indentation-limit`.

## A walrus never sits in a comprehension's iterable

Both Python backends lower an expression-position `IRLetIn` to an assignment
expression, `((v := e), body)[1]`, and `BMap`, `BZip` and a list or tensor
`IRConformsTo` check to comprehensions. CPython refuses `:=` anywhere inside
a comprehension's iterable, even under a lambda or a nested comprehension
there, and the optimizer's CSE does put lets there (a cumulative's
materialized cell list, `[T(((l := ...), ...)[1]), ...]`), so such a module
did not load. `PythonNesting.bindIterable` binds an iterable whose rendered
text contains `:=` to a temporary first, `((_itN := it), [b for v in
_itN])[1]`. That is the same evaluation (a comprehension evaluates its first
iterable once, eagerly, in the enclosing scope), and an iterable without a
walrus is emitted as before, so every module that loaded before is
byte-identical. Pinned by the corpus program
`arithmetic/intProductLetInComprehensionIterable` and the IR fuzz group's "a
let in a comprehension's operand" cases (scalar, Julia, batched). Docs-repo
task `backends-agree-python-walrus-in-comprehension-iterable`.

## Unary math must not raise where the interpreter answers

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

## `--memoRecursion`: a per-query table for recursive calls

A recursive probability function called with equal arguments from several
branches recomputes the subtree each time: an HMM whose hidden state the query
does not fix costs 2^n calls. Under `--memoRecursion` (`CompilerConfig`
`memoRecursion`, off by default) both Python backends decorate every
probability and integrate method on a recursive call cycle with `nest_memo`,
and every other one that reaches such a cycle with `nest_memo_scope`
(`CodeGenPyTorch.memoPlan`). The table lives for one top-level query: the
first decorated call opens it and drops it on return, so it never serves a
value computed under other weights. The HMM then costs 2n+1 calls.

Arguments are keyed by value (scalars by type and value, tuples, `Left`/`Right`
and constructors by their parts, linked lists through a per-cell key with a
stored hash, so `sample[1:]` costs one lookup). Anything else (a tensor, a
closure) is keyed by identity, and the table holds a reference to it, since
Python reuses a freed object's id. A varying tensor therefore never hits, while
a pass-through one shares. A hit returns the same object, which for a torch
result is the same autograd node.

The flag is dropped under `--topKCutoff`, where a pruned probability depends on
the path to a call, and by the Julia backend. The CLI warns in both cases.
Without the flag, and for a program without recursion, the emitted code is
byte-identical. Tests: `test/TestMemoRecursion.hs` (call counts and exactness
through the binary) and the `End2End.Python MemoRecursion` corpus sweep.
