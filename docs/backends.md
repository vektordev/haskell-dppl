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
is **pure arithmetic** (`spillable`: no draw, no generator reference, no call,
no lambda). A whole conditional expression may move, intact with its guard.
The no-call rule is the approved scope, and it is why `writeLogits`'s V-deep
`ConsInferenceList(main.forward(..)[0], ...)` chain is still refused at V = 200
(docs-repo task `writelogits-cons-chain-nests-v-deep`). The Julia and batched
Python emitters have no such pass and were not checked. Pinned by `End2End`'s
`deep expression spill` group (hand-built IR: a 300-term sum, with a
divide-by-zero arm as the laziness canary).

The batched emitter has no spill, but its one known V-deep line no longer
arises: a select chain `x == k0 ? v0 : x == k1 ? v1 : .. : d` with scalar
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
(`loopable`) is spilled whole as a loop (`generateSpillStatement`):
`_sN = []`, `for _vM in xs:`, the body as statements into `_eM`,
`_sN.append(_eM)`. Same list, same order, so `sum(_sN)` adds the same floats.
The loop variable is renamed to a fresh `_vM` because a `for` target, unlike a
comprehension's, lands in the function scope. Docs-repo task
`python-emitted-expression-exceeds-parser-nesting`.

The statement form trades bracket depth for **indentation** depth, one level
per nested conditional, and CPython also caps that at 100 (`IndentationError:
too many levels of indentation`). That ceiling is backend-wide rather than
spill-specific: ~95 nested ifs load and 100 do not, with or without an
enumerated `draw` around them.

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
