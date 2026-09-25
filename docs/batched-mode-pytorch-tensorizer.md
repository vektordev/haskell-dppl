# Batched Mode (PyTorch tensorizer)

`batched :: Bool` (CLI `--batched`) opts into batched inference: instead of
scalar Python evaluated one query point at a time, emit branch-free
elementwise PyTorch that runs a whole `[B]`-shaped batch at once
(`torch.where` instead of a data-dependent `if`). `SPLL.IRSelectPass`
retags eligible `IRIf` nodes as `IRSelect` (both arms evaluated, combined
by a mask) before the optimizer runs — a no-op for scalar backends, which
lower it back to `IRIf`. `CodeGenPyTorchBatched.generateFunctionsBatched`
then emits tensor code over the *tensor fragment*: fixed-shape tuples of
float/int/bool, neural/enumerable constructs, and list-valued/
constructor-tagged samples via *shape-signature bucketing*
(`pythonLibBatched.bucketed` partitions a batch by structural signature and
calls the kernel once per bucket). `OpLog`/`OpDiv` route through
`safe_log`/`safe_div` so autograd doesn't NaN through the untaken arm of a
select; a refused `IRError` arm emits as a NaN `poison()` constant the
select masks away.

An ADT whose constructors are all nullary (`data Color = Red | Green |
Blue`) is an *enumeration*: its tag is a value, not a structure, so the
signature keys the whole ADT as one bucket and `_pack` stacks the tags into
an `EnumBatch` (a `[B]` tag tensor); `is<Ctor>` (`is_ctor`) and `==` then
answer per-element masks through `torch.where`. The emitted constructor
classes carry `_enum`/`_enum_tag` only when collapsed: the compiler emits
every enumeration collapsed first, and the fallback is per ADT. A refusal
caused by a collapsed enumeration's test (e.g. one choosing between two list
shapes, which has no `torch.where` form, or leaving a recursive call without
a structural guard) carries the ADTs whose tests the offending condition
reads, directly or through a `let` (`Refusal`'s `refusalBlame`, from
`enumBlame`); those are keyed back into the signature and the program
re-emitted, so the other enumerations stay collapsed. A refusal no collapsed
enumeration is blamed for re-emits with none collapsed, so its outcome is
exactly the uncollapsed backend's -- collapse never costs a program its
batched eligibility, in at most k+1 attempts for k enumerations. So
CLEVR-shaped scenes (enumerated attributes, Gaussian positions) bucket by
object count alone — `End2EndTesting.batchedEnumBucketingTests`,
`test/cases/data-structures/clevrSceneEnumAttrs`.

Combining two neural ADT reads (`match (readAttrs s1) ++ match (readAttrs
s2)`) makes the compiler enumerate each read's domain as ADT *constants*
(`Nil()`, `Obj(Red())`, ...), the `BTensor` an enumerated sum maps over.
`batchedVal` renders those as instantiations of the classes the backend
emits itself; each is one compile-time value, not a batch. Inside that map
body (a comprehension element, which `hoistStructural` cannot lift out of)
a structural `if` — `isNil o` guarding `color o` — is emitted as Python's
lazy `t if c else f` rather than a `torch.where`, so the sibling
constructor's field accessor is never evaluated. Task
`batched-backend-refuses-neural-adt-constants`; corpus
`test/cases/neural/neuralAdtReadCount`, `neuralEnumReadCount`. Cost caveat:
branch-free evaluation cannot skip the residuals a nested `++` count chain's
`is_member` guard rules out, so an n-slot chain does `n!`-ish work per call
where the scalar backend prunes per row (6 slots: ~49s per call, whatever
`B`) -- correct, but not yet practical past ~4 slots. Tier-0 materialization
would make it a convolution but declines the table, the leaf cell
(`match (readAttrs s)`, a 97-value sum) exceeding `maxTabulatedLeafNodes`;
docs-repo task `batched-count-chain-enumeration-factorial`.

A prob/integ path may call only forward/integrate methods: a batched
`generate` is a different artifact (trailing batch size, per-element draws).
But the IR compiler evaluates a *deterministic* helper forward through its
`_gen` method whenever the helper's value is fixed by what the path already
knows — `d c = (m c) ++ (0 - (m c))` measures `d` against `m_gen(c)`, and
every CLEVR comparison/`exist` program has that shape. `inlineDetGenCalls`
therefore beta-reduces each complete call to a generator that
`IROptimizer.deterministicGens` proves draws nothing and `hasGenCycle` proves
non-recursive into the caller before the call-graph guard runs, renaming every
binder of the inlined body; a call to a random or recursive generator (e.g.
`factorial`) is still refused. Task `batched-prob-path-calls-helper-generate`;
corpus `test/cases/neural/neuralHelperArgUsedTwice`, `neuralHelperDrawSelect`.
It made 15 more corpus programs batched-eligible (`flip`, `adt`,
`sharedLatent*`, `clevrEqualLargeMetalSphere*`, ...). The corpus differential
also now routes ADT-valued query samples through the bucketing wrapper, which
it previously refused as unbatchable.

A call-graph guard refuses value-dependent recursion (e.g. `dice`); other
non-fragment constructs (marginal `VAny`, composite enumeration,
mismatched-shape select arms) are refused with a diagnostic naming the
construct rather than compiling to something silently wrong. Runtime lib:
`pythonLibBatched.py`.

When a group's query domain is statically finite, **dense enumeration
mode** evaluates the kernel once over the whole domain, giving a `[V]`
probability vector any query gathers into — strictly additive (ordinary
methods stay byte-identical; an unrenderable domain just yields no dense
methods). `topK` pruning is per-element (both `torch.where` arms are
always evaluated, so pruning only picks which value survives), which
covers the dense `[V]` axis for free too.

Tested by the `BatchedPython` group, gated on the `.tst` `batched`/`dense`
header tokens and a torch-enabled Python (`NEST_TORCH_PYTHON` → a venv
path → `python3`; repo convention: `~/.cache/nest/torchvenv`) — skips with
a visible note if none is found. Refusal behaviour has separate
torch-independent coverage.

`benchmarks/batched_vs_scalar.py` times the emitted code: a scalar
per-point loop against one batched call for the same `ReadNN` program
(needs a torch-enabled Python, same lookup as `BatchedPython`).
