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

`IRSelectPass` retags by syntax, so it also retags a conditional whose guard
is a shape probe the fragment admits: `sample == []`, a constructor-test
predicate, or a CSE name bound to one (`let cse_0 = sample == [] in let
cse_1 = select (not cse_0) True False in ... select cse_1 (... head sample
...) 0.0`, the witness guard of a draw-bound list element). The backend
first demotes every select whose condition is `structural` back to an `IRIf`
(`demoteStructuralSelects`), so it is emitted as a Python `if` and the arm it
rules out never runs; emitted eagerly, that arm read the head of the empty
tail (task `batched-draw-bound-list-element-reads-empty-tail`, corpus
`data-structures/drawBoundListElementGuardsEmptyTail`). The impact census
labels a program that demotes (`usesSelectDemotion`, `docs/testing.md`).

`torch.where` selects tensors, not Python tuples, so a tuple-valued select
is split into one select per component (`distributeSelects`). The split
copies the condition, and an arm's `let`-spine, into every component. That
is harmless while they are pure, but a copied random draw is a second,
independent draw: `draw (a, b) = if Uniform < 0.5 then (True, True) else
(False, False)` drew its coin once per component in `generate` and agreed
only half the time (task `batched-generate-destructured-draw-double-sample`).
An impure condition or arm (`batchPure`: an `IRSample`, or a generator
reference under its raw or post-rename name) is therefore bound once above
the split, its binders renamed fresh; pure parts are copied as before, so
prob/integ bodies emit unchanged. Corpus
`let-bindings/drawDestructuredAgreement*`.

The split only sees an arm that is syntactically a tuple (`tupleValued`).
An arm that merely evaluates to one -- a CSE name, a hoisted structural
block `_hsN`, a call, a tuple constant -- reaches the runtime's
`where_anchored` as a whole `T`, which selects two `T` arms leaf by leaf
(task `batched-guarded-select-over-tuple-result`). Corpus
`conditionals/guardSelectOverTupleResult`, and the topK pruning selects of
`data-structures/adt{KeywordNames,FieldNamesAB,NullaryOneTwoField,MixedArityCtors}`.

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

A non-empty list constant (`[1.0, 2.0]`, or the `[ANY]` a per-mask variant
puts where a list built from draws is masked) is spelled as the runtime's
cons structure over its constant leaves: its length is a compile-time fact,
so every bucket agrees on it, and the leaves broadcast against a sample's
`[B]` leaves. `InferenceList.__eq__` treats an `AnyInferenceList` tail as
matching the rest of the other list, as `pythonLib` and the interpreter do
(head's inverse compares `Cons(x, ANY)` against the constant). A per-element
choice between two list constants stays refused (`listValued`). At `-O0` the
enum-index lookup `indexOf(x, [..])` survives unfolded and resolves to
`pythonLibBatched.indexOf`. Docs-repo tasks
`batched-refuses-list-constants-with-data` and
`batched-refuses-any-list-constant-in-mask-variant`.

A list `map` (`BMapList`) is `pythonLibBatched.mapList(f, xs)`: within a
bucket the spine is uniform Python structure, so it is a Python walk applying
`f` to each `[B]` leaf, and the result is rebuilt with `toList`. Inner lambdas
are admitted as Python closures (`(lambda a, b: ...)`, binders shadowing the
structural-binder set); the probability and integrate variants bind their
inverse as a `let`-bound lambda and map that name. Docs-repo tasks
`batched-refuses-list-map` and `batched-refuses-inner-lambda`.

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
`test/cases/neural/neuralAdtReadCount`, `neuralEnumReadCount`. Branch-free
evaluation cannot skip the residuals a nested `++` count chain's `is_member`
guard rules out, so an untabulated n-slot chain does `n!`-ish work per call
where the scalar backend prunes per row. Tier-0 materialization turns it into
a convolution: the leaf cell (`match (readAttrs s)`, a 97-value sum) is
judged with its domain-tensor literal counted as one node, so 10 slots at
`B = 256` take ~0.8s per call, linear in slots (docs-repo task
`batched-count-chain-enumeration-factorial`).

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

**Per-structure split.** Shape-signature bucketing fixes every structure
the *input* carries. A value-dependent select between two structures picks
one per element instead: isLeft's inverse `if sample then Left ANY else
Right ANY` (corpus `either_isleft`, `isLeftOfRightDiscardsComparedDraw`),
or a helper choosing `Right w` or `Left ()` by `w == 1`. `torch.where` has
nothing to choose between two shapes, so the dichotomy guard refused these.
The second bucketing strategy splits the batch at the select:
`splitStructureSelects` (prob/integ bodies only, in `prepBatchedBody`)
rewrites the select to `let _spN = split_uniform(c) in if _spN then t else
f`, which `structural` treats as a shape-directed `if`, and the method body
becomes a local `_split_kernel` run under `split_retry`. At run time
`split_uniform` answers a Python bool when the condition agrees across the
call. A mixed condition raises, and `split_retry` re-runs the kernel on the
two halves of the batch (`_slice_batch` indexes every `[B]` leaf of every
argument, and `_scatter` merges the results as `bucketed` does). Re-running
the body's prefix is exact because a forward/integrate kernel is a pure
function of its arguments. A generate body is never split (`prepGenBody`):
re-running would redraw the condition. Every split leaves two smaller,
non-empty halves, so the retry terminates. Three shapes are left to the
guard: a condition that draws, a condition reading a collapsed enumeration's
test (the enum fallback above makes it structural instead), and a select
inside a tensor map's body, a comprehension element with no statement
position for the binding. A select there whose condition reads only the
map's element is not per-element at all: the element is a domain constant
(`bindMap` puts it in `sBound`), so it is a Python conditional (corpus
`either-maybe/enumeratedEitherSelectOnDomainConstant`). The impact census
labels a program that splits (`CertifiedCensus.structureSplitLabel`), so its
rows always run on the batched backend. Docs-repo task
`batched-value-dependent-structure-select`.

A per-mask variant that still carries a `VAnyExcept` placeholder is retired
to a runtime refusal of that one mask (`retireUnrenderableVariants`,
rendered by `retiredMethod` as a `throw` of the shared message), as on the
scalar text backends, instead of refusing the whole program (corpus
`tupleCtorTestOfSharedDraw`).

A call-graph guard refuses value-dependent recursion (e.g. `dice`); other
non-fragment constructs (marginal `VAny`, composite enumeration, a
structure select the split does not reach) are refused with a diagnostic
naming the construct rather than compiling to something silently wrong.
Runtime lib: `pythonLibBatched.py`.

When a group's query domain is statically finite, **dense enumeration
mode** evaluates the kernel once over the whole domain, giving a `[V]`
probability vector any query gathers into — strictly additive (ordinary
methods stay byte-identical; an unrenderable domain, or one of more than
`denseDomainCap` = 65536 values, just yields no dense methods). The size is
counted from the symbolic `MultiValue` before anything is listed: a
product-ADT domain is the cross product of its slots, and listing a ten-slot
scene's 25^10 values is what made the batched compile run out of memory. `topK` pruning is per-element (both `torch.where` arms are
always evaluated, so pruning only picks which value survives), which
covers the dense `[V]` axis for free too.

Tested by the `BatchedPython` group, gated on the `.tst` `batched`/`dense`
header tokens and a torch-enabled Python (`NEST_TORCH_PYTHON` → a venv
path → `python3`; repo convention: `~/.local/share/nest/torchvenv`, not under `~/.cache`, which cleaners may wipe) — **fails** if none is found,
naming why (`End2EndTesting.noTorch`), unless `NEST_SKIP_TORCH=1` opts out
explicitly. Refusal behaviour has separate
torch-independent coverage.

`benchmarks/batched_vs_scalar.py` times the emitted code: a scalar
per-point loop against one batched call for the same `ReadNN` program
(needs a torch-enabled Python, same lookup as `BatchedPython`).

## Eligibility advisory at `-v`

A *scalar* `compile` run at `-v` closes with a batched-eligibility advisory
(`SPLL.Prelude.batchedRefusal`, reported by `app/Main.hs`), so you can see
whether `--batched` would take a program without flipping the flag and
reading a refusal. It re-runs the pipeline in batched mode, which is why it
is behind `-v` rather than on by default, and it names the **first**
offending construct only — fixing that one may reveal more behind it. Its
verdict is pinned against the backend's own refusals by the
`BatchedRefusal` test group.
