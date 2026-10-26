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

After the optimizer, `SPLL.IRGatherPass` rewrites a one-hot point read --
a `+`-tree of `if k == s then raw[k + c] else 0.0` over a contiguous key
range, e.g. a per-mask variant's `P(a = sample[0])` over a neural Int
domain -- into one range-guarded `nn_gather(raw, s + c)`. Every arm of the
sum was an eager `torch.where`, so the read cost O(V) tensor ops and O(V)
source; at V = 1000 the variant went from ~17-26 ms to ~0.06-0.09 ms per
call and the module from 107 KB to 37 KB (task
`batched-mask-variant-neural-read-nests-v-deep`, corpus
`neural/batchedMaskVariantNeuralReadChain`). Only a whole matching tree in
the linear spelling is rewritten; all other IR passes through unchanged.

`SPLL.IRLeafTablePass` runs after it. A program that draws several neural
reads and branches on them enumerates them as nested loops, and each draw's
decode `AcFst (f_auto_prob(raw)(x))` sits inside the loops of the draws
before it, so it used to run once per enumerated world: 10^4 + 10^3 + 10^2 +
10 decodes for four `[0..9]` reads, each a method call, a membership test, a
gather and a select over the batch, and all eager. The pass binds
`map (\v -> decode v) dom` once around the outermost loop the decode does
not depend on and reads it by position (`v - lo`) inside. It matches only a
decode at the variable of a strictly nested loop over a contiguous integer
literal domain, reading a raw output bound outside the outer loop; a decode
is pure and total on its domain, so evaluating it at every value is exact.
The runtime's side of the same task gives the per-world ops a batch-
independent fast path: `nn_gather`, `is_member` and `tensor_index` with a
Python-int argument, `where_anchored` with a Python-bool condition (the
picked arm, when that is provably what `torch.where` would give), and
`logical_not` (the emitted form of `not`) on a Python bool. On the task's
constraint programs at B = 512 (forward + backward) `--batched` went from
8-29x slower than the scalar module run feature-major to 0.8-3x (the
residual on the ~10 ms programs is the eager select evaluating both arms of
the query's `sample` test, which the scalar code's Python `if` does not).
Corpus `neural/neuralLeafTableAscending`.

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
shapes, which has no `torch.where` form, or leaving a recursive call under
an unsplit select) carries the ADTs whose tests the offending condition
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
binder of the inlined body. Task `batched-prob-path-calls-helper-generate`;
corpus `test/cases/neural/neuralHelperArgUsedTwice`, `neuralHelperDrawSelect`.
It made 15 more corpus programs batched-eligible (`flip`, `adt`,
`sharedLatent*`, `clevrEqualLargeMetalSphere*`, ...). The corpus differential
also now routes ADT-valued query samples through the bucketing wrapper, which
it previously refused as unbatchable.

**Pure callees.** Two more kinds of method are deterministic functions of
their arguments, so a prob/integ path may call them; the backend emits them
as ordinary batched methods next to `forward`/`integrate`, but only when a
prob/integ path reaches them (`pureCallees`), so a body nothing reads cannot
cost a program its eligibility:

- a helper's Gaussian parameters, `f_normal` (`normal_params`): the caller's
  density of `shifted 1.0 2.0 * 3.0` reads `shifted`'s `(mu, sigma)` (corpus
  `distributions/normalThroughFunction{Nested,Param}`,
  `logNormalThroughFunction`; docs-repo task
  `batched-prob-path-calls-helper-normal-params`);
- the *forward evaluator* of a recursive deterministic generator, which
  `inlineDetGenCalls` cannot inline: `f_gen` is renamed `f_eval` in every
  prob/integ/normal body and emitted as `evaluate` (not `eval`, which is
  `Module.eval`) from the generate body, without a batch size. `factorial`,
  and the plan-enumeration folds over a neural read's ADT fields
  (`numRed (rest s)`, `existsRed`, `checksumSum`, ...), batch this way (corpus
  `conditionals/factorial`, `recursiveHelperOnlyWhereGuarded`, `plan-enumeration/planEnumRecThreaded`;
  docs-repo task `batched-prob-path-calls-recursive-helper-gen`).

An evaluator is pure, so it gets the prob/integ treatment in full, including
the per-structure split below: a recursion on a per-element value
(`factorial x` with `x` per element) splits until each half agrees, one on a
batch-uniform value never mixes, and one through an ADT field is a structural
`if`. The per-element case has no corpus row (the differential passes
parameters batch-shared, and modality inference refuses the helper on a drawn
value), so `End2EndTesting.batchedPerElementEvaluatorTests` runs `factorial`
on a `[B]` argument. A call to a recursive evaluator is split above at *every*
call site, not only inside its own cycle: an eager `torch.where` arm would run
it on elements the scalar backend never passes it, and `cnt n = if n == 0 then
0 else cnt (n - 1) + 1` does not return on `-1` (corpus
`recursiveHelperOnlyWhereGuarded`). A nullary pure callee is referenced by a bare name and emitted as a call
(`sNullaryCalls`). A call to a *random* recursive generator is still refused.
The impact census labels a program that calls a pure callee
(`CertifiedCensus.pureCalleeLabel`), since the fuzz arms compare prob/integ
bodies only.

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

**Recursion.** Within a bucket a structural `if` is Python control flow, so a
recursion it guards runs only for the elements that take its arm. Under an
eager `torch.where` arm a recursive call runs for every element, and unless
it descends into a list tail (the bucket's uniform length then bounds it) it
never stops. So the split also covers every value-dependent branch above a
call into the method's own recursive component (`sRecCallees`, read off
`methodSCCs` by `enterMethod`) that does not descend into a list tail:
`splitStructureSelects` splits it as above. A batch-uniform guard (`dice`'s
`x == 1.0`, `x` a shared parameter) never mixes, and a per-element one
(`conditionals/recursionDepthFromSample`, `k < 0.25` with `k` the sample)
splits until each half agrees, so every element recurses exactly as deep as
on the scalar backend. `recOffenders` judges only calls inside the caller's
own strongly connected component (an entry call `main = rec` is not
recursion) and refuses what is left: a call under a value-dependent branch
the split does not reach (a select inside a tensor map's body), with no
tail descent. A generate body cannot be re-run, since its condition is a
draw. `splitGenRecursion` evaluates the condition once and emits the two
arms as closures `\_batchN v.. -> arm` over their free locals;
`gen_branch` runs each closure on its half of the batch, with the free
values sliced and `_batchN` set to the half's size, and never runs an empty
half. A recursive generate that builds a list keeps its
`heterogeneousGenStub`. An inner lambda's body renders as an expression, so
`hoistStructural` does not hoist out of it. Docs-repo task
`batched-value-dependent-recursion`.

**Partial-arm split.** A value-dependent `if` whose arm can raise outside
its domain (`head`/`tail`, `fromLeft`/`fromRight`, a field of a
multi-constructor ADT, or a call to a method holding one, `partialArm`)
is not a `torch.where` either: the arm would run on the elements that do
not take it. `nth k xs = if k == 0 then head xs else nth (k - 1) (tail xs)`
recursed past the end of the list that way and its `head` raised.
`splitPartialBranches` (after the structure split, prob/integ only) emits
`split_branch(c, \_batchN v.. -> t, \_batchN v.. -> f, v..)`, the
`gen_branch` mechanism without a batch size: a uniform condition runs one
arm, a mixed one runs each arm on its half and scatters. Nothing is re-run,
so the arms cost what the eager select did. `splitGenRecursion` takes the
same trigger in a generate body. A runtime-key index (`nn_gather`,
`tensor_index`) clamps and is not partial. Corpus
`data-structures/listIndexByRecursion`, `listIndexFromSample`; docs-repo
task `batched-conditional-evaluates-a-partial-arm`.

A per-mask variant that still carries a `VAnyExcept` placeholder is retired
to a runtime refusal of that one mask (`retireUnrenderableVariants`,
rendered by `retiredMethod` as a `throw` of the shared message), as on the
scalar text backends, instead of refusing the whole program (corpus
`tupleCtorTestOfSharedDraw`).

A call-graph guard refuses a recursion the split does not reach; other
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

Tested by the `BatchedPython` group over every corpus program (batched
admission is universal; `dense` is the one `.tst` header token) and a
torch-enabled Python (`NEST_TORCH_PYTHON` → a venv
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
