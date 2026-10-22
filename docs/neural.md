# Neural declarations and AutoNeural

Neural declarations, their `of` annotations, and the generated read/write-logits functions.

## Neural Declarations

Neural networks are declared separately as
`NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type
environment before inference; `ReadNN name param` calls the named network
at runtime.

**A network's input is `Symbol`, `Float`, `Tensor[s] t`, or a tuple of those**
(task `tensor-type-shaped-neural-inputs`, slice S1 of the docs-repo design
`tensors-in-core-language`). `Lang.isNeuralInputType` is the gate,
`neuralInputType`/`neuralValueType` read a declaration's two sides, and
`Validator.validateNeuralShape` refuses any other input and the reverse
`(source -> Symbol)` shape. Which tensor *outputs* are admitted is the next
section's. `Symbol` stays a first-class opaque handle beside `Tensor`
permanently.

- **The type.** `TTensor Shape RType` over `RType.hs`'s `Shape`/`Extent` (the
  IR tensor's). The element is a scalar (`isTensorElemType`: Float, Int, Bool,
  Symbol). Surface syntax `Tensor[e1, ..., en] t` (`Parser.pTensorType`; a type
  keyword only when `[` follows, so `Tensor` stays usable as an ADT name).
  Rank 0, a non-positive extent, a non-scalar element, and the nested spelling
  `Tensor[2] (Tensor[3] Float)` are registered parse errors (nesting is
  rejected, not normalized). `Tensor[1] Float` is not `Float`. Unification
  (`RInfer.unifies`) is monomorphic: equal shapes unify their elements,
  anything else is a `UnificationFail` naming both tensor types. No shape
  variables, no broadcasting. `matches _ _ = False` degrades silently on a new
  constructor, so a new `RType` constructor means grepping for every match.
- **Input layout.** `AutoNeural.inputSlots` is the flat packing order:
  element-major, tuple fields left to right, tensor elements row-major.
  `makeForwardDecl` prints it (`inputLayoutString`) above the output layout in
  every read-logits group's doc comment. It is the *mocks'* packing order, not
  a contract on a real network: the emitted code passes the input
  structurally (in Python today as the runtime's tuple `T`), so a denoiser
  receives `(x_t, t)` apart.
- **The `ReadNN` modality rule reads its input.** A read keeps its Gaussian /
  enumerable verdict only when its input is a point (`ModalityInfer.inputIsPoint`:
  `Exact`, or `IWit` witnessed, field by field through a product); otherwise it
  is `SampleOnly` (`Bottom`): generate compiles, probability is a missing
  variant. `neural mu :: (Float -> Float); main = mu Normal` used to be typed
  `PNormal` and answered a silently wrong density. This also moved
  `readMNist(if Uniform < 0.5 then s else t)` from the central generate-backed
  guard's refusal to a missing variant; that guard's message is now pinned
  white-box (`Rejection.CentralGenerateBackedGuard`). A finite random input
  (an enumerable `Bool` choosing the input) is `Bottom` too: marginalising over
  it was declined (option (c) of design `diffusion-models-wishlist`).
- **A tensor's modality** is `IRec topGround elem` (`ModalityInfer.topI`): the
  compact form of a homogeneous n-ary product with a static spine.
- **Mocks.** `MockNN.evaluateMockNNFor` dispatches on the input type: a
  `Symbol` input keeps the envelope protocol (`(0, seed)` random,
  `(1, (spike, seed))` spiking, `(2, [logits])` verbatim); any shaped input is real
  data, and the mock is a fixed projection of it (`shapedMockLogits`: the input
  flattened in layout order, truncated or padded with `1.0` to the plan's
  logit count -- so a `Float -> Float` mock is `N(x, 1)`, and a
  `(Float, Float) -> Float` one reads `(mu, sigma)` off its input). The
  End2End harness shapes a `.tst` envelope given to a shaped network's
  parameter into a real input carrying those logits (`shapeNeuralParams`,
  applied once in `loadCorpusPair`, via `MockNN.mockInputFor`), and installs the
  same projection as each text backend's mock (`NetMock`: `pyMockDef`,
  `juliaMockDefs`, `batchedMockExpr`), so `neural/tensorInput*` runs the
  `autoNeuralProb*` rows unchanged through a real 784-element tensor. Text
  backends render only rank-1 tensor values (`pyVal`/`juliaVal`); a rank-2
  input program is interpreter-only in the corpus
  (`neural/tensorInputRank2Discrete`).

**A network's output may be a Float tensor: a diagonal Gaussian head** (task
`tensor-gaussian-heads-rd-diffusion`, slice S2 of `tensors-in-core-language`).

- **What is admitted.** `Validator.validateNeuralTarget`: a rank-1
  `Tensor[n] Float`, as the whole output or a tuple field of it. A tensor over
  any other element is refused (only Float tensors are probabilistic outputs,
  decision C), as are rank above 1 (the text backends render rank 1 only) and
  a tensor under an `Either`, a list or an ADT field.
- **The plan** is `TensorPlan sh Continuous`, `getSize = numel * 2`. Its logit
  layout is element-major, elements row-major: `[mu_1, sigma_1, mu_2, sigma_2,
  ...]` (D6). That is the layout of the nested-tuple spelling, so a network
  trained against the tuple program reads the tensor program unchanged
  (`neural/tensorHeadLayout` and its tuple twin pin the same numbers). The
  layout is a wire format: changing it is a retraining event
  (`planLayoutString`'s documentation). The layout table prints one row for
  the whole tensor.
- **The reader and the sampler** are one `BMap` over `BIota sh`, the tensor of
  element positions: element k reads its slots at `ix + 2k`, so the emitted
  code is O(1) in the tensor's size (Python module 26170 bytes at d = 4 and
  26209 at d = 64, the difference being the digits in the comments;
  `Internals."tensor Gaussian heads"`). The density sums per-element
  log-densities and, under the linear semiring, exponentiates (`BReduce` has
  no product operator). A tensor has no CDF (`IRCompiler.compareValueExpr`'s
  `TTensor` case is a runtime error) and no writeLogits (`requiredNormalFns`
  names a normal function no compile generates).
- **The plan-aware mock.** A shaped network whose output holds a tensor is
  mocked by `MockNN.planAwareMockSlots`: the k-th Gaussian leaf reads its mu
  off input slot k (0.0 past the input's end), with sigma `1/sqrt(2 pi)`, so
  an element's density at its mean is 1 and a trajectory's density stays of
  order 1 in any dimension; discrete regions are uniform. Every other shaped
  network keeps the projection mock. The harness mocks carry the same recipe
  (`NetMock.netMockRecipe`). A query names a tensor value as `[| v1, ..., vn |]`
  (`Parser.pTensorVal`; values only, the expression literal is slice S3's).
- **The diffusion trajectory** `step t x = if t < 0.5 then [x] else x : step
  (t - 1.0) (mu (x, t))` with `main = step T (prior 0.0)` is tractable: every
  state is in the output, so every network input is witnessed
  (`neural/tensorDiffusionTrajectory`, d = 4, T = 3, interpreter, Python,
  Julia and batched). The initial state is a network read at a constant, an
  iid Gaussian tensor without new syntax. This needed `ModalityInfer` to pass
  the observation into the arms of an observed `if` under a deterministic
  condition: the recursive call sits in the else arm, and seeded at the
  declaration root the witness question for its parameter was answered no
  (`neural/neuralTrajectoryScalar`). The marginal of the final state is
  `Bottom` (`Rejection.TensorTypes`).

**No `of` is `of _`, and every read is tagged** (task
`of-annotation-and-auto-derived-enumeration-divergence`). `Prelude.compile`
first resolves each declaration's annotation once (`resolveNeuralDecls` over
`Lang.resolveNeuralAnnotation`): the declaration's own clause, else the
registry's entry for its type, else `_`, with every `_` auto-derived in place
and every written part kept as written. A `_` auto-derivation refuses (an
`Int`/`Symbol` slot, a recursive type with no depth, mutual recursion) is a
`CompilerError` naming the declaration and the slot (`at slot snd.fromLeft`).
The plan engine's layout and Analysis's `DiscreteValues` tag on the `ReadNN`
both come from that one value, so no `of`, `of _` and the equivalent written
clause compile to the same bytes (`Internals`' `neural annotation spellings
compile identically`). Before, only a *written* clause tagged the read, so the
two spellings took different engines.

A tag may carry a **continuous leaf**: it is then the node's value *shape*,
not an enumeration. Every consumer that loops over a tag refuses one
(`Analysis.enumerableDomain`, which `IRCompiler.isEnumerable`,
`Modality.finFromTags` and DrawSinking read, and the budget gate's
`enumeratedCount`), and listing finds no values in it. Accessors read
through it, so `fst p` off an `(Int, Float) of ([0,1,2], Real)` read is an
ordinary enumerable `[0,1,2]` (`plan-enumeration/ofRealBesideDiscreteSlot*`).
It used to drop the whole tag. The read itself has no dense path while its
domain is mixed; it is the plan engine that answers it, continuous leaf and all
(a leaf the body never reads integrates out, one it compares is a Gaussian
tail), including when the read is passed straight to a helper (below).

**Structural propagation.** Analysis computes the tags of `fst`/`snd`,
`fromLeft[Partial]`/`fromRight[Partial]`, `isLeft`/`isRight`, ADT field
accessors, constructor tests and constructors (`TCons`, `left`/`right`, ADT
constructors) on the operand's `MultiValue` itself (`Analysis.structuralTag`),
never listing the cross product it stands for. Listing (`listedTag`) is the
reference: wherever both answer they agree exactly, in canonical form
(`Internals`' `structural enum propagation agrees with listing`, over every
corpus node; above 2^16 tuples the listing evaluates an ADT implicit function
directly rather than through the interpreter, pinned equal to `listedTag` at
every node within that bound). A non-canonical operand (a tuple constant is a flat
`MultiDiscretes [VTuple ..]`) falls back to listing. Listing had made a 3^12
tuple read with an `of` uncompilable: `fst s` needed 2·3^11 cross-product
elements to see all three colours.

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

## A read-logits network's categorical sampler is one call

A discrete leaf of a read-logits network's own `generate`
(`AutoNeural.lottery`) is `IRBuiltin (BCategoricalIndex start n) [u, vec]`:
the inverse-CDF slot index of one uniform `u` over the leaf's `n` unnormalised
logit slots, mapped back to its value arithmetically (a contiguous `Int`
range), by a comparison (`Bool`), or through a constant `BTensor` table
(anything else). It is **pure** -- the randomness is the `IRSample IRUniform`
argument -- so no purity or CSE rule needed a case for it. Each runtime has a
`categorical_index` (`pythonLib.py`, `pythonLibBatched.py` as one cumsum,
`juliaLib.jl`); the interpreter is the reference, pinned at the CDF boundaries
by `Internals/categorical index`.

It replaced a chain of nested `IRIf`s, one per value, each re-summing the
remaining weights: O(V^2) text, and one indentation level per value, so CPython
refused to import any module with a 99+-value `neural` domain (`forward`
included). `End2End`'s `wide neural domain` group compiles a 150-value
declaration and runs it. Two things are still V-deep: `main`'s own
`writeLogits`, a nested `ConsInferenceList` chain that trips CPython's
200-parenthesis limit at V = 200 (docs-repo task
`writelogits-cons-chain-nests-v-deep`); and `constructorLottery`, the same
if-chain over an ADT's constructors, which only bites an ADT with ~100
constructors and is left as it is.

## The CDF of a read sums its point masses

The network's `_auto_prob` is a point mass, so `toIRInference`'s cumulative
`ReadNN` clause answers `cdf(x)` as `sum over v in dom of P(read = v) *
[v <= x]` (`enumSumNode` over the read's `DiscreteValues` domain, the
comparison by `compareValueExpr`, all in the compile's semiring). A read whose
domain has a continuous leaf, or exceeds the materialization budget, has its
`integrate` refused (`known-issues/neuralMixedReadCdfRefused`). A bare `Bool`
read takes the generic Boolean CDF split and a Gaussian-headed one the
`gaussianLeaf` clause, before this one. Pinned by
`test/cases/neural/neuralIntReadCdf` and `neuralTupleReadCdf`.

## One network call per argument per query

The compiler emits a network call `n(sym)` at every read, binding it as
`nn_raw` next to the reader. A program that reads several fields of one read
(`define truth = see img in Face (.. x0 truth ..) (.. x1 truth ..)`, or the
per-field draws `DrawSinking.splitProductDraw` makes of `draw truth = see img`)
therefore gets one call per field. Each sits inside that field's enumeration
loop and under the guards of the field equations, so a J-field read called the
network up to 2J times per query. Neither the compiler's loop hoist
(`hoistInvariantBindings`, which cannot see through a guarded block's binding)
nor CSE (which shares only what is evaluated unconditionally) merged them.

At `-O2` the optimizer's `shareNetworkCallsCounted` does. It runs right before
CSE, knows the declared networks from `OptEnv.optNeurals`
(`optimizeEnvWith`), and for each distinct pure application `n(arg)` binds one
`cse_nn_<k>` at the lowest node covering every occurrence. It also lifts a
single occurrence out of an enumeration loop that `arg` does not read. It never
moves a call past a binder of `arg`'s free variables, or past an `if`/select
whose condition reads them, since such a condition (`isAny(img)`) may be what
keeps the call off an argument the network cannot take. The cost: a call that
used to be reached only in some arms (an all-ANY query skips every field's
loop) now runs once even when no arm needs it. `generate` is unaffected, because
`n_auto_gen` samples and is not pure. Pinned by `Internals.repeatedNeuralReadShared`
(one application of `see` in `main`'s probability body, for the `define`
spelling, `drawProductReadPerField20` and the Guess-Who shape
`drawProductReadUnderBinding`) and `Internals.networkShareScoping` (the scoping
rules). Task `repeated-neural-read-not-shared`.

## AutoNeural naming: `readLogits` / `writeLogits`

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
- The text backends run the `.tst` `writeLogits_len`/`writeLogits_at` rows too
  (End2End's `Python WriteLogits` group and `Julia WriteLogits` batch). Until
  task `writelogits-text-backends-broken` only the interpreter did, and every
  emitted writeLogits but a flat discrete one crashed: the IR standard library's
  `listConcat` existed only in the interpreter (it is now mirrored in
  `pythonLib.py`/`juliaLib.jl` like `indexOf`/`listProd`), a nullary normal
  function was referenced but never called (the backends' `callableNames` now
  include nullary normal functions), and a tuple component's normal function was
  defined under its group's name rather than the one the IR calls it by
  (`ReservedNames.componentNormalName` is the one spelling of that rule).
- **Dead arms** (task `writelogits-dead-arm-nan`): an Either/ADT arm whose
  probability is *exactly* zero has no conditional, so its slots are filled with
  iid N(0, 1) noise pushed through each slot's link (softmax for a discrete/ADT
  flag group, sigmoid for an Either flag, `exp` for sigma) -- on-manifold, per the
  design's "Per-slot validity". writeLogits is therefore stochastic in dead slots
  only: `runWriteLogitsC` draws that noise from a fixed seed (stays a pure
  function), `runWriteLogitsRandC` from the caller's generator. Compare vectors
  zero-weight-aware (`TestWriteLogitsProperties.liveSlotMask`): slots under a
  zero-probability arm are not compared. The noise is the only randomness the
  central generate-backed guard admits in a writeLogits body -- it sees the body
  through `AutoNeural.stripDeadSlotFills`, which recognises the `l_wlarm_*`
  guards and nothing else. A near-zero arm (1e-300) is live and written.
- **Correlated slots are encoded independently, with a warning** (task
  `warn-correlated-slots`). Each plan leaf is written from its own marginal, so
  `main = draw w = Uniform < 0.5 in (w, w)` writes `[0.5, 0.5, 0.5, 0.5]`: the
  product of marginals, not the joint. The vector is unchanged, but the compile
  warns (`CompileWarnings.CorrelatedWriteLogitsSlots`), naming the plan-leaf
  slots and the variables the shared draws are bound to. The trigger is the
  observation-mask latent walk (`ObservationMask.slotLatentNames`,
  `correlationClasses`) on the function's observation tree, with slots coarsened
  to writeLogits plan leaves (`CompileWarnings.planLeafSlot`). It only fires for
  a function that actually has a writeLogits and whose body is a constructor
  tree: `main = f 0.4` with a correlated `f` warns for `f` only. Pinned by
  `test/cases/neural/correlatedSlotsWriteLogits`, which
  `WriteLogitsRoundtrip.DensityAgreement` skips for that reason.
- **A discrete leaf is fitted to the function's own output support** (task
  `writelogits-int-output-truncated-to-registry-domain`). The registry is keyed
  by type, but `add a b = readD a ++ readD b` over digits `0..6` ranges over
  `0..12`. `AutoNeural.fitPlanToSupport` compares each `Discretes` leaf of the
  registered plan with the function's `DiscreteValues` tag at that position: a
  support inside the registered domain keeps the registered layout (what the
  network's own reader expects, zeros included); one reaching outside it lays
  the leaf out over the support itself. So `add`'s writeLogits has 13 slots,
  and no wider `neural writeLogits :: Int of ...` declaration is needed (one
  would conflict with `readD`'s `of` clause in the validator). Where the
  support is not statically known (a recursive count), the registered layout
  is kept and the compile warns
  (`CompileWarnings.WriteLogitsSupportUnverified`): mass outside it is
  dropped. A `Bool` leaf never warns, its domain being whole. The test
  harness's `End2EndTesting.endpointPlan` resolves the same fitted plan.
  Pinned by `WriteLogits.outputSupport` and
  `test/cases/neural/writeLogits_sum_wider_than_registry`.
- A third, historical direction (`source -> Symbol`, once called "Encoder")
  named an external network with no SPLL call site; it has been removed and
  is rejected at validation (`SPLL.Validator.validateNeuralShape`).
