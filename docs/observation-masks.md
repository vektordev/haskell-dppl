# Observation masks

Which `ANY` queries a function can answer (`SPLL.ObservationMask`).

A query with `ANY` holes is not a point query with a wildcard value — it is an
observation of a **different shape**, so a different density is the answer.
`SPLL.ObservationMask` is the analysis that says what those shapes are, and the
rewrite that turns one into an ordinary program (design
`witnessed-per-query-capability`, task 2), and the per-mask inference variants
compiled from those programs with a runtime dispatcher (task 3, below).

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

**Variants and the dispatcher** (task `per-mask-variants-by-pruning`,
`SPLL.MaskVariants`, driven from `Prelude.withMaskVariants`). For a function
with `1..marginalSlots` enumerated slots, every mask other than all-concrete
whose masked program the lattice admits gets a group `f__m<bits>` (bits over
the enumerated slots in tree order, `1` = masked), holding only `probFun` and
`integFun`, compiled from the pruned program by the ordinary pipeline (cut
down to `f` and its callees). `f`'s own probability and integrate functions
become a **dispatcher**: under the parameter lambdas and the query-type guard,
per-slot flags test each enumerated slot's `isAny` outer node first (with a
tag test before every `fromLeft`/`head`/field accessor, so no accessor meets
`ANY` or the wrong constructor), and when the root is not `ANY` and some flag
is set, a decision tree calls the mask's variant with the dispatcher's own
arguments, or raises an `IRError` naming the function, the mask and the masks
it does answer ("cannot compute marginal of 'main' at query mask (ANY, _):
..."). Otherwise the query reaches the unchanged all-concrete body, which keeps
its own root unit factor. A hole compiles to the unit factor in
`toIRInference` (mass one, dim 0, no branch) without reading the sample.

Things worth knowing:

- **Variant bodies are lazy.** Which masks have a variant is the masked
  program's *modality verdict* (`typedStages` only); the IR compile of the
  variant is a thunk forced only when something reads it (codegen, the
  optimizer pass over that group, a query reaching it). A masked program can
  cost far more than its unmasked one -- a latent the full observation
  recovers is enumerated once its slot is masked -- and
  `TestInternals`' materialization differential compiles a 6-term and-chain at
  budget 0 whose `(ANY, _)` variant takes ~110 s; eagerly, every query of that
  program paid it. An admitted mask whose compile an engine then refuses is a
  variant whose body is that refusal.
- **The flags are inline, not let-bound**, on purpose: an inline `isAny`/tag
  test is what `IRSelectPass` and the batched backend's `structural` recognise
  as bucket-uniform, so under `--batched` the dispatch stays a real Python
  branch. Let-bound, the dispatch became a select, which evaluated every
  variant eagerly and indexed a `poison()` placeholder.
- **Skipped** under `--pruneAnyChecks` (the dispatcher collapses anyway), when
  probability and integrate are both suppressed, for a root that is a single
  leaf, and when a user function already holds a variant's name. Over budget, the function compiles
  as before, `groupDoc` says why, and the CLI prints one warning naming the
  function and `--marginalSlots` (`Prelude.marginalBudgetWarnings`).
- **The let-fold `ANY` guard is now the fallback**: over-budget functions,
  non-constructor roots, list tails. `TestInternals`' "witnessed-inference ANY
  refusal" group pins it at `marginalSlots = 0` and the dispatcher at default.
- **Text backends retire a variant they cannot render.** A masked program can
  leave a `VAnyExcept` witness its full observation never did
  (`tupleCtorTestOfSharedDraw` at `(_, ANY)`). In an ordinary group that still
  refuses the compile (`anyExceptCodegenRefusal`); in a variant
  (`IRFunGroup.maskVariantOf`) `retireUnrenderableVariants` replaces just that
  body with a runtime refusal pointing at the interpreter, which answers it.
- Corpus sweeps in `TestObservationMask` ("per-mask variants and the
  dispatcher"), over the 38 corpus programs with variants: the all-concrete
  arm is byte-identical to a `marginalSlots = 0` compile before the optimizer
  (`Prelude.compileUnoptimized`); every mask of a forward sample answers or
  refuses (totality); and a finite slot summed over its domain equals its
  `ANY` query at every mask of the others (marginalisation consistency).
  Engine crashes a masked query exposes are excepted by message in
  `knownMaskCrashes`, each naming its docs task.
