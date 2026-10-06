# Test suite reference

Structure of the test suite, the `.tst` format, the known-issues corpus, rewrite invariance and the test tiers. Procedures (what to run when) are in CLAUDE.md.

## Test Structure

The suite runs under tasty (`tasty-quickcheck` for properties, `tasty-hunit`
for unit tests). It is split across **two cabal test-suites**, each its own
executable/OS process: `haskell-dppl-test` (`test/Spec.hs`, everything below
except Corpus) and `haskell-dppl-test-corpus` (`test-corpus/SpecCorpus.hs`,
just the `Corpus` group, module `TestCorpus`). `stack test` builds and runs
both automatically; `--ta` patterns only reach whichever one you invoke
directly (`stack test haskell-dppl:test:haskell-dppl-test-corpus --ta '-p ...'`), since each
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
  Julia and Python, plus the batched groups (see `batched-mode-pytorch-tensorizer.md`)
- `test/Rewrites.hs` / `test/TestRewrites.hs` — the rewrite-invariance net
  (groups `RewriteInvariance` and `RewriteInvarianceCorpus`; see "Rewrite
  invariance" below)
- `test/TestKnownIssues.hs` — drives `test/cases/known-issues/`: pinned
  repros of open compiler bugs, each declaring which failure shape
  it demonstrates (see "Known-issues corpus" below)
- `test/TestFuzz.hs` — `Fuzz`, inside the opt-in `Slow`/`Aspirational`/`SuperSlow` groups,
  plus `Shrinker` (the typed generator's shrink contract) and `Admission
  oracle`, which are in the default suite
- `test/BackendAgreement.hs` / `BackendCoverage.hs` — the batched backend
  drivers behind `prop_Fuzz_BackendsAgree`, and the corpus-minus-fuzz construct
  exception list (see `fuzz-testing.md`, "Backend agreement")
- `test/AdmissionOracle.hs` — the ModalityInfer ↔ IRCompiler admission
  contract (see `modality-and-admission.md`, "The admission contract"), driven by the `Slow` property
  `prop_Fuzz_AdmissionTotality`
- `test/TestCaseParser.hs` / `ArbitrarySPLL.hs` / `TestTolerances.hs` — the
  `.tst` parser, QuickCheck generators, shared numeric tolerances

## The `.tst` format

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

## `.tst` expectations: prob, dim and the impossible shape

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

## Known-issues corpus (`test/cases/known-issues/`)

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
expect-failure: refused "some substring"       -- compiles; some variant is absent with a recorded refusal reason containing this
expect-failure: no-code                        -- compiles, but generate/probability/integrate is silently absent
expect-failure: wrong-result                   -- compiles and runs; the p()/cdf() rows below pin the known-wrong value
expect-failure: broken                         -- mechanism unpinned; the p()/cdf() rows below state the idealized value instead
```

`crash`/`diagnostic` are checked against an exception thrown while *forcing*
`compile`'s result — a graceful `Left` (an intended, working refusal) does not
satisfy either; that is what `TestRejection.hs` is for. `refused` is the
graceful form of an open capability gap: the compile succeeds and some
function's variant is absent with a recorded reason (`refusedVariants`)
containing the substring. Fourteen `diagnostic`/`crash` pins moved there when
static refusals stopped crashing the compile. **`wrong-result` rows
are currently not evaluated by anything**: `checkExpectFailure` treats the
shape as documentation (`return ()`), and this folder is excluded from the
corpus sweeps that would otherwise compare them. So a `wrong-result` pin does
*not* fail the day its bug is fixed -- editing its rows to any value still
passes (found while fixing `planSumWithSunkDiscreteDrawDim`, task
plan-sum-with-sunk-discrete-draw-reports-density; follow-up docs task
`known-issues-wrong-result-rows-unchecked`). Until that lands, verify a fix to
a `wrong-result` pin by moving the program into the ordinary corpus.

`broken` is the loose fallback for a repro that was migrated without
characterizing exactly how it currently fails (no exact crash message or
wrong value pinned down by hand). The rows below the header instead state the
*idealized* value -- what the fixed compiler should produce -- and
`TestKnownIssues.hs` runs each row on every backend the `backends:` header
declares (read as everywhere else: no header means interpreter, julia,
python) that it can evaluate -- the interpreter in-process, and Python through
End2End's own emitted-module script -- and asserts the compiled program does
**not yet** match it on any of them, within the ordinary `probTolerance`; a runtime crash, a refused compile, a missing variant, or a
merely different number are all "still broken" and pass, while an exact match
fails loudly ("may be fixed now"), naming the backend. The header says where
the bug is pinned: a Python-only bug (e.g. the emitted module failing to load)
is spelled `backends: python`, so the interpreter already giving the right
answer is not misreported as a fix. Julia, batched and dense are not evaluated
here (a missing `julia` binary would read as "still broken", a silently green
pin), and a `broken` pin declaring *only* those fails loudly rather than
passing vacuously. This trades away the free "which exact
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

## Rewrite invariance

`test/Rewrites.hs` holds four semantics-preserving source rewrites (task
`rewrite-invariance-net-draw-apply-helper-alias`, law-carrying-modality M0):
draw introduction (`C[e]` → `draw z = e in C[z]`, only where `C` evaluates `e`
once and unconditionally -- never out of an `if` arm or a function body),
linear inlining (its inverse, when the variable occurs once and not under a
function body), helper extraction (a subterm becomes a call of a new top-level
function over its free locals) and alias introduction (`draw y = x in
b[x := y]`). The task's "`draw x = e in b` ⇄ `(\x -> b) e`" is not one of them:
the two spellings parse to the same AST, which a unit test pins.

`TestRewrites` applies every family at every site of every interpreter-routed,
non-neural, non-slow corpus program (one test per program, ~4000 variants,
~50 CPU-s; group `RewriteInvarianceCorpus`, which lives in the opt-in `Slow`
group) and to the ten probe pairs (group `RewriteInvariance`, default suite) of law-carrying-modality's evidence table,
judging each pair with the three-outcome oracle: both answer → probability and
dim must agree (hard); original answers, rewrite does not → logged, unless
`refusalIsHard` has promoted that family (each flips in the commit of the
law-carrying milestone that claims it); original does not, rewrite does → the
rewrite is checked against its own forward sampler. Known disagreements are
listed in `knownDivergences` with their tracking task and a
`known-issues/` pin; an entry that stops diverging fails, so the list cannot
rot. The logged frontier is visible with `TASTY_HIDE_SUCCESSES=false`.

Helper extraction names a helper's parameters after the caller's variables,
which is how it found `enumerateAppliedLambda`'s capture: the loop bound the
callee's parameter around the argument's own measure, so `h b` called under an
enumerated `draw b` measured `b == b` and lost the draw's weight (29 corpus
programs; `let-bindings/helperParamShadowsEnumeratedDraw`).

## Slow and Aspirational tests

Three tiers, each opt-in by environment variable:

| tier | how to run | expected | run it |
|---|---|---|---|
| default | `stack test` | **green** | after every step; the gate |
| `Slow` | `NEST_SLOW_TESTS=1 stack test` | **green** | before a merge or a push |
| `Aspirational` | `NEST_ASPIRATIONAL_TESTS=1 stack test` | red/flaky, by definition | when working on what it pins |

(`SuperSlow`, `NEST_SUPERSLOW_TESTS=1`, is the sampling-vs-PDF fuzz tier; see
`docs/fuzz-testing.md`.)

**`Slow` is expected green.** A red `Slow` run is a regression like a red
default run, unless it is a `Fuzz` property hitting a new seed-dependent
failure (see below). It holds tests that are expensive and unlikely to catch
regressions outside the code they pin: a `.tst` file's `slow` header (honoured
by `known-issues/` pins too), a `TestInternals.hs` case placed in
`slowInternalsTests`, the corpus-wide rewrite-invariance sweep, and the `Fuzz`
properties not listed as aspirational. The depth-4 plan-enumeration stress
programs (`planHelperOnFoldResult*`, `planFoldDisjunction*`, ~10 s per compile)
and `planEnumRecJointState` are `slow`; their correctness is pinned at small
depth by the default suite's polynomial-growth tests. A full `Slow` run takes
about 4 minutes on 4 cores.

**`Aspirational` holds what we want to guarantee but cannot yet**: tests that
fail or flake at HEAD. Today that is five `Fuzz` properties
(`TestFuzz.aspirationalFuzzNames`, each entry with the evidence that put it
there). Measured 2026-10-01 over three seeds, `TypedCompileNeverCrashes` and
`ProbNeverGenerateBacked` failed every time. The other three
(`TopKZeroMatchesExact`, `TopKNeverInflates`,
`BranchCountingDoesNotChangeProbability`) failed once, on one shared program.
Rules:

- Moving a test **into** `Aspirational` is how a known-red test stops making
  `Slow` red. It is not a way to make a change look green. A test your change
  broke is a regression; it does not go here.
- Moving a test **out** is part of fixing what it finds: a fix that makes an
  aspirational property pass moves it back into `Slow` in the same commit.
- A `Fuzz` property is seed-dependent, so a `Slow` property can still fail on
  a seed nobody has tried. Treat that as a new finding: reproduce it with its
  `--quickcheck-replay` seed and file it. Move the property to
  `Aspirational` only once it is shown to fail repeatably.
- An `aspirationalFuzzNames` entry naming no property fails the tree build, so
  the list cannot rot past a rename.

Each `Fuzz` property carries a whole-property wall-clock deadline (120s,
`NEST_FUZZ_SCALE`-scalable) on top of its per-case one, so a property that
would otherwise multiply a high discard rate by a 5s-per-draw hang drains its
remaining draws as discards and reports "Gave up" instead of having to be
abandoned. A one-line note on stderr names any property that hit it. See
`docs/fuzz-testing.md`, "Two budgets".

## Test suite time

**Every commit message that reports a test result also reports the default
suite's wall time against the base it was measured from**: not just
`1484/1484 green` but `1484/1484 green (45s -> 50s)`. Measure both numbers the
same way, on the same machine, with a warm build: `stack test` end to end, or
both test binaries run directly and their times added. Say which. A change
that moves tests between tiers reports the tier times it affected too. The
log this produces is how a slowdown gets traced to the commit that caused it.
The suite has had to be trimmed back repeatedly because nobody saw it grow.
There is no hard gate yet; the delta is for the audit.

The default suite runs in about a minute on 4 cores (main ~50 s, corpus
~17 s). What keeps it there, so a regression is recognisable: the test
binaries run with `-A64m -n4m` (`package.yaml`; the default nursery cost
~15 s of parallel GC); the Julia End2End batch is split into 4 parallel
shards run under `julia --compile=min` (one LLVM-compiled batch was a 60 s
single test); and the batched-eligibility compiles run in parallel while the
tree is built (`parMapIO`). They are deliberately not deferred into the tests
that read them: shared lazy results forced by many tasty threads at once is
the shape that deadlocked the fuzz tier (docs-repo task
`fuzz-tier-blackhole-deadlock-at-property-start`). Don't introduce
`unsafeInterleaveIO`/`unsafePerformIO` values that several tests force. When
the suite slows down, time it per group
(`--ta '-p "$2==\"End2End\""'`) and look for a single test on the
critical path before cutting coverage.

## Benchmarks

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
