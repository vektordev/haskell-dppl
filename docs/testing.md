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
  folding happened to delete). It compiles the corpus under six configs.
  The topK thresholds 0, 0.05 and 0.1 share one compile, re-thresholded with
  `withTopKCutoff`, because the cutoff is a runtime parameter. topK +
  `logSpace` keeps its own compile.
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
- `test/ScalingCheck.hs` — the pure half of the known-issues performance pins:
  program-family templates and the growth verdict (see "Performance pins")
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
- `test/CorpusSweep.hs` — the registry every whole-corpus check is built
  through (see "Corpus sweeps" below)

## Corpus sweeps

A check that iterates over the programs of `test/cases/` is a **sweep**, and
every sweep is built through `CorpusSweep.corpusSweep` (one tasty node per
program) or `corpusSweepAll` (one node built from the whole selected slice: a
batch, a few aggregate properties, a single test looping over it), from a
`SweepSpec`:

```haskell
SweepSpec { sweepName = "End2End.Python", sweepTier = Default, sweepSlow = SkipSlow
          , sweepSelect = \e -> routed Python e && hasQueries e
          , sweepNote = "every p()/cdf() row against the emitted Python" }
```

A sweep costs one compile or run per corpus program, about 500 of them, so
adding one is not like adding a unit test. Spelling it as a `SweepSpec` makes
it one visible line in a diff, and `grep -n 'SweepSpec' test/*.hs` lists them
all.

- **The corpus is parsed once per binary** (`loadCorpus`, in `Spec.hs` and
  `SpecCorpus.hs`) and handed to every sweep. A `CorpusEntry` holds the parsed
  program and the raw `.tst` rows. Compiles and mock-shaped rows are each
  sweep's own business (`End2EndTesting.shapedCases`).
- **Tiering.** `sweepTier` (`Default`, `Slow`, `Aspirational`) decides which
  environment variable the sweep needs. With its tier off it builds an empty
  group. `sweepSlow` applies the `.tst` `slow` header: `SkipSlow` (the usual
  policy), `OnlySlow` (the `End2End (slow)` twins) or `IgnoreSlow` (static
  checks that neither compile nor run the program).
- **The cost table.** Every test of a sweep runs under a clock. After the run,
  each binary prints one line per sweep that ran a test: tier, programs
  selected, tests run, build time (the `IO` that built the tree, e.g.
  BatchedPython's eligibility compiles) and test time summed over its tests.
  The last line gives the sweeps' share of the time summed over every test of
  the binary. Tests run in parallel, so summed times exceed the wall time and
  include waiting for a core. Compare them between runs on one machine, not
  with the wall clock. A sweep whose tests share lazily compiled programs
  (the `Corpus` properties' per-config maps) charges each compile to
  whichever test forced it first.
- **The bypass check.** `Internals."no corpus loader is called outside
  CorpusSweep"` fails if a test module other than `CorpusSweep.hs` (and
  `TestCaseParser.hs`, which defines `listCorpusPplFiles` and resolves single
  programs by name with it) calls a corpus loader (`sweepLoaderNames`). A
  lookup of one program by name (`corpusPplPath`) is not a sweep and is fine
  anywhere.

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
expect-failure: growth above polynomial 2      -- a performance wall: a templated family still grows faster than this
expect-failure: code-size above 60 KB          -- the emitted Python is still larger than this
expect-failure: hang                           -- the compile still runs into its cap instead of finishing
```

`crash`/`diagnostic` are checked against an exception thrown while *forcing*
`compile`'s result — a graceful `Left` (an intended, working refusal) does not
satisfy either; that is what `TestRejection.hs` is for. `refused` is the
graceful form of an open capability gap: the compile succeeds and some
function's variant is absent with a recorded reason (`refusedVariants`)
containing the substring. Fourteen `diagnostic`/`crash` pins moved there when
static refusals stopped crashing the compile. `wrong-result` rows pin the
value the bug produces today: the program must compile, and each p()/cdf()
row must still match its pinned (wrong) value, within `probTolerance`, on
every backend the `backends:` header declares that the harness can evaluate
(the same interpreter and Python checks `broken` uses, described next). A
different number, a crash, a refused compile or query, or a pin with no
p()/cdf() rows all fail. So a pin fails both the day its bug is fixed (move
the program into the ordinary corpus with the idealized rows) and the day the
wrong value drifts (re-pin it). Before task
`known-issues-wrong-result-rows-unchecked` these rows were not evaluated at
all, and three of the four pins they held turned out to be fixed already.

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
pin), and a `broken` or `wrong-result` pin declaring *only* those fails
loudly rather than passing vacuously. This trades away the free "which exact
mechanism regressed" signal `diagnostic`/`wrong-result` give for robustness
against unrelated code churn shifting a pinned message or number -- appropriate
when nobody has run the repro yet to observe its actual failure mode.

### Performance pins: growth and code size

Two further `expect-failure:` shapes pin a *performance wall* rather than a
wrong answer (task known-issues-performance-scaling-checks). Both are checked
in `TestKnownIssues.hs`, with the pure half (templates, the verdict) in
`test/ScalingCheck.hs`:

```
expect-failure: growth above polynomial 2      -- or: growth above linear
knob: N = 2, 4, 6, 8, 10                       -- required; >= 2 increasing positive values
metric: code-size                              -- optional: code-size (default) | ir-size | alloc | wall-time
flags: -O 0 --noIntegrate                      -- optional, CLI spelling
cap: 10 s, 8000 MB                             -- optional per-compile cap (these are the defaults)

expect-failure: code-size above 60 KB          -- B, KB = 1000 B, MB = 10^6 B
flags: --pruneAnyChecks                        -- optional, as above; cap: too

expect-failure: hang                           -- flags: and cap: optional, as above
cap: 2 s, 500 MB                               -- state a small one: the cap is the pin's cost on every run
```

The follow-on lines come straight after the `expect-failure:` line, in any
order among themselves. `flags:` accepts `-O N`, `--noIntegrate`,
`--noProbability`, `--noGenerate`, `--pruneAnyChecks` and
`--materializationBudget N`, applied over `defaultCompilerConfig`. Any other
flag is a parse error, not ignored.

**Growth.** The `.ppl` is a template over the knob: `{{N}}`, `{{N-1}}`,
`{{i+2}}` stand for integers, and `{{for i in 1..N sep ", "}}...{{end}}`
repeats its body (inclusive bounds, an optional separator, nestable). Text
outside `{{ }}` is copied verbatim, so `of 4x.{...}` is fine. A template
beats a directory of pre-generated variants because the knob is explicit.
The harness compiles each knob value in turn and takes the local log-log
slope `log(f2/f1) / log(n2/n1)` between consecutive points. That slope is the
apparent polynomial degree: exactly k for `n^k`, and rising with n for an
exponential. The pin holds once some pair's slope exceeds the degree plus
a margin (0.25 for code-size and ir-size, 0.5 for alloc, 1.0 for wall-time),
or once a point hits the cap. The climb stops there, so the expensive points
are only paid for after a fix. If every pair stays within the bound, the pin
fails with "may be fixed" and prints the table. A first point that already
hits the cap means the knob values are too large, and fails. Choose knob
values so that a family growing within the bound would stay far below the
cap: a capped point counts as evidence of superpolynomial growth.

The metrics, deterministic first: `code-size` counts the bytes of emitted
Python, `ir-size` the characters of the shown `IREnv`, `alloc` the bytes this
thread allocated during compile and codegen (GHC's per-thread allocation
counter, which parallel tests do not disturb), and `wall-time` seconds. A
wall the optimizer folds away (the module comes out linear, but the
unoptimized IR does not) is still visible at `-O 0`, or as `alloc` at the
default `-O2`.

**Code size.** The program compiles and its emitted Python must still exceed
the bound. A fix that shrinks it below the bound fails the pin.

**Hang.** The compile must still run into its cap. A compile that finishes
fails the pin as "may be fixed", and so does one that throws, because the bug
has then changed shape. A non-terminating loop that allocates hits a small
allocation cap in well under a second.

**The cap.** Every compile runs under a `timeout` and a per-thread allocation
limit (`enableAllocationLimit`), so a runaway compile is killed and recorded
as "exceeded" instead of hanging the suite or exhausting memory. Bounding
allocation also bounds what the compile can retain. A growth pin's family
point that is refused, crashes or fails to parse fails the pin, as does a
code-size pin that hits its cap: these pins describe programs that compile,
only too expensively. Positive-polarity guards ("stays polynomial") for walls
that are already fixed stay `TestInternals` growth tests, as before. The
known-issues folder holds only open bugs.

The pins today, together about 1.2 s of the default suite:
`nestedEqualityChainGrowth` (alloc at `-O2`, about 8x per level) and
`gaussianTrajectoryUnprunedModuleSize` (code size). The harness's own tests are
`KnownIssuesScaling` (templates, slopes, the climb) and `KnownIssuesHarness`
(both caps, header parsing).

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

`Corpus.TopKOperandOrder` (Slow, task
`transformation-differential-testing-m1-config-differencing`) applies one more
rewrite, `Rewrites.commuteSites`: swap the operands of one call of a
commutative built-in (`plus`, `mult`, `and`, `or`, `max`, `eq` and the int
forms). Each swapped program gets its own topK compile and answers the
original's `p()` rows at threshold 0 (must agree with the original: hard) and
0.1 (a divergence is logged as `ORDER-DEPENDENT`). Programs known to diverge are
listed in `knownOperandOrderDependent` with their tracking task, and an entry
that stops diverging fails. At landing, 393 sites over 247 programs agreed at
both thresholds; only the constructed pin `topk-pruning/topKOperandOrder`
diverges (see `semiring-presult-internals.md`, "topK Branch Pruning").

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
fail or flake at HEAD. Today that is three `Fuzz` properties
(`TestFuzz.aspirationalFuzzNames`, each entry with the evidence that put it
there). Measured 2026-10-01 over three seeds, `TypedCompileNeverCrashes` and
`ProbNeverGenerateBacked` failed every time. `SharedDrawConfigInvariants`
(topK at 0 and 0.1, branch counting) replaced three per-invariant properties
that, re-measured 2026-10-07 over six seeds, timed out in a topK compile in
four runs.
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

## Impact analysis: skipping unchanged checks

The expensive corpus sweeps execute a program only when what the check
consumes has changed since it last passed (`test/ImpactManifest.hs`; docs-repo
task `emitted-code-test-impact-analysis`). Each check hashes its inputs into a
key, and the manifest records the key of each (check, program) slot's last
pass. A check whose key matches is skipped. It still appears in the tree and
passes with the QuickCheck label `skipped: unchanged since <commit>`. After
the run, one line per sweep says how many were skipped and how many executed:

```
Impact analysis -- End2End.Interpreter: 499 unchanged, 0 run; ...; End2End.Python: 450 unchanged, 4 run
```

**Covered sweeps and their keys.** Every key also contains the check's
version constant (`End2EndTesting.*CheckVersion`) and the harness
fingerprint, which is the source of `End2EndTesting.hs`, `CorpusSweep.hs`,
`ImpactManifest.hs`, `TestCaseParser.hs` and `TestTolerances.hs`. Any edit to those files reruns
everything. A sweep defined in another module adds that module's source to
its own key (`sourcesFingerprint`), so editing it reruns that sweep only.

| sweep | key, besides version and harness |
|---|---|
| `End2End.Python` | the exact script `testPython` runs (the emitted module, the mocks, and the row checks with the tolerance spliced in), `pythonLib.py`, and `python3`'s path and version |
| `End2End.Julia` (per program, inside each shard) | the program's module and row checks as `juliaBatchTestCode` renders them under a fixed module name, `juliaLib.jl`, `julia --version`, and the flags. An all-unchanged shard starts no julia |
| `End2End.Interpreter`, `Interpreter Unoptimized` | `show` of the compiled `IREnv` (at -O2 or -O0), the parsed program's networks, writeLogits registry and ADTs, the rows, the values `testInterpreter` derives from them, the tolerances, and the interpreter fingerprint |
| `End2End.Normalization` | the `IREnv`, the same program fields, the seeded draws (`normalizationDraws`), the tolerance, and the interpreter fingerprint |
| `End2End.Python Unoptimized`, `End2End.Julia Unoptimized` | as `End2End.Python` and `End2End.Julia`, on the -O0 compile |
| `End2End.Python WriteLogits` | the exact script `testPythonWriteLogits` runs (the emitted module, the mocks, the row checks), `pythonLib.py`, and `python3`'s path and version |
| `End2End.Julia WriteLogits` (per program, inside the batch) | the program's module and row checks as `juliaWriteLogitsBody` renders them alone, `juliaLib.jl` and `julia --version` |
| `SelectPassNoOp`, `PlanEngineMatchesDense`, `BudgetZeroMatchesDefault`, `PlanEngineLogSpaceMatchesLinear` | `show` of both compiles the differential compares (scalar and select-passed; budget 0 and dense; budget 0 and default; budget-0 linear and log space), a refusal included, the program fields, the rows, the tolerance, and the interpreter fingerprint (`differentialKey`) |
| `BatchedPython.<differential>` (per program, inside each of the four torch batches) | the program's name, batched source, query groups and network mocks as the driver renders them, and the torch fingerprint: `pythonLibBatched.py`, and the torch python's path, Python version and torch version. An all-unchanged differential starts no python |
| `KnownIssues` (`broken` and `wrong-result` pins) | the `expect-failure` header, the backends checked, the `IREnv` with the program fields and rows, the interpreter fingerprint, and on Python each row's exact script and the Python runtime; `TestKnownIssues.hs` joins the harness |
| `Corpus.LogSpaceMatchesLinear` (one test per program) | the program's log-space `IREnv`, its fields, its p() rows and the tolerance, and the interpreter fingerprint; `TestCorpus.hs` joins the harness |
| `Slow.RewriteInvarianceCorpus` | the rows, and for the original and every variant (family and site) its program fields and its compile, a refusal's message included, and the interpreter fingerprint; `TestRewrites.hs` and `Rewrites.hs` join the harness. A variant whose compile timed out or crashed leaves the program unkeyed |

The **interpreter fingerprint** (M1 of the task) is the source of every
`src/` module that `IRInterpreter` transitively imports (13 of 39, read off the
import lines at run time), plus `SPLL/Prelude.hs` (the `run*C` entry points),
`stack.yaml` and the GHC version. The compiler proper (`IRCompiler`, the
optimizer, the parser, the typing passes, codegen) is outside it. A compiler
change reaches an interpreter check through the emitted `IREnv`, which is in
the key already, so a commit that leaves a program's IR unchanged reruns
nothing for it.

**What is never skipped.** The compile always runs: the key is computed from
its output. A compile that fails, or crashes while the key is rendered, has
no key, so the check executes and reports the failure. A failing check is not
recorded. A failing Julia shard records none of its programs, because the
failure cannot be attributed to one of them.

**The manifest** is `.stack-work/nest-impact-manifest`, one per checkout and
so one per worktree. The corpus binary keeps its own,
`.stack-work/nest-impact-manifest-corpus`, since the two processes may run at
once and each writes its manifest back whole. It is never committed. It maps each slot to its last
passing key, so it does not grow without bound, and a `-p` run leaves the
other slots alone. A missing or unreadable manifest means a full run.
`NEST_FULL_TESTS=1` ignores the manifest, executes every check, and records
each pass. Neither the pre-merge `Slow` run nor the timings need it (see
below); use it when a change touches the manifest keys or the harness that
computes them, since a wrong key is exactly what a cached run cannot see.

**Adding a check, or changing one.** Wrap the property in `cachedProperty`
(or `cachedBatch` for a shared process, or `cachedAction` for an HUnit
assertion) and give it a key that covers
*everything the check reads*. A value the check consumes but the key leaves
out lets a pass survive a change that should have invalidated it. When a
check's logic changes, bump its version constant; the harness hash only
backstops a forgotten bump.

**Not covered, deliberately.** Checks whose verdict is the compile itself have
nothing to skip: the `KnownIssues` crash, diagnostic, refused, no-code,
code-size, hang and growth pins, `BatchedPython`'s eligibility properties,
and `Julia free names are escaped`. Their key could only be the compiler's
source, which every compiler commit changes. The other `Corpus` properties
are one property over the whole pool, so they have no per-program slot until
each is split per program, as `Corpus.LogSpaceMatchesLinear` was. The `Slow`
batched topK differentials are not covered either.

## Test suite time

**Every commit message that reports a test result also reports the default
suite's wall time against the base it was measured from**: not just
`1484/1484 green` but `1484/1484 green (45s -> 50s)`. Measure both numbers the
same way, on the same machine, with a warm build and **a primed manifest**:
run the suite once, then time a second consecutive run on the unchanged tree
(`stack test` end to end, or both test binaries run directly and their times
added; say which). That is the cost a developer pays per step: the checks
impact analysis cannot skip, which is where growth now shows up. A first run
after a change depends on how many programs the change touched, so it is not
the audited number. Timing with `NEST_FULL_TESTS=1` is optional; report it
too when a change adds or re-keys cached checks. A change
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
the suite slows down, read the per-sweep cost table ("Corpus sweeps"
above), time it per group
(`--ta '-p "$2==\"End2End\""'`) and look for a single test on the
critical path before cutting coverage.

### Coverage-informed tiering

Before demoting a test to `Slow` for its cost, ask what the default suite
would lose. `scripts/coverage-tiering/coverage_tiering.py` answers that
offline (docs-repo task `coverage-informed-test-tiering`). It builds an HPC
build into `.stack-work-coverage`, partitions the default tier into units
(one per corpus program across every corpus sweep, one per non-corpus test
group two levels deep, one per `Corpus` property), runs the instrumented
binary once per unit with its own `HPCTIXFILE`, and runs a greedy weighted
set cover over the units' tick sets with their summed test times as cost.
Units outside the cover execute nothing the cover does not, so they are
demotion candidates. It writes `report.csv` and `report.md` under
`.stack-work-coverage/tiering/`. A human decides the moves.

```bash
scripts/coverage-tiering/coverage_tiering.py all -j 4   # build, timings, units, run, analyze
scripts/coverage-tiering/coverage_tiering.py analyze    # redo the report from existing runs
scripts/coverage-tiering/coverage_tiering.py estimate   # main binary's wall time without the candidates
```

The `timings` step runs the uninstrumented suite with `NEST_FULL_TESTS=1`, so
run it on an idle machine. The `run` step is resumable and takes about an
hour on 4 cores: each unit process spends ~15 s building the tree before it
runs anything. `haskell-dppl-exe` subprocesses are covered through a shim on
`PATH`. Python subprocesses run under `pytrace.py`, which records the lines of
`pythonLib.py`/`pythonLibBatched.py` they execute. Julia is not covered, so
units holding Julia checks are always kept. The report states the other
caveats. Tick coverage is not value coverage, and coverage moves with the
code, so re-run it when the suite has grown materially.

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
