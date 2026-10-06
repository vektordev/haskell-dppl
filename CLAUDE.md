# CLAUDE.md

Guidance for Claude Code in this repository. If something here is wrong or
outdated, correct it. Keep this file an index: mechanism detail goes in
`docs/`, linked from below.

## Project

NeST (Neuro-Symbolic Transpiler) — a compiler for SPLL (Sum-Product Loop
Programming), a probabilistic programming language. Compiles probabilistic
programs to Python or Julia, supporting neural network integration and
probabilistic inference (sampling, exact probability, integration). Every
program compiles into three variants — **generate**, **probability**,
**integrate** — each present only where inference is tractable.

## Build & Run

```bash
stack build
stack test                     # default suite (both test binaries)
stack run -- -i file.ppl compile -o output.py -l python   # -o is required
stack run -- -i file.ppl compile -o output.jl -l julia
stack run -- -i file.ppl generate
stack run -- -i file.ppl probability -x 0.5               # P(X=0.5)
stack run -- -i file.ppl cumulative -x 0.5                # P(X<=0.5)

stack test --ta '-l'                                      # list test names
stack test --ta '-p "/End2End.Interpreter/ && /dice/"'    # select tests
stack test haskell-dppl:test:haskell-dppl-test-corpus --ta '-p ...'  # one binary
TASTY_HIDE_SUCCESSES=false stack test                     # show every test + timings
NEST_FULL_TESTS=1 stack test                              # execute every corpus check
```

- The corpus sweeps skip a program whose emitted code, `.tst` rows, runtime
  and harness are unchanged since it last passed. The manifest is
  `.stack-work/nest-impact-manifest`, per worktree. Skipped checks pass with
  the label `skipped: unchanged since <commit>`, and a summary line follows
  the run. `NEST_FULL_TESTS=1` executes everything. See `docs/testing.md`,
  "Impact analysis".

- `stack test` runs two test binaries: `haskell-dppl-test` (everything) and
  `haskell-dppl-test-corpus` (the `Corpus` group). A bare `--ta PATTERN` goes
  to both, and a binary it matches nothing in reports "All 0 tests passed".
  To target one, use the full `package:test:suite` form shown above.
- Store test output in a temp file and grep that. Don't rerun to grep again.
- CLI flags: `-v`, `-O 0-2`, `-k CUTOFF` (topK), `-c` (branch counts), `-d`
  (dump AST/IR after each stage), `--logSpace`, `--batched`, `--marginals`,
  `--marginalSlots N`, `--materializationBudget N`, `--noTypeCheck`,
  `--pruneAnyChecks`, `--no{Integrate,Probability,Generate}`. Subcommand
  flags: `--help`.
- Use `stack`, never `cabal`. `package.yaml` is the source, the `.cabal` is
  generated.

## Rules

- **Never rebase; integrate with `git merge`.** Commit hashes are cited in
  the docs-repo tickets and in commit messages, and a rebase rewrites them.
  `pull.rebase` is `false` and a local `pre-rebase` hook refuses rebases
  (override: `NEST_ALLOW_REBASE=1`, only when the user asks).
- **Zero warnings.** `src/`, `app/` and `test/` build with `-Wall -Wcompat
  -Wincomplete-record-updates -Wredundant-constraints -Werror`. Don't add
  `-Wno-*` flags to `package.yaml`. Fix the code. For a real false positive,
  use a module-scoped `OPTIONS_GHC` with a comment explaining why (today:
  `test/ArbitrarySPLL.hs` `-Wno-orphans`, `IRCompiler` `-fmax-pmcheck-models`).
- **Test tiers.** Default `stack test` must be green after every step.
  `NEST_SLOW_TESTS=1 NEST_FULL_TESTS=1` must be green before a merge or push.
  `NEST_ASPIRATIONAL_TESTS=1` holds tests known to be red. A test your change
  broke is a regression and does not go into Aspirational. A fix that makes
  an aspirational test pass moves it back to Slow in the same commit.
  Details: `docs/testing.md`.
- **Report suite time in commits.** A commit message that reports a test
  result also reports the default suite's wall time against its base,
  measured the same way on a warm build with `NEST_FULL_TESTS=1`, e.g.
  `3203/3203 green (90s -> 97s)`.
- **Static refusals use `Semiring.refuse`, not `error`.** A shape an engine
  can't handle becomes an absent variant with a recorded reason. `error` is
  for internal invariants only (`docs/modality-and-admission.md`).
- **Never hand-write a linear identity on a probability.** Use the
  `Semiring` (`srComplement`, `srZero`, ...). Any new complement or
  subtraction site must compile its operand unpruned (`IRCompiler.unpruned`)
  (`docs/semiring-presult-internals.md`).
- **Generated names go in `SPLL.ReservedNames`.** A new runtime function or
  Julia `Base` call goes in that backend's escaped-name list. The tests name
  anything missing (`docs/language-frontend.md`).
- **Emitted `Double`s go through `pyDouble`/`juliaDouble`.** Python and Julia
  have no `Infinity`/`NaN` names (`docs/backends.md`).
- **A new public `pythonLib` function needs a classification** in
  `test/prelude_numerics_probe.py` (`docs/backends.md`).
- **A new `RType` constructor means grepping for every match on `RType`.**
  Catch-alls such as `RInfer.matches _ _ = False` fail silently on it.
- **Benchmarks**: warm up once before timing, since the first run includes
  stack's rebuild.

## Pipeline

```
source → Parser → Validator → PerValue (helper expansion) → CalleeNormalize
  → RInfer (+ Monomorphize on failure) → Analysis (DiscreteValues) → DrawSinking
  → ForwardChaining → ModalityInfer → Analysis (IsConditional)
  → IRCompiler (generate / probability / integrate) → PerValue (install)
  → IRSelectPass (batched only) → IROptimizer → CodeGen{PyTorch,PyTorchBatched,Julia}
```

`SPLL.Prelude.compile` is the authority on stage order.

## Modules

`src/SPLL/`:

- `Parser` — megaparsec surface parser, with desugaring of `draw`/`define`/`observe`/patterns.
- `Lang/Types`, `Lang/Lang` — `Expr`/`ExprF`/`Value`/`Program`, plus generic traversals and substitution.
- `Validator` — structural checks on a parsed program (reserved names, neural shapes, ...).
- `CalleeNormalize` — rewrites function values in callee position into lambdas the compiler can see.
- `Typing/RInfer` — return-type (`RType`) inference with source-positioned errors.
- `Typing/Monomorphize` — clones polymorphic top-level functions once per type they are used at.
- `Typing/RType`, `Typing/PType`, `Typing/Typing` — type and annotation (`TypeInfo`, `Tag`) definitions.
- `Typing/AlgebraicDataTypes` — implicit ADT functions (constructors, accessors, tests).
- `Typing/ForwardChaining` — chain names and invertibility certificates (point inversion).
- `Typing/Determinism` — forward determinism dataflow with a call-graph fixpoint.
- `Typing/Modality`, `Typing/ModalityInfer` — the capability lattice and its inference, projected to `PType`.
- `Typing/Infer` — legacy all-in-one typing entry point, used by tests.
- `InferenceRule` — `RType` schemes of the built-in expression forms, used by RInfer.
- `Analysis` — `DiscreteValues`/`IsConditional` tags, enumeration domains and decomposability verdicts.
- `DrawSinking` — moves enumerable `draw`s into the operand that reads them.
- `ObservationMask`, `MaskVariants` — which `ANY` query shapes a function answers, plus their per-mask variants and runtime dispatcher.
- `PerValue` — per-value queries: a signature's `Enumerated` slot answered as one vector over its domain.
- `IRCompiler` — AST to IR for all three variants, holding all the inference engines.
- `Semiring` — `PResult` combinators over the linear/log/max-product semirings.
- `IntermediateRepresentation` — `IRExpr` and `IRFunGroup`.
- `IRSelectPass` — `IRIf` → `IRSelect` for batched mode.
- `IROptimizer` — constant folding, CSE and let-in optimization.
- `CodeGenPyTorch`, `CodeGenPyTorchBatched`, `CodeGenJulia` — the backends.
- `AutoNeural` — generated readLogits/writeLogits functions and partition plans for neural declarations.
- `ReservedNames` — the single registry of compiler-claimed and target-language names.
- `Prelude` — `compile`, smart constructors and the `run*` query entry points.
- `Examples` — hand-built example programs.

`src/`: `IRInterpreter` (reference semantics), `PredefinedFunctions`
(InjF table: forward, inverse, derivatives), `StandardLibrary` (IR
stdlib), `MockNN` (mock networks for tests), `PrettyPrint`, `Utils`.
`app/Main.hs` is the CLI. The runtimes are `pythonLib.py`,
`pythonLibBatched.py` and `juliaLib.jl`.

## Documentation index (`docs/`)

| doc | covers |
|---|---|
| `pipeline-and-types.md` | stage order, `Expr`/`TypeInfo`/`Value`/`MultiValue`/`CompilerConfig`, the `PType` order, the `-d` dump |
| `language-frontend.md` | `draw` vs `define`, `observe`, type signatures, reserved names and mangling, type-error provenance, monomorphization |
| `modality-and-admission.md` | the Modality layer, conditioning inside `if` arms, re-inferring recovered variables, refusals as absent variants, the admission contract |
| `witness-inversion-engines.md` | plan-guided enumeration, set-valued witnesses, affine Gaussian marginalisation, witnessing a named function's parameter, forward-chaining acyclicity |
| `callee-normalization.md` | callee rewrites, pointwise lifting of arrow-typed `if` mixtures |
| `enumeration.md` | enumerated branches, enumerability across calls, draw sinking, marginal materialization, the dense budget gate, agreement fusion, tensors in the IR |
| `semiring-presult-internals.md` | `PResult` combinators, log space, dims, the impossibility flag, branch counting, `anySafeShared`, topK and lower bounds, the query-type guard |
| `observation-masks.md` | `ANY` query shapes, correlation classes, per-mask variants |
| `per-value-queries.md` | `Enumerated` signatures, the per-value result layout, fast path vs fallback, refusals |
| `neural.md` | neural declarations, input types (`Tensor`), `of` annotations, the categorical sampler, readLogits/writeLogits |
| `batched-mode-pytorch-tensorizer.md` | batched backend, dense mode, refusals |
| `backends.md` | runtime libraries under torch, float literals, Python nesting spill, safe unary math |
| `testing.md` | suite layout, `.tst` format and expectations, the known-issues corpus, rewrite invariance, tiers, impact analysis (skipping unchanged checks), suite time, benchmarks |
| `fuzz-testing.md` | generators, shrinking, coverage, budgets, the admission-totality and backend-agreement properties |

Design, task and investigation documents live in the separate
`~/code/NeST_internal_docs` repository.
