# Surface language and front end

Binding forms, `observe`, type signatures, reserved names, type-error reporting and monomorphization.

## Binding forms: `draw` and `define`

There is no `let` in the surface language (design `let-binding-semantics`).
The two binding forms differ only when the right-hand side is random, and there
they give different distributions, so the author has to pick:

- `draw x = e in body` — **eager**: `x` is one sample of `e`, shared by every
  use. The parser desugars it to `(\x -> body) e` (`SPLL.Prelude.letIn`), which
  is the shape every downstream pass calls a "let". This is what `let` used to
  mean.
- `define x = e in body` — **lazy**: `x` stands for `e` itself, so every use is
  an independent draw. The parser eliminates it on the spot by capture-avoiding
  substitution (`SPLL.Lang.Lang.substituteVar`); no later pass ever sees it.

Both accept the destructuring patterns (`(a, b)`, `h : t`, `Left x`, `[]`), and a
destructuring `define` is lazy per name. A destructuring `draw` is one sample:
the tuple and cons patterns bind the RHS to a generated `p_d<n>` and project
every name from it (`test/cases/let-bindings/drawDestructured*`). `let` stays reserved and is refused
with a diagnostic naming both forms. Prose elsewhere in this file (and in
`docs/`) says "`let`" for the eager binding; read it as `draw`.

## `observe` (Maybe-valued conditioning)

`observe base pred` is parser sugar, not a dedicated `Expr` constructor —
it desugars to `let v = base in if pred v then right v else left ()`
(`Just x = right x`, `Nothing = left ()`), giving
`p(Just v) = p(base = v) · p(pred v)` and, via structural `ANY`
marginalisation, a proper `Maybe`-valued distribution for free
(`p(Just ANY) + p(Nothing) = 1`). Conditioning is
`p(Just v) / p(Just ANY)`.

The base must be let-bound, not spliced in twice (else a probabilistic
base becomes two independent draws), and a literal lambda predicate is
beta-reduced at parse time — otherwise the bound variable is invisible to
inversion and compilation fails.

On a **continuous** observation the denominator `p(Just ANY)` is answered by
the set-witness engine: a wildcard in a constructor slot leaves the tag pinned
but the payload unconstrained, so the point constraint is dropped and the
observation's interval kept, measured as a CDF difference (dim 0) rather than
a density. `intersectSet` spells that as `WChoice`, a *runtime* choice of
constraint set — the wildcard is a property of the query sample and has no
static trace in the witness template.

`invertToWorlds` has cases for the boolean connectives (`and`/`or`/`not`), so
`(v > lo) && (v < hi)` compiles the same as the nested-if spelling: each leaf
is inverted at both canonical polarities (`invertBoolToWorlds`, reusing
`invertToWorlds` itself the same way the `IfThenElse` condition case already
does), then recombined. `and`/`or` at their "natural" polarity (and+True,
or+False) intersect directly; the other polarity needs a disjoint
decomposition (`not(a&&b) = not(a) or (a&&not(b))`, `a||b = a or
(not(a)&&b)`) so the two possibly-overlapping sets of worlds are never both
measured — getting that wrong double-counts the overlap. `not` just swaps
which list is which. Mirrors the plan-guided engine's analogous
`planInvert`/`planInvertBool` fold over (True-worlds, False-worlds) pairs.
Corpus: `observeTwoSidedIntervalAnd` (the `&&` twin of `observeTwoSidedInterval`)
and `observeDisjointTails` (`||`, the double-counting canary).

## Type signatures

A top-level definition may carry a signature, `f :: T` (`SPLL.Parser.pSignature`,
`Program.signatures`). It is optional: a definition without one is typed by
inference alone. The type grammar is the ordinary one, plus arrows without
parentheses at the top (`Symbol -> [Symbol] -> (Int, Face)`), tuples of any
width (right-nested, `(a, b, c)` is `(a, (b, c))`), list types `[t]`, and the
per-value marker `Enumerated t` (see `per-value-queries.md`). Only `name ::` is
tentative, so a broken signature is reported where it breaks.

A signature *constrains* inference: RInfer adds `type(f) ~ T` after every
other constraint, in both the monomorphic and the generalising pass, so a
definition that disagrees is reported "In the type signature of 'f'". A
signature naming no definition, two signatures for one name, and more than one
`Enumerated` slot are refused by `SPLL.PerValue.validateSignatures`. A
`NotSetYet` in a signature is a hole (a fresh variable); only the compiler's
own helper signatures use it.

## Reserved names: `SPLL.ReservedNames` is the one registry

Every name the pipeline claims for itself lives in `SPLL.ReservedNames`: the
surface keywords, the distribution primitives, the binders generated code
declares (`sample`, `acc_prob`, `top_k_cutoff`, `TOP_K_CUTOFF`, `ACC_PROB_INIT`), the temporary
prefixes (`l_`, `cse_`, a leading `_`), chain names (`ast<n>`), the parser's
own desugaring binders (`p_d<n>`, `p_ob<n>`, and CalleeNormalize's
`p_eta<n>` for an eta-expanded alias), the per-function variant
suffixes (`_gen`, `_prob`, ...), the group suffixes (`_auto`, and the semiring
tags `map`/`count`/`sumprod`), and the target-language keyword lists. A user
identifier landing on a compiler name used to be accepted and misbehave: a
parameter called `sample` was captured by every probability function's query
binder (a wrong density in the interpreter, a duplicate-argument module in
Python and Julia), a local `b_gen` was read as a generator call by
`isEffectfulVar`, and a function `n_auto` beside a network `n` emitted two
Python classes of which the second won.

Two checks consume it. `Parser.pIdentifier` refuses a reserved name in the
value namespace, reported through `registerParseError` at the name's own
position (a plain `fail` is swallowed by the top-level backtracking and
reports only column 1). `Validator.validateReservedNames` repeats the check on
the AST (`internalNameReason`, which exempts the frontend's `p_d`/`p_ob`/`p_eta`
binders) for programs built without the parser, and is the only place the
*derived-group* collisions are visible (`groupNameCollisions`: `n_auto` beside
neural `n`, `f_map`/`f_count` beside `f`) -- checked as collisions rather than
blanket suffix bans, since `word_count` alone is an ordinary name. Adding a
generated name anywhere means adding it to the registry and a representative
to `TestInternals`' `reserved names` group.

Target-language names are the exception: those are **mangled** at emission,
never rejected, so a program's legality never depends on its backend.
`renameADTIdentifiers` covers ADT names and `mangleUserIdentifiers` everything
else (definition names, and every parameter/`draw` binder by scope-aware
alpha-renaming, so free names such as runtime functions are never touched),
both with the backend's `pyMangle`/`juliaMangle`. The escaped set is every
name the emitted code already uses. For Python (`pythonReservedIdentifiers`)
that is the keywords, `self` (every method's receiver), the runtime's classes
(`pythonRuntimeClassNames`: `T`, `Left`, `InferenceList`, ...), everything else
`from pythonLib* import *` brings in (`pythonRuntimeValueNames`: `randn`, `eq`,
and `math`'s re-exports `exp`, `pi`, `e`, `factorial`, ...), and **all** of
Python's builtins (`pythonBuiltinNames`). For Julia (`juliaReservedIdentifiers`)
it is the keywords, `juliaLib`'s export list, and the `Base` names codegen
emits (`juliaBaseNames`: `randn`, `rand`, `sum`, `string`, ...; a curated
subset, since all of `Base` is too big). A parameter `randn` used to capture the
body's `Normal` draw in both backends, and a definition `randn` replaced the
Python runtime's at module scope (task `python-runtime-name-shadowing`).

The lists are hand-maintained, so emitted code never depends on the build
machine's Python, and three tests keep them honest. `TestInternals` asks
`python3` for the runtimes' real star-import surface plus `dir(builtins)`, and
checks `juliaLib.jl`'s `export` line. The End2End property `Julia free names
are escaped` scans the corpus's emitted Julia for any called name the module
does not define. **Adding a runtime function or a new `Base` call in
CodeGenJulia means adding it to the list**, and the tests name what is
missing. Consequences worth knowing: a definition named like a builtin changes
its Python API name (`factorial` is `module.factorial_`), and a Julia
definition so named gets `name__gen`.

A function group's class is its capitalised name made unique by
`groupClassName` against all of those and the ADT classes: capitalising landed
`t` on the runtime's tuple class `T` (every tuple broke) and `foo` on
constructor `Foo`'s class (a silently wrong `p(Foo) = 0`).

## Type errors carry the source they came from

A unification failure is reported the way GHC reports one -- a position, the two
types in the vocabulary the *user* writes, and a context chain naming what they
wrote:

```
prog.spll:1:12:
    Couldn't match type '[s]' with '(u, v)'
      In the function 'tail'
      In the pattern: h : t
```

`RInfer`'s `Constraint` carries a `Maybe Provenance` (the originating
expression's `srcPos` plus a description from `describeExpr`). It used to carry
a `Maybe String` holding only the *phase* that emitted the constraint
(`"Apply"`, `"inferResultingType"`), and `solver` discarded even that before
throwing, so `addRTypeInfo` could only print
`UnificationFail (TADT "Scene") (ListOf (TADT "Object"))` followed by 88 lines
of program and constraint dump. That dump still exists and is still useful for
work on `RInfer`; it is behind `-v`.

**There is deliberately no table keyed on pairs of types.** A rule that
recognised, say, an ADT meeting a list and emitted bespoke prose about cons
patterns would improve one program shape and have to be re-derived at the next
site; naming the source improves every unification failure at once. New
diagnostics here should follow that: make the mechanism carry more, do not add
a case. `TestRejection.TypeErrorDiagnostic` includes a case on an unrelated
ill-typed program precisely so this cannot silently degenerate.

Three things keep positions available, and each is load-bearing:

- `TypeInfo.srcPos :: Maybe SourceSpan`, defaulted by `makeTypeInfo`, so adding
  it changed no construction site. It is `Nothing` on everything the parser did
  not build (the prelude, `SPLL.Examples`, anything a later pass synthesizes),
  and every diagnostic degrades gracefully rather than requiring it.
- `Parser.withSpan` wraps `term` and `expr` -- **and the atoms inside
  `application`**, which calls `atom` directly and so would otherwise leave
  every argument position-less. Cross-function type errors had no position at
  all until that was fixed.
- Nodes that are *built* rather than parsed inherit a span through
  `fillMissingSpans`, which only fills where `srcPos` is `Nothing`:
  `stampSynthesized` gives `letInDestructor`'s generated `head`/`tail`
  scaffolding the span of the pattern it came from (plus
  `spanDesugaredFrom`, the `In the pattern: h : t` line), and `keepSpanOf`
  gives `normalizeExpr`'s rebuilt `ReadNN`/`InjF`/projector nodes the span of
  the application they replaced. Without these a message could point at, or
  print, the generated `p_d0` binder -- pinned against by
  `TestRejection.TypeErrorDiagnostic`.

`Eq` on `TypeInfo`/`Expr`/`Program` stays **derived and structural**: two values
from different source positions really are different. The position-blind
comparison is a separate `Equiv`/`(~=)` class in `SPLL.Lang.Types`, identical to
the derived `Eq` on spanless values, used by the parser tests that compare a
parse against a constructed value or two parses of different source strings.
`TestParser`'s `prop_EquivAgreesWithEqWithoutSpans`/`prop_EquivIgnoresSpans` pin
both halves, so the switch neither weakened those tests nor made them vacuous.

**Known limitation**: a failure has two sides and is reported against one --
whichever constraint the solver reached when the contradiction materialised,
which is ordering-dependent. Naming both needs provenance on *types* rather than
constraints; docs-repo task `type-error-blames-one-side-only`. The broader
triage of every other user-facing error site is the docs-repo investigation
`user-facing-error-site-inventory`.

## Polymorphic top-level functions are monomorphized

RInfer types every top-level declaration monomorphically: one type, shared by
all uses. `add x y = x + y` used at both `Float` and `Int` therefore used to be
a unification failure. When -- and only when -- that monomorphic inference
rejects a program, `RInfer.retryMonomorphized` retries it with
let-generalisation (`inferGeneralized`: HM over the call graph's strongly
connected components, dependencies first, class constraints on a generalised
variable carried in the scheme and re-checked at each instantiation), then
`SPLL.Typing.Monomorphize` clones each polymorphic declaration once per type it
is used at, and the cloned program goes through the ordinary monomorphic
inference. Every later pass sees an ordinary program with more declarations.

Naming: a declaration used at one type keeps its name; one used at several
becomes `add__int`/`add__float` (`mangleName`, a fixed-arity prefix encoding of
the type arguments, so `__`-separated and unambiguous) and no longer exists
under its own name; an uninstantiated polymorphic declaration stays as it was
(its free type variables default to the float variant, as before). A mangled
name that collides with a user declaration gets `_` appended.

Retrying only on failure is deliberate: every program the old inference
accepted is typed exactly as before, and if the generalised retry fails too
the **original** monomorphic diagnostic is reported, so no existing error text
moved. The monomorphization happens at the RInfer seam, not in IRCompiler as
the design first sketched, because ForwardChaining, ModalityInfer, Determinism
and Analysis all key off declaration names and `rType`s and would otherwise
each need to see through a polymorphic body. Out of scope: passing a
polymorphic function as a value (higher-order polymorphism) -- it is
instantiated at the one type its use forces, like any reference. Tests:
`test/TestMonomorphize.hs`; corpus `arithmetic/polyTwoTypes`,
`polyNestedTwoTypes`.
