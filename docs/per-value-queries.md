# Per-value queries

One query returns `P(slot = v, rest)` for every `v` in a discrete result
slot's domain (docs-repo task `per-value-query-over-enumerated-slot`,
`SPLL.PerValue`). The motivating case is a posterior over a finite latent, such as the
secret face in Guess-Who: one vector, not one point query per face assembled
in Python.

## Spelling

A top-level type signature marks the slot `Enumerated`:

```
main prior board =
  draw s = pick prior in
  draw truth = see (nth s board) in
  (s, truth)

posterior :: Symbol -> [Symbol] -> (Enumerated Int, Face)
posterior = main
```

Signatures are optional everywhere else and are a general feature
(`Program.signatures`, see `language-frontend.md`). `Enumerated t` may stand on
the result itself (`f :: Enumerated Int`) or on a tuple component of it, at any
tuple depth. A marker in a parameter type, inside a list, on a function-typed
component, or inside another marker is a parse error at the marker. One marked
slot per signature (v1). Several slots (a tensor-valued result) and a slot
nested in a constructor are deferred to docs-repo task
`per-value-query-v2-scope`.

## Meaning

Two properties fix it, and `test/TestPerValue.hs` checks both on every program
it covers:

- element `v` is the point query with the slot set to `v`: probability within
  1e-15, with the same dimension, impossibility flag and branch count;
- the vector's sum is the query with the slot `ANY`.

The query's own value at the marked slot is ignored, so pass `ANY` there. Every
other slot follows the ordinary query rules, `ANY` holes included. `topK`
pruning, the dimension, the impossibility flag and the branch count are each
the point query's, **per element**.

The result is the point query's layout with each field a vector in domain
order, plus the domain as a last field:

```
(probs, (dims, (imposs, values)))                -- default
(probs, (dims, (branchCounts, (imposs, values)))) -- --countBranches
```

A vector is a list in Python, an array in Julia and a rank-1 `VTensor` in the
interpreter. The domain order is the slot's `DiscreteValues` order (an `of
[...]` list's order), else the order `autoDeriveMultiValue` enumerates the
slot's type in.

## How it compiles

`SPLL.PerValue` hooks in at three places in `SPLL.Prelude`:

1. **Front end** (`expandPerValue`, before RType inference). A marked `f` gets
   helper definitions, all named in `SPLL.ReservedNames.perValueHelperSuffixes`:
   - `f__point` is `f`'s own definition, eta-expanded to its declared arity.
     `f` itself becomes a call to it, and every other function's reference to
     `f` is redirected to it. So `f` as a *value* is unchanged and only its
     query interface differs. Point queries go to `f__point`.
   - `f__slot` is the marked slot alone, under the same `draw` chain. Its
     Analysis tag is the domain, and it is dropped before IR compilation.
   - `f__prior`/`f__given`, the fast path's split, below.

   Each helper gets a signature pinning what `f`'s declared type says about
   it. That matters for `f__given`, whose slot parameter would otherwise stay
   a type variable in programs like `(c, c)`, and a comparison against a type
   variable is emitted as a float comparison (`OpApprox`).
2. **Plans** (`perValuePlans`, at `compileRTyped`). Signatures are checked
   against the inferred types and each marked function is planned: its
   parameters, whether the fast path applies, and the domain. Signatures are
   then cleared, so the per-mask variants, which re-enter `compileRTyped`,
   never plan again.
3. **Installation** (`installPerValue`, after `stripBranchCount`, so the body is
   built for the final result encoding). `f`'s probability function becomes a
   `BMap` over the domain, then one projection `BMap` per field. `f` has no
   integrate function (refused, pointing at `f__point`) and no `writeLogits`.

**Fast path.** When `f`'s body (after inlining an alias such as `posterior =
main`) begins with `draw s = E in B`, and the slot path through `B`'s draws and
tuples reaches exactly `s`, the body splits into `f__prior = E` and `f__given
... s = B`. Element `v` is `prodP` of `f__prior` at `v` and `f__given` at the
query with the slot set to `v`, with `s = v` (`srTimes`, so log space works).
The slot is never enumerated, so no `BReduce` ranges over it.

A side effect worth knowing: `f__given` sees `s` as a deterministic parameter.
A network whose input depends on `s` (`see (nth s board)`) is therefore
answered here, although the point query of the same program is intractable
(no probability function) at this compiler.

**Fallback.** Any other finite discrete slot unrolls into one `f__point` point
query per value. Under `topK` the fallback is always used, because the fast
path would prune `f__given` against an accumulated probability that lacks the
prior factor. That would not be the point query's pruning.

**Refused**, as an absent probability variant with the reason recorded
(`Semiring.refuse`'s contract, reported by `runProbNamedC`):

- a continuous slot;
- a slot with no finite domain the compiler can derive (an unbounded `Int`);
- a domain over `materializationCardinality` (`--materializationBudget`);
- `--batched`;
- a definition that does not take every declared argument as a parameter.

## Things worth knowing

- `-d`/`--marginals` show the helpers as ordinary functions. `f__point` and
  `f__given` get their own mask variants and dispatchers like any function.
- Extra-semiring groups (`--semiring=map`) of a per-value function still
  answer point queries under that semiring; per-value max-product is not
  built.
- The Python backend's nesting limit applies to the point queries, not to the
  per-value body. A 24-deep `if` chain in `f__point` fails to import ("too
  many nested parentheses"), which is why `TestPerValue`'s text-backend checks
  use an 8-face board.
