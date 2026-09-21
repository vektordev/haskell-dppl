-- An ADT field named `a` or `b` collides with the derived per-branch sample
-- variable the compiler generates internally for this FDecl. `compile`
-- itself succeeds (the crash is at query time, evaluating a Pair sample), so
-- this is pinned as `broken` rather than `diagnostic`/`crash` -- neither of
-- those shapes runs a query, only `compile`. The identical program with
-- fields renamed to p/q (test/cases/data-structures/adtMixedArityCtors.ppl)
-- compiles and correctly answers p(Pair 0.5 0.25) = (0.7, 2.0) -- the
-- idealized value below.
expect-failure: broken
p(Pair 0.5 0.25)=(0.7, 2.0)
