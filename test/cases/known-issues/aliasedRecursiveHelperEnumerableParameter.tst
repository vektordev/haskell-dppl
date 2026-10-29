-- decreasingRecursionEnumeratedArgument with the recursive helper's parameter
-- aliased (`draw q = r in ...`), the AliasIntro rewrite at the helper's site.
-- The original answers p(7) = 1.0, and so does the same alias on a
-- non-recursive helper (`loop r = draw q = r in if q < 1 then 0 else 7`).
-- Verified at 8924628 on dev. Docs task
-- alias-of-recursive-helper-parameter-refuses-with-random-argument.
expect-failure: refused "has no inference rule for its arguments the if-then-else (random)"
p(7)=(1.0, 0.0)
