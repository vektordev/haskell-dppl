-- A callee selected via a user-ADT field accessor
-- (`a k`, extracting the closure field of a literal `Add` constructor) is not
-- reduced to its lambda body by CalleeNormalize, so the whole VADT is applied
-- instead of the extracted closure. `compile` itself succeeds (the crash is
-- at query time), so this is pinned as `broken` rather than
-- `diagnostic`/`crash`. Idealized (inferred, not doc-stated): `a` extracts
-- `\x -> x + 1.0`, applied to 3.0 gives 4.0 deterministically.
expect-failure: broken
p(4.0)=(1.0, 0.0)
