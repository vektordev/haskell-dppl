-- Two constructors of one ADT declare the SAME field names (`A l,r` and
-- `B l,r`). The compiler emits exactly one accessor `l`, hard-bound to `A`
-- (the first constructor declaring it), so evaluating a `B`-rooted sample in
-- probability mode calls `A`'s accessor on it and crashes at query time.
-- `compile` itself succeeds (the crash is inside `generate`/`forward` while
-- scoring a specific sample), so this is pinned as `broken` rather than
-- `diagnostic`/`crash`. Idealized value, by symmetry with the identical `A L
-- L` query (which succeeds and answers 0.072): p(B L L) = 0.072, dim 0.
expect-failure: broken
p(B L L)=(0.072, 0.0)
