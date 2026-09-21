-- Found by the let/set-witness fuzz generator (~2% of its crashes): both arms of the `if` are the syntactically identical tuple
-- `(False, left 0)`, so `snd` always yields `left 0` regardless of the
-- random condition -- the observation should never need to be inverted
-- through the condition's `or` at all. Idealized: p(Left 0) = (1.0, 0).
expect-failure: diagnostic "InjF 'or' has 0 inversions solving for"
