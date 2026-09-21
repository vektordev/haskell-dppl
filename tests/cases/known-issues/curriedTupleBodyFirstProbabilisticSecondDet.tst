-- Same defect as curriedTupleBodyBothProbabilistic,
-- with the second (last-applied) argument deterministic. y is bound to 1.0,
-- so querying y=9.0 should idealized-ly be impossible -- but the y=1.0
-- indicator is silently dropped, so the bug returns x's density unguarded.
-- The row below pins the currently-wrong value.
expect-failure: wrong-result
p((0.0, 9.0))=(0.39894228, 1.0)
