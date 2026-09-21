-- Same defect as curriedTupleBodyBothProbabilistic, mirrored -- x is deterministic (bound
-- to 1.0), y is probabilistic. Querying x=9.0 should idealized-ly be
-- impossible, but the x=1.0 indicator is silently dropped. The row below
-- pins the currently-wrong value.
expect-failure: wrong-result
p((9.0, 0.0))=(0.39894228, 1.0)
