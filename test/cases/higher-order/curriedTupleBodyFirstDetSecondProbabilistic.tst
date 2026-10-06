-- curriedTupleBodyBothProbabilistic mirrored: x is deterministic (bound to
-- 1.0), y is probabilistic, and the x = 1.0 indicator is kept. Formerly a
-- known-issues wrong-result pin (the indicator was dropped, so x = 9.0
-- answered phi(0) at dim 1).
p((9.0, 0.0)) is impossible
p((1.0, 0.0))=(0.39894228, 1.0)
