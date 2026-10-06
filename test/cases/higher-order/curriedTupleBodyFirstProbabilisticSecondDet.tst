-- curriedTupleBodyBothProbabilistic with the last-applied argument
-- deterministic (y bound to 1.0); the y = 1.0 indicator is kept. Formerly a
-- known-issues wrong-result pin (the indicator was dropped, so y = 9.0
-- answered x's density unguarded).
p((0.0, 9.0)) is impossible
p((0.0, 1.0))=(0.39894228, 1.0)
