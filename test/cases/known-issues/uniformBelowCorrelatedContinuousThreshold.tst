-- A comparison against a continuous random threshold that the result also
-- reads: `Uniform < x` with x returned in the first slot. No equation
-- measures the correlated pair, so the probability and integrate variants
-- are refused. Before task uniform-below-random-threshold-no-forward the
-- refusal was silent (exit 0, no reason). Since task
-- engine-applicability-as-data the binding of x is refused first: the
-- set-witness walk meets the comparison against the fresh Uniform, no other
-- engine applies, and x is bound sample-only. Idealized:
-- p((True, True)) = integral_0^0.5 x dx = 0.125,
-- p((False, True)) = integral_0.5^1 x dx = 0.375.
slow
expect-failure: refused "no inference engine applies to the binding of 'x'"
