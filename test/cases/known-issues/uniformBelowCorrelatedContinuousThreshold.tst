-- A comparison against a continuous random threshold that the result also
-- reads: `Uniform < x` with x returned in the first slot. No equation
-- measures the correlated pair, so the probability and integrate variants
-- are refused. Before task uniform-below-random-threshold-no-forward the
-- refusal was silent (exit 0, no reason). Idealized:
-- p((True, True)) = integral_0^0.5 x dx = 0.125,
-- p((False, True)) = integral_0.5^1 x dx = 0.375.
expect-failure: refused "has no closed form for its two random operands"
