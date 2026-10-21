p((ANY, 1.0))=(1.0, 0.0, False)
cdf((ANY, 2.0))=(1.0, 0.0)
cdf((ANY, 0.5))=(0.0, 0.0)
-- A function in a component of a deterministic result: a wildcard query
-- slot over it bounds nothing, so the cdf is the other component's. A
-- concrete closure there would be a run-time refusal (no cdf is defined over
-- a function); before task function-value-compared-in-probability-mode the
-- integrate compile died on compareValueExpr's arrow invariant.
