-- The cumulative query of a neural read with a continuous leaf is refused:
-- the read's CDF is computed by summing its point masses over its enumerated
-- domain, and a (Int, Float) read has none. Before task
-- neural-int-read-cdf-returns-pmf it silently returned the point
-- probability/density instead. Idealized: the heads are independent, so
-- cdf((i, x)) = P(I <= i) * P(F <= x), the Float head's normal CDF. Docs task
-- neural-read-cdf-continuous-leaf-refused.
expect-failure: refused "cumulative distribution of the neural read"
