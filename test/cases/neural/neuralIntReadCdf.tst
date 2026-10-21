-- The CDF of a neural Int read sums the read's point masses over its domain
-- up to the query: P(X <= 2) = 0.1 + 0.2 + 0.3. It used to return the point
-- mass P(X = 2) = 0.3 (docs task neural-int-read-cdf-returns-pmf). Below the
-- domain the mass is 0, at or above its top 1.
cdf(2, (2, [0.1, 0.2, 0.3, 0.4]))=(0.6, 0.0)
cdf(0, (2, [0.1, 0.2, 0.3, 0.4]))=(0.1, 0.0)
cdf(-1, (2, [0.1, 0.2, 0.3, 0.4]))=(0.0, 0.0)
cdf(3, (2, [0.1, 0.2, 0.3, 0.4]))=(1.0, 0.0)
cdf(7, (2, [0.1, 0.2, 0.3, 0.4]))=(1.0, 0.0)
p(2, (2, [0.1, 0.2, 0.3, 0.4]))=(0.3, 0.0)
