-- The CDF of a tuple-valued neural read: the sum of the read's point masses
-- over the enumerated pairs at or below the query in both components, i.e.
-- P(X <= 0) * P(Y <= 1) = 0.25 * 0.8 for independent heads. A masked (ANY)
-- component bounds nothing. Docs task neural-int-read-cdf-returns-pmf.
cdf((0, 1), (2, [0.25, 0.75, 0.5, 0.3, 0.2]))=(0.2, 0.0)
cdf((1, 0), (2, [0.25, 0.75, 0.5, 0.3, 0.2]))=(0.5, 0.0)
cdf((ANY, 1), (2, [0.25, 0.75, 0.5, 0.3, 0.2]))=(0.8, 0.0)
cdf((0, ANY), (2, [0.25, 0.75, 0.5, 0.3, 0.2]))=(0.25, 0.0)
p((0, 1), (2, [0.25, 0.75, 0.5, 0.3, 0.2]))=(0.075, 0.0)
