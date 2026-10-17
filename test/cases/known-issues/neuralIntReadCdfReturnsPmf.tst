-- The cumulative query of a neural Int read returns the point mass: the
-- emitted integrate calls the read's forward. cdf(2) answers 0.3 where
-- P(X <= 2) = 0.6. Same for (digit a, digit a) and digit a ++ 0; Bool reads,
-- Float heads and sums of two reads are right. Verified at b16b4d9 on dev.
-- Docs task neural-int-read-cdf-returns-pmf.
expect-failure: broken
cdf(2, (2, [0.1, 0.2, 0.3, 0.4]))=(0.6, 0.0)
