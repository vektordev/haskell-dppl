-- A curried function-valued result: two arrows past the spine, two eta
-- binders. At (1, 2, 3) both arms give 6; at (2, 2, 3) they give 7 and 12.
-- Task arrow-result-main-entry-points.
p(6.0, 1.0, 2.0, 3.0)=(1.0, 0)
p(7.0, 2.0, 2.0, 3.0)=(0.5, 0)
p(12.0, 2.0, 2.0, 3.0)=(0.5, 0)
cdf(10.0, 2.0, 2.0, 3.0)=(0.5, 0)
