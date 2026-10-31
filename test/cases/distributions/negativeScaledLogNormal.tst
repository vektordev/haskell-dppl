-- Task lognormal-family-kept-through-nonpositive-scale-mult: a log-normal
-- times a negative constant kept the PLogNormal family, so the density and
-- cdf were read off a log-normal supported on the positives and answered 0
-- everywhere on the negatives. Y = -2 X, X ~ LogNormal(0, 1):
-- p(-2) = phi(0) / 2, cdf(-2) = P(X >= 1) = 0.5.
p(-2.0)=(0.19947114020071635, 1.0)
p(2.0) is impossible
cdf(-2.0)=(0.5, 0.0)
