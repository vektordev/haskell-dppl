-- Task lognormal-family-kept-through-nonpositive-scale-mult, the runtime-sign
-- twin: the scale is a parameter, unknown when h is compiled, so the
-- log-normal family is not kept and the generic inversion through mult
-- answers. Y = -X, X ~ LogNormal(0, 1): p(-2) = phi(log 2) / 2,
-- cdf(-2) = P(X >= 2) = 1 - Phi(log 2).
p(-2.0)=(0.1568740192789811, 1.0)
p(2.0) is impossible
cdf(-2.0)=(0.24410859578558275, 0.0)
