-- The materializer's canary (task materialize-discrete-marginals), one level
-- deeper than letThreadEnumerable: the LEFT OPERAND of the outer ++ is itself
-- an enumerable chain, and its two operands share the enumerated latent u.
-- Correct (u counted once): the inner sum is 0.7 at 0 and 0.3 at 2, so with
-- w ~ Bernoulli(0.5) the whole chain is 0.35, 0.35, 0.15, 0.15.
-- A materializer that tabulated the inner sum by convolving two independent
-- marginals would get 0.49/0.42/0.09 inside and 0.245/0.455/0.255/0.045 here.
p(0)=(0.35, 0.0)
p(1)=(0.35, 0.0)
p(2)=(0.15, 0.0)
p(3)=(0.15, 0.0)
cdf(1)=(0.7, 0.0)
cdf(3)=(1.0, 0.0)
