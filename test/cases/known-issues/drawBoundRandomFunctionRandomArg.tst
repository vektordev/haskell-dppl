-- The draw-bound spelling of higher-order/arrowApplyRandomFunctionNormalArg:
-- one randomly selected function applied to a random argument. The lifted
-- mixture (task arrow-lifted-mixture-for-function-values) answers the
-- deterministic-argument twin (arrowApplyLetBoundRandomFunction), but a random
-- argument has to be inverted through each arm's lambda, which forward
-- chaining cannot reach through the selection. The probability variant is
-- refused by name; before, it was stopped only by the central generate-backed
-- guard. Idealized: the mixture 0.5 N(1, 1) + 0.5 N(0, 2), as the inline
-- twin. Docs-repo task draw-bound-random-function-random-argument-refused.
expect-failure: refused "a randomly selected function value bound to"
p(0.5)=(0.2726997, 1.0, False)
p(2.0)=(0.1814780, 1.0, False)
cdf(1.0)=(0.5957312, 0.0)
