-- The curried twin of arrowApplyLetBoundRandomFunction: a draw-bound random
-- selection between two-argument functions, one arm itself selecting its
-- inner closure at random. The lifted mixture takes one argument per arrow of
-- the arms' type and opens each arm only once fully applied; opening after
-- the first argument left a closure where a packed result was expected, an
-- ill-typed IR (task arrow-lifted-mixture-for-function-values). Values:
-- 1 + 3 = 4 at 0.5, 3 at 0.25, 1 at 0.25.
p(4.0)=(0.5, 0.0, False)
p(3.0)=(0.25, 0.0, False)
p(1.0)=(0.25, 0.0, False)
p(2.0) is impossible
cdf(1.0)=(0.25, 0.0)
cdf(3.5)=(0.5, 0.0)
cdf(4.0)=(1.0, 0.0)
