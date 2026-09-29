-- A let-bound continuous latent compared with `==` twice (task
-- sampling-matches-pdf-continuous-equality-density; the program its review
-- asked to pin, less the `observe`). The False outcome of `x == 0.0` is the
-- complement of a point, a WSet `WExcept`; it used to travel as a `WPoint`
-- holding the VAnyExcept sentinel, and the second comparison's
-- intersection applied `OpEq`/`OpSub` to it (forceOp panic at -O2, an
-- interpreter type error at -O0). Each True outcome is the Normal's density
-- at its point (dim 1 -- the density convention for a point observation);
-- removing a point from a continuous set leaves its mass whole (a mass minus
-- a density is the mass), so p(2) = 1.0 at dim 0. p(0)/p(1) is the likelihood
-- ratio N(0)/N(1) the review wanted to see.
p(0)=(0.3989422804014327, 1.0)
p(1)=(0.24197072451914337, 1.0)
p(2)=(1.0, 0.0)
p(3) is impossible
