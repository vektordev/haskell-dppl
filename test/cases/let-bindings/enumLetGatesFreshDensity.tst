p(0.0)=(0.2017, 1.0)
p(3.0)=(0.2017, 1.0)
p(1.5)=(0.12952, 1.0)
-- The continuous sibling of test/cases/let-bindings/enumLetGatesFreshDraw*:
-- given the enumerated latent `b` the body is a fresh Normal, i.e. a density.
-- The enumerated sum keeps its terms' dims (task
-- enumerated-sum-over-density-body; until then it reported every sum as a
-- mass and a run-time guard raised "met a continuous density" instead), so
-- the answer is the mixture of N(0,1) and N(3,1): 0.5*phi(x) + 0.5*phi(x-3)
-- at dim 1. Its CDF is let-bindings/enumLetGatesFreshDensityCdf.
