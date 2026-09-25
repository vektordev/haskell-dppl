expect-failure: broken
p(0.0)=(0.2017, 1.0)
p(3.0)=(0.2017, 1.0)
-- The continuous sibling of test/cases/let-bindings/enumLetGatesFreshDraw*:
-- given the enumerated latent `b` the body is a fresh Normal, i.e. a density,
-- but every enumerated sum ('enumSumP') reports a mass (dim 0), which was
-- harmless only while enumerated bodies were always forward-and-compare
-- indicators. Task enum-let-latent-gates-fresh-draw therefore guards the
-- delegated body at RUN time: a point query here raises ("met a continuous
-- density") rather than answering with the wrong dim. The rows are the
-- idealized mixture of N(0,1) and N(3,1): 0.5*phi(0) + 0.5*phi(3) at dim 1.
-- The CDF of the same program does answer, and is pinned by
-- test/cases/let-bindings/enumLetGatesFreshDensityCdf. Follow-up task
-- enumerated-sum-over-density-body.
