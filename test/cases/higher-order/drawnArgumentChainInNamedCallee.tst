-- A drawn argument passed to a named callee that draws a chain from it,
-- queried for the marginal over the chain's last step: phi(0) phi(0.5) =
-- 0.140454 at dim 2. The witness chain of s1 (sample[0]) held steps toward
-- other occurrences, and the wildcard test over them read the ANY slot, so
-- s1 took the unevaluable-witness route (the open body) and lost its own
-- density: 0.352065 at dim 1. Refused before task
-- named-callee-binding-not-floored, wrong after it (814c061); the
-- helper-extract rewrite of let-bindings/aliasedChainStepMarginalTail found
-- it. Task aliased-parameter-plus-zero-marginal-loses-dim.
p((0.0, (0.5, ANY)))=(0.1404537443096252, 2.0)
p((0.0, (0.5, 1.0)))=(0.04944889338563758, 3.0)
p((0.0, (ANY, ANY)))=(0.3989422804014327, 1.0)
