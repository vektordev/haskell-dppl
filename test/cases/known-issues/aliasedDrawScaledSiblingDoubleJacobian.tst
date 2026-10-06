-- Verified at 50aeb1a (plus the named-function-list-head-witness-not-recovered
-- change, which does not touch it; also wrong at 7c70723): re-binding a
-- witnessed draw through an alias, next to a scaled fresh draw in a sibling
-- field, applies that sibling's change of variables twice. The unaliased
-- spelling `draw x0 = Normal in (x0, 0.5 * Normal)` answers correctly.
-- Idealized: p((0.0, 0.0)) = phi(0) * 2 phi(0) = (0.31830989, 2); the
-- compiler answers 0.63661977. Found by the rewrite-invariance sweep over
-- distributions/ouChainUnrolled (TestRewrites.knownDivergences). Docs task
-- aliased-draw-scaled-sibling-double-jacobian.
expect-failure: broken
p((0.0, 0.0))=(0.31830989, 2.0)
p((1.0, 0.5))=(0.11709966, 2.0)
