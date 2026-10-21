-- An ANY in the witnessing slot of an if-rooted program with a deterministic
-- condition. The condition is false, so the value is x : [x], and the marginal
-- p([ANY, a]) is phi(a) at dimension 1. The same body without the if
-- (draw x = Normal in x : [x]) answers it through its (ANY, _) mask variant.
-- Here the observation tree stops at the if root (ObservationMask.buildObs),
-- so main has one self-contained <root> slot and no mask variants. The point
-- witness is read from the head, which is ANY, and the binding is read twice,
-- so the query ends in the runtime error "cannot compute marginal: binding 'x'
-- is unobserved (ANY in its witnessing slot)". Docs task
-- if-root-deterministic-condition-any-marginal-refused.
expect-failure: broken
p([ANY, 0.5])=(0.35206533, 1.0)
p([ANY, 0.0])=(0.39894228, 1.0)
