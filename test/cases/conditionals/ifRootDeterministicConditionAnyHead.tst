-- An ANY in the witnessing slot of an if-rooted program with a deterministic
-- condition (docs task if-root-deterministic-condition-any-marginal-refused).
-- The condition reads no latent, so each arm is an observation tree of its own
-- (ObservationMask.observationArms) and the masks range over the union of the
-- arms' enumerated slots, head and tail.head. The condition is false, so the
-- value is x : [x], and p([ANY, a]) = phi(a) at dimension 1, as on the if-free
-- spelling draw x = Normal in x : [x].
p([ANY, 0.5])=(0.35206533, 1.0)
p([ANY, 0.0])=(0.39894228, 1.0)
p([0.5, ANY])=(0.35206533, 1.0)
p([ANY, ANY])=(1.0, 0.0)
p([ANY]) is impossible
p([ANY, 0.5, 0.1]) is impossible
