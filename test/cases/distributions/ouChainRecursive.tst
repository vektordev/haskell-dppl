-- Milestone M0 of design diffusion-models-wishlist as the design wrote it: the
-- same AR(1)/Ornstein-Uhlenbeck trajectory as distributions/ouChainUnrolled,
-- built by recursion. Every latent is still a point witness in the output list,
-- so the values are identical to the unrolled form's. The witness of step's
-- parameter is recovered through the if-then-else on t, which is deterministic
-- at every call: each arm is inverted on its own and the condition selects
-- (task witness-through-deterministic-if-over-list-arms). A list of the wrong
-- length is impossible.
slow
p([0.0, 0.0, 0.0])=(0.25397454, 3.0)
p([0.5, 0.2, -0.1])=(0.16909049, 3.0)
p([1.0, 0.9, 0.81])=(0.15404335, 3.0)
p([1.0, 0.9]) is impossible
p([1.0, 0.9, 0.81, 0.5]) is impossible
