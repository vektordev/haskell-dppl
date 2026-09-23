-- Milestone M0 of design diffusion-models-wishlist as the design wrote it: the
-- same AR(1)/Ornstein-Uhlenbeck trajectory as distributions/ouChainUnrolled,
-- built by recursion. Every latent is still a point witness in the output list,
-- so the idealized values are identical to the unrolled form's:
-- p([0.0, 0.0, 0.0]) = (0.25397454, 3), p([0.5, 0.2, -0.1]) = (0.16909049, 3),
-- p([1.0, 0.9, 0.81]) = (0.15404335, 3). Instead probability-mode compilation
-- throws: the random argument of the named function `step` is not recovered
-- from its occurrence at the head of the list. See
-- known-issues/namedFunctionConsWitness for the two-line core.
expect-failure: diagnostic "set-valued witness construction failed"
