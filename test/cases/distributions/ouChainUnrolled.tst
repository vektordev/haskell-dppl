-- Milestone M0 of design diffusion-models-wishlist, in the form that compiles
-- today: a three-state AR(1)/Ornstein-Uhlenbeck trajectory, i.e. a diffusion
-- model with a fixed linear denoiser. Every latent is a point witness in the
-- output list, so p(x0, x1, x2) = N(x0; 0, 1) N(x1; 0.9 x0, 0.5) N(x2; 0.9 x1, 0.5),
-- a density of dimension 3. The recursive spelling of the same chain
-- (known-issues/ouChainRecursive) does not compile yet.
backends: interpreter, julia, python
p([0.0, 0.0, 0.0])=(0.25397454, 3.0)
p([0.5, 0.2, -0.1])=(0.16909049, 3.0)
p([1.0, 0.9, 0.81])=(0.15404335, 3.0)
