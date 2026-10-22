-- Milestone M2 of design diffusion-models-wishlist, spelled as the design
-- wrote it: a toy 1-D diffusion whose initial state is a primitive Normal
-- draw (neural/neuralTrajectoryScalar starts from a network read instead)
-- and whose reverse kernel is a Gaussian-head network of (x_t, t). Every
-- state is in the output list, so mu's input is witnessed at each step and
-- the trajectory density is a product of closed-form Gaussians. The
-- shaped-input mock reads (mu, sigma) off the input, so mu (x, t) is N(x, t):
-- p = N(x0; 0, 1) N(x1; x0, 2) N(x2; x1, 1), a density of dimension 3.
-- The marginal of the final state alone is refused (Rejection.TensorTypes,
-- "the marginal of a scalar diffusion's final state is sample-only").
p([0.0, 0.0, 0.0])=(0.03174682, 3.0)
p([1.0, 0.0, -0.5])=(0.01499613, 3.0)
p([-0.5, -2.0, -1.0])=(0.01282687, 3.0)
p([2.0, 1.0, 1.5])=(0.00334609, 3.0)
p([0.0, 0.0]) is impossible
p([0.0, 0.0, 0.0, 0.0]) is impossible
