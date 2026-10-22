-- The R^d diffusion trajectory of task tensor-gaussian-heads-rd-diffusion at
-- d = 4, T = 3: a tensor-valued Gaussian head (a diagonal Gaussian per step)
-- read along a recursive trajectory whose every state is in the output list,
-- so each network input is witnessed. The initial state is the network
-- `prior` read at a constant: an iid Gaussian tensor with no new surface
-- syntax.
--
-- The plan-aware mock (MockNN.planAwareMockSlots) reads element k's mu off
-- input slot k with sigma s = 1/sqrt(2 pi): prior 0.0 is N(0, s^2 I) and
-- mu (x, t) is N(x, s^2 I). So the density is the closed-form product
-- prod_k prod_i N(x_k,i; x_(k-1),i, s^2) with x_(-1) = 0, i.e.
-- exp(-pi * sum of squared steps), dim 16.
batched
p([[|0.0, 0.0, 0.0, 0.0|], [|0.0, 0.0, 0.0, 0.0|], [|0.0, 0.0, 0.0, 0.0|], [|0.0, 0.0, 0.0, 0.0|]])=(1.0, 16.0)
p([[|0.1, -0.2, 0.3, 0.0|], [|0.4, 0.0, 0.2, -0.1|], [|0.5, 0.3, 0.0, -0.5|], [|0.2, 0.6, -0.4, -0.3|]])=(0.04748484, 16.0)
p([[|0.5, 0.0, 0.0, 0.0|], [|0.5, 0.5, 0.0, 0.0|], [|0.5, 0.5, 0.5, 0.0|], [|0.5, 0.5, 0.5, 0.5|]])=(0.04321392, 16.0)
p([[|0.0, 0.0, 0.0, 0.0|], [|0.0, 0.0, 0.0, 0.0|], [|0.0, 0.0, 0.0, 0.0|]]) is impossible
