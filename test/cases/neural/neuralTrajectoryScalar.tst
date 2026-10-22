-- The scalar diffusion trajectory of task tensor-gaussian-heads-rd-diffusion.
-- The recursive call's parameter is witnessed by the head of the list it
-- returns, but the call sits in the else arm of an if: ModalityInfer used to
-- seed the witness question at the declaration root only, so the inner
-- `mu (x, t)` read an unwitnessed input and the whole trajectory was Bottom.
-- The shaped-input mock reads (mu, sigma) off the input: prior 0.0 is N(0, 1),
-- mu (x, t) is N(x, t). So p = N(x0; 0, 1) N(x1; x0, 2) N(x2; x1, 1).
p([0.0, 0.0, 0.0])=(0.03174682, 3.0)
p([0.5, 1.0, 0.2])=(0.01971821, 3.0)
p([-1.0, 0.5, 1.5])=(0.00881577, 3.0)
p([0.0, 0.0]) is impossible
