-- A run-time zero scale under an affine shift: the point mass at 1 (task
-- helper-parameter-zero-factor-answers-nan).
backends: interpreter, julia, python, batched
p(1.0)=(1.0, 0.0)
p(0.5) is impossible
cdf(1.0)=(1.0, 0.0)
cdf(0.5)=(0.0, 0.0)
