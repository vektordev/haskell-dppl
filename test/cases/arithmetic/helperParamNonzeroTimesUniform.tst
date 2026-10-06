-- The nonzero arm of the run-time zero-factor branch keeps the ordinary
-- inversion (task helper-parameter-zero-factor-answers-nan).
backends: interpreter, julia, python, batched
p(1.0)=(0.5, 1.0)
p(3.0) is impossible
cdf(1.0)=(0.5, 0.0)
cdf(3.0)=(1.0, 0.0)
