-- Row 6: the callee is chosen by a *deterministic* if. The else arm carries
-- weight zero, so the answer is the then arm's N(1, 1) -- but the else arm is
-- still compiled, which is what used to crash.
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
