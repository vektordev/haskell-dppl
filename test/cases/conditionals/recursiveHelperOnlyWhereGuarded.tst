-- cnt terminates only on a non-negative whole number, and main calls it only
-- where x is one. Batched: an eager torch.where arm would also call it at
-- x = -1 and never return, so the branch guarding the call is split.
batched
p(0.5, -1.0)=(0.3520653, 1.0)
p(0.5, 2.0)=(0.1295176, 1.0)
p(3.0, 3.0)=(0.3989423, 1.0)
cdf(0.0, -1.0)=(0.5, 0.0)
cdf(2.0, 2.0)=(0.5, 0.0)
