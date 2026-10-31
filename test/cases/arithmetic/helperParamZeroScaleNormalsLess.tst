-- Two Normals scaled by the same runtime zero: both sides are the point 0, so
-- 0 < 0 is False. The difference's scale hypot(0, 0) vanished inside the
-- closed-form Gaussian-difference CDF and the runtime read Phi(0/0) as 0.5
-- (task two-normal-comparison-zero-scale-wrong, Gaussian.normalDiffComparison).
p(True)=(0.0, 0.0)
p(False)=(1.0, 0.0)
