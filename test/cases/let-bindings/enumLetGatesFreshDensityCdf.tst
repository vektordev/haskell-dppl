backends: interpreter, julia, python, batched
cdf(0.0)=(0.25067, 0.0)
cdf(3.0)=(0.74933, 0.0)
cdf(1.5)=(0.5, 0.0)
-- An enumerated latent selecting between two fresh Normals. Given `b` the
-- body is a continuous draw, handed to the ordinary rules (task
-- enum-let-latent-gates-fresh-draw); a CDF value is a mass, so the enclosing
-- enumerated sum is exact: cdf(0) = 0.5*Phi(0) + 0.5*Phi(-3). The point
-- density of the same program is a known issue
-- (known-issues/enumLetGatesFreshDensity).
