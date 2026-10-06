-- A parameter zero factor of a non-Gaussian product: the point mass at 0, not
-- the inversion through a division by it, which found every value impossible
-- (task helper-parameter-zero-factor-answers-nan, IRCompiler.runtimeZeroFactor).
backends: interpreter, julia, python, batched
p(0.0)=(1.0, 0.0)
p(0.5) is impossible
cdf(0.0)=(1.0, 0.0)
cdf(-0.5)=(0.0, 0.0)
