-- The helper-extraction rewrite of arithmetic/drawBoundZeroTimesNormal: inside
-- h the zero is a parameter, so the Gaussian's scale |z| vanishes only at run
-- time, where the product is the point mass at 0 (was NaN at dim 1; task
-- helper-parameter-zero-factor-answers-nan, IRCompiler.degenerateScaleGuard).
backends: interpreter, julia, python, batched
p(0.0)=(1.0, 0.0)
p(0.5) is impossible
cdf(0.0)=(1.0, 0.0)
cdf(-0.5)=(0.0, 0.0)
