-- The let-bound sibling of arrowApplyRandomFunction: the same probabilistic
-- function value, but selected behind a `let` rather than directly in callee
-- position, so CalleeNormalize's if-distribution rule never touches it (it
-- deliberately leaves a bare name in callee position alone). This is the
-- shape task arrow-lifted-mixture-for-function-values exists for: the
-- mixture is lifted pointwise by IRCompiler's IfThenElse equation instead of
-- being resolved away syntactically before annotation.
backends: interpreter, julia, python
p(4.0)=(0.5, 0.0, False)
p(6.0)=(0.5, 0.0, False)
p(5.0) is impossible
cdf(3.0)=(0.0, 0.0)
cdf(4.0)=(0.5, 0.0)
cdf(5.0)=(0.5, 0.0)
cdf(6.0)=(1.0, 0.0)
