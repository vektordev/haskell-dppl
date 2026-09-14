-- Row 8, the most serious of the four: a *probabilistic* function value. The
-- if picks a lambda at random and the result is applied to a deterministic
-- argument, so the value is 4.0 or 6.0 with equal mass. Before callee
-- normalisation this type-checked and compiled, then died at run time
-- multiplying the 0.5 branch weight by a VClosure.
backends: interpreter, julia, python, batched
p(4.0)=(0.5, 0.0, False)
p(6.0)=(0.5, 0.0, False)
p(5.0) is impossible
cdf(3.0)=(0.0, 0.0)
cdf(4.0)=(0.5, 0.0)
cdf(5.0)=(0.5, 0.0)
cdf(6.0)=(1.0, 0.0)
