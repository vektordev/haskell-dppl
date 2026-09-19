-- Row 3: the callee is a lambda literal passed as an argument. Same N(1, 1) as
-- the named-function control; this is the shape investigation
-- modality-function-space-test-coverage found panicking in toIRNormalParams.
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
