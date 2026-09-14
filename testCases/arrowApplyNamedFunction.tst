-- Row 1 of investigation modality-function-space-test-coverage's probe table:
-- the shape that always worked, kept as the control the four broken ones are
-- one syntactic step away from. f Normal ~ N(1, 1).
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
