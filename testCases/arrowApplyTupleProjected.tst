-- Row 4: the callee is a lambda projected out of a let-bound tuple. Callee
-- normalisation reduces `fst p` to the lambda it denotes, leaving the (now
-- dead) binding behind; the answer is the control's N(1, 1).
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
