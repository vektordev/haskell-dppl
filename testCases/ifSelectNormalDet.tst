-- A deterministically selected Gaussian. ModalityInfer types this PNormal
-- ("deterministic-tag selection of a Normal keeps the family",
-- TestModalityInfer), and the Normal shortcut then asked toIRNormalParams for
-- an IfThenElse's (mu, sigma) and hit the fallthrough error -- a verdict the
-- rest of the pipeline could not cash. A conditional is a mixture, so it now
-- keeps its own handler; here the else arm's weight is zero and the answer is
-- the then arm's N(1, 1).
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
