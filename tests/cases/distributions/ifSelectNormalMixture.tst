-- The probabilistic-condition sibling of ifSelectNormalDet: an even mixture of
-- N(1, 1) and N(0, 2), which is not itself Gaussian (ModalityInfer types it
-- Integrate, deliberately dropping the family) and is measured arm by arm.
backends: interpreter, julia, python, batched
p(0.5)=(0.2726997, 1.0, False)
p(1.0)=(0.2874875, 1.0, False)
cdf(1.0)=(0.5957312, 0.0)
cdf(20.0)=(1.0, 0.0)
