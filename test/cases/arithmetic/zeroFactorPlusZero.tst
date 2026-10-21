-- `draw z = Normal in 0.0 * z` is a point mass at 0 (its law is a Dirac at
-- 0, arithmetic/drawBoundRandomTimesLiteralZero). Adding 0.0 to it is the
-- same point: the sum's law is folded from its operands' known values
-- (ModalityInfer.foldedValue). It answered p(0.0) impossible, the plus
-- inversion measuring the product at `sample - 0.0` with the density
-- machinery. Found by the rewrite-invariance net's injf-identity family
-- (task dirac-law-point-lost-under-plus-or-helper).
batched
p(0.0)=(1.0, 0.0)
p(1.0) is impossible
cdf(-0.5)=(0.0, 0.0)
cdf(0.0)=(1.0, 0.0)
