-- Over-determined observation: slots 2 and 3 both recover the same latent y,
-- so the support is the manifold c == b - 1. The redundant recovery path is
-- dropped by forward chaining (both routes are semantically equal) and the
-- manifold constraint is carried by the deterministic-slot consistency
-- indicator instead -- a dim-0 factor, so the result stays dim 2.
-- Regression for task multi-path-recovery-unmaterialized-crash: this used to
-- die at run time with "Variable ast14 not declared".
backends: interpreter, julia, python, batched
p((0.3, (3.7, 2.7)))=(1.0, 2.0, False)
p((0.8, (4.0, 3.0)))=(1.0, 2.0, False)
p((0.3, (3.7, 2.6))) is impossible
p((0.3, (5.0, 4.0))) is impossible
p((1.5, (5.2, 4.2))) is impossible
