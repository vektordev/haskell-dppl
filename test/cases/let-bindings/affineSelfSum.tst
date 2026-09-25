p(0.5)=(0.19333405840142465, 1.0, False)
p(0.0)=(0.19947114020071635, 1.0, False)
cdf(0.5)=(0.5987063256829237, 0.0)
-- A shared latent read twice: 2x is N(0, 2), not the N(0, sqrt 2) that
-- substituting x at each use would answer. Design affine-gaussian-forms
-- section 4 names this as the case against a single-use rewrite.
