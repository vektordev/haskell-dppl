-- `draw z = Normal in 0.0 * z` is a point mass at 0 and answers (1.0, dim 0)
-- since law-carrying-modality M6 (arithmetic/drawBoundRandomTimesLiteralZero).
-- Adding 0.0 to it, or extracting the product into a helper, loses that: this
-- answers p(0.0) impossible. Verified at 3b72682 on dev, interpreter. Found by
-- the rewrite-invariance net's injf-identity and helper-extract families
-- (TestRewrites.knownDivergences). Docs task
-- dirac-law-point-lost-under-plus-or-helper.
backends: interpreter, python
expect-failure: broken
p(0.0)=(1.0, 0.0)
