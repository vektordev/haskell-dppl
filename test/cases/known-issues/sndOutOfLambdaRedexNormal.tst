-- A tuple projection whose operand is a literal lambda redex. `main` is
-- admitted PNormal, but the Gaussian catch-all hands the whole `snd (...)` to
-- toIRNormalParams, which cannot see through the unreduced application.
-- Idealized: main is a standard Normal, p(0.0) = (0.3989422804014327, dim 1).
-- Admission-oracle family 6 of fuzz-admission-over-promises; ticket
-- snd-out-of-lambda-redex-normal-params.
expect-failure: refused "cannot extract Normal params"
