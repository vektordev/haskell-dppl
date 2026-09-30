-- Probe row 10 of design law-carrying-modality's evidence table, the
-- rewritten half. Its working twin `main = 0.0 * Normal` answers
-- p(0.0) = (1.0, dim 0). Verified at 2d50350 on dev: this answers (NaN, dim 1),
-- a wrong result. Pinned as `broken` rather than `wrong-result` because
-- TestKnownIssues does not evaluate `wrong-result` rows, and this one should
-- report itself fixed. Task let-bound-zero-factor-loses-dirac-mass; pinned by
-- task rewrite-invariance-net-draw-apply-helper-alias.
expect-failure: broken
p(0.0)=(1.0, 0.0)
