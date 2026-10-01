-- A recursive helper applied straight to a neural read, `sevens (readDigits
-- sym)`. The 16105-value `of` domain is over the default materialization
-- budget, so the dense route declines, and the plan-guided route is not
-- entered: the read is a call argument rather than a draw binding. The compile
-- falls through to set-valued witness construction and dies. Draw-binding the
-- read, `draw ds = readDigits sym in sevens ds`, compiles and is exact; the
-- two spellings mean the same thing. Under budget (depth 2) both compile.
-- The pairwise twin is planPairwiseReadsAsHelperArgs.
-- Task: plan-engine-not-entered-for-inline-neural-read.
expect-failure: diagnostic "set-valued witness construction failed"
