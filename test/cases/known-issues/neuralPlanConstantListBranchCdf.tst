-- A neural (plan-enumerated) program with a constant-list arm, asked for its
-- cdf. The plan traversal tests a deterministic arm against a cumulative
-- target with `planDetGuard`'s `not (val > sample)` (IRCompiler.hs), which
-- only means `val <= sample` for a scalar; for a list it is an `OpGreaterThan`
-- on two lists. The interpreter's list `>` is False whenever both lists are
-- non-empty (its `[] > []` base case is False and the step is a conjunction),
-- so the arm counts its full mass at every query (0.514424 and 0.654269 on
-- the rows below). Python's
-- `InferenceList.__gt__` recurses into `EmptyInferenceList.value` (None) once
-- every head compares greater, raising `TypeError: '>' not supported between
-- instances of 'NoneType' and 'NoneType'` -- the disagreement
-- prop_Fuzz_BackendsAgree found. Both backends are wrong, so both are pinned.
-- Idealized: x ~ N(0,1), so each arm has mass 0.5; [0.0] is not <= the query
-- under either the componentwise order or the equality indicator the
-- non-neural path (compareValueExpr) uses, so only [Normal] contributes:
-- 0.5 * Phi(q). The interpreter currently gives 0.5 + 0.5 * Phi(q).
-- Task plan-det-guard-compares-composite-values-with-greater-than.
expect-failure: broken
backends: interpreter, python
cdf([-1.898], (2, [0.0, 1.0]))=(0.014424, 0.0)
cdf([-0.5], (2, [0.0, 1.0]))=(0.154269, 0.0)
