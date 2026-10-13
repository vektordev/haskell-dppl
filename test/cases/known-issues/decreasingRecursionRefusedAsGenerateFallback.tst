-- requireDeterministicUnderEnum refuses any call to a generate function on a
-- call cycle inside an enumerated branch. Here the recursive call has a
-- decreasing argument (loop (r - 1)) and sits behind `if False`, so the
-- refusal's own advice ("rewrite the recursion so it has a decreasing
-- argument") does not apply. Both enumerated arguments (1 and 2) take the
-- final else branch, so main is a standard Normal. Idealized:
-- p(0.5) = (0.3520653267642995, dim 1). Admission-oracle family 7 of
-- fuzz-admission-over-promises; ticket
-- decreasing-recursion-refused-as-generate-fallback.
expect-failure: refused "reached a generate-backed fallback"
