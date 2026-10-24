-- A comparison with the literal on the left (`2 > v`), bound by `draw z = ..`
-- and used as an if condition, over an enumerated Int. Answered p(1) = 1.0
-- and p(0) impossible until the fixed-bound comparison equation asked the
-- inclusive CDF for a strict Int `>` (`2 > v` read as P(v <= 2)); fixed with
-- task strict-int-less-than-non-strict-when-operand-shared.
-- Found by the rewrite-invariance sequence property (seed 20261014:
-- compare-swap then draw-intro on either-maybe/observeContinuousEqualsLetfree).
-- Docs task draw-bound-literal-left-comparison-condition-wrong.
p(1)=(0.3, 0.0)
p(0)=(0.7, 0.0)
