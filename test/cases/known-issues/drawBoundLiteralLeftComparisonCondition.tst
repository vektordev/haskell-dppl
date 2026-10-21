-- A comparison with the literal on the left (`2 > v`), bound by `draw z = ..`
-- and used as an if condition, over an enumerated Int. Verified on dev at
-- 5ebe3dc (interpreter): p(1) = 1.0 and p(0) impossible. `v < 2`, the
-- unbound `if 2 > v then ..`, and `(z, v)` as the body all answer 0.3 / 0.7.
-- Found by the rewrite-invariance sequence property (seed 20261014:
-- compare-swap then draw-intro on either-maybe/observeContinuousEqualsLetfree).
-- Docs task draw-bound-literal-left-comparison-condition-wrong.
backends: interpreter, python
expect-failure: broken
p(1)=(0.3, 0.0)
p(0)=(0.7, 0.0)
