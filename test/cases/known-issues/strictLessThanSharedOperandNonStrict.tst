-- `x < y` between two enumerated Ints is evaluated as `x <= y` once `y` is
-- also read by a sibling operand of the `&&` (here `y < 5`). Idealized:
-- p(True) = P(x = 0, y = 1) = 0.25, p(False) = 0.75. All three backends
-- answer the swapped values pinned below, i.e. P(x <= y). Sharing the left
-- operand instead, `(x < y) && (x < 5)`, is right. Found by experiments_nest
-- program-guided-diffusion (its chained-`<` constraint programs failed an
-- exactness check); docs task strict-int-less-than-non-strict-when-operand-shared.
backends: interpreter, python, batched
expect-failure: wrong-result
p(True)=(0.75, 0.0)
p(False)=(0.25, 0.0)
