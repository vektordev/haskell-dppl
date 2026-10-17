-- An ANY mark of a drawn event whose mark is the recursive call's state
-- argument. The emitted code passes the query's ANY itself as `prev`
-- (`gen.forward(sample[1:], e_[1])`), so every `prev == 0` test is False and
-- the next step always takes the prev = 1 arm: p([(0.0, ANY), (0.0, 0)])
-- answers 0.013926 (= 0.125 phi(0)^2 0.7) instead of summing the mark out.
-- The interpreter and Python agree, and so does --semiring map. Found by the
-- publication-exploration C4 pilot (missing marks in a marked point
-- process). Verified at b16b4d9 on dev. Docs task
-- any-mark-passed-as-recursive-call-state.
-- Idealized: p([(0,0),(0,0)]) + p([(0,1),(0,0)]) = 0.000795775 + 0.0111408.
expect-failure: broken
p([(0.0, ANY), (0.0, 0)])=(0.0119366, 2.0)
