p([(0.0, ANY), (0.0, 0)])=(0.0119366, 2.0)
p([(0.0, 0), (0.0, 0)])=(0.000795775, 2.0)
p([(0.0, 1), (0.0, 0)])=(0.0111408, 2.0)
p([(0.0, ANY), (0.0, ANY)])=(0.0198944, 2.0)
p([(0.0, ANY), (0.0, 1), (0.0, ANY)])=(0.00158734, 3.0)
p([(0.0, ANY)])=(0.0997356, 1.0)
-- An ANY mark of a drawn event whose mark is the recursive call's state
-- argument. The query's ANY used to be passed as `prev` itself
-- (`gen.forward(sample[1:], e_[1])`), so every `prev == 0` test was False and
-- the next step always took the prev = 1 arm: p([(0.0, ANY), (0.0, 0)])
-- answered 0.013926 (= 0.125 phi(0)^2 0.7). The binding now sums the ANY leaf
-- over its domain {0, 1}: 0.000795775 + 0.0111408. Found by the
-- publication-exploration C4 pilot (missing marks in a marked point
-- process). Task any-mark-passed-as-recursive-call-state.
