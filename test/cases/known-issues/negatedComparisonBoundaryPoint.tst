-- `v > 1.0` spelled `not (v <= 1.0)` (the language has no <=). The set-witness
-- engine closes a continuous interval at its bound, so `v > 1.0` answers the
-- density at the boundary point (0.2420, dim 1); this spelling answers
-- impossible there. Measure zero, but the two spellings disagree pointwise.
-- Verified at 3b72682 on dev, interpreter. Found by the rewrite-invariance
-- net's compare-flip family (compare-negate) over
-- either-maybe/observeDisjointTails (TestRewrites.knownDivergences). Docs task
-- null-set-conventions-not-preserved-under-negation. The idealized row is the
-- `v > 1.0` spelling's answer.
backends: interpreter, python
expect-failure: broken
p(Right 1.0)=(0.24197072451914337, 1.0)
