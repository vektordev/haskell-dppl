-- The if-flip of `if Normal == 0.5 then 1 else 2`, which answers p(1) with
-- the density convention of sampling-matches-pdf-continuous-equality-density
-- (0.3521, dim 1). Under `not` the same event answers impossible. Verified at
-- 3b72682 on dev, interpreter. Found by the rewrite-invariance net's if-flip
-- family over either-maybe/observeContinuousEqualsLetfree
-- (TestRewrites.knownDivergences). Docs task
-- null-set-conventions-not-preserved-under-negation. The idealized row is
-- the un-negated spelling's answer; whether the convention should hold at
-- all is that task's decision.
backends: interpreter, python
expect-failure: broken
p(1)=(0.3520653267642995, 1.0)
