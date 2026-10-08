-- topK operand-order canary (task
-- transformation-differential-testing-m1-config-differencing; tracked by
-- topk-prunes-on-left-operand-marginal-only). Three Bernoulli(0.3) bits
-- summed left-nested. Exact values are Binomial(3, 0.3). Under topK the
-- outer + guards each enumerated term on accProb * p(x + y = e), and at
-- threshold 0.1 p(x + y = 2) = 0.09 is below the cutoff, so p(3) prunes to 0.
-- The commuted spelling z + (x + y) guards on p(z = 1) = 0.3 instead and keeps
-- 0.027. Corpus.TopKOperandOrder (Slow) requires that divergence to be seen
-- here, so a fix to the pruning rule shows up as a stale entry.
backends: interpreter, julia, python, batched
p(0)=(0.343, 0.0)
p(1)=(0.441, 0.0)
p(2)=(0.189, 0.0)
p(3)=(0.027, 0.0)
p(4) is impossible
