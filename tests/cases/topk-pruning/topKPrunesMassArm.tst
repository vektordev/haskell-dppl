-- Corpus.TopKNeverInflates canary for a mixed-dimension mixture: at 1.0 the
-- exact answer is the then-arm's mass (dim 0 wins the mixture), but at
-- threshold 0.1 that arm is pruned and the pruned program answers the else
-- arm's density (0.95, dim 1). A mass and a density are not comparable, so the
-- property only compares values at equal dim and otherwise requires the pruned
-- dim to be the higher one (pruning removes alternatives, and the lowest dim
-- wins, so it can only rise).
backends: interpreter, julia, python, batched
p(1.0)=(0.05, 0.0)
p(0.5)=(0.95, 1.0)
