-- topK inflation canary (task topk-inflates-probability-int-comparison-mix):
-- p(False) is the complement of the CDF P(rhs <= 0.5) = 0.05, whose only
-- contributing arm prunes away at threshold 0.1. Before the fix p(False)
-- answered 1.0 under topK; Corpus.TopKNeverInflates pins <= 0.95.
backends: interpreter, julia, python, batched
p(True)=(0.05, 0.0)
p(False)=(0.95, 0.0)
