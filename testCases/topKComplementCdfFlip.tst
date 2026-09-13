-- topK inflation canary (task topk-inflates-probability-int-comparison-mix):
-- the negation's inverse is decreasing, so in cumulative mode the operand's
-- CDF P(x <= 0.5) = 0.05 is flipped through a complement -- and that CDF's
-- only contributing arm prunes away at threshold 0.1. Before the fix
-- cdf(-0.5) answered 1.0 under topK; Corpus.TopKNeverInflatesCdf pins <= 0.95.
backends: interpreter, julia, python, batched
p(-0.2)=(0.05, 0.0)
p(-0.7)=(0.95, 0.0)
cdf(-0.8)=(0.0, 0.0)
cdf(-0.5)=(0.95, 0.0)
cdf(-0.1)=(1.0, 0.0)
