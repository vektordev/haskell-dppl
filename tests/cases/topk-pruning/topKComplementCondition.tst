-- topK inflation canary (task topk-inflates-probability-int-comparison-mix):
-- the condition is itself an if whose True-probability (0.05) prunes to 0 at
-- threshold 0.1, and the else-weight is the complement of it. Before the fix
-- p(2.0) answered 1.0 under topK; Corpus.TopKNeverInflates pins <= 0.95.
p(1.0)=(0.05, 0.0)
p(2.0)=(0.95, 0.0)
p(3.0) is impossible
