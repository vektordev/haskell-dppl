-- topK prunes inside an if condition (task map-semiring-complement-and-cdf-wrong):
-- the condition is itself an if, so both its weights come from one pass over its
-- arms, each a lower bound, and its 0.05-weight else arm prunes at threshold 0.1.
-- Pruned, p(1) = p(2) = 0.475; TestInternals "topK prunes inside a condition"
-- pins those, and Corpus.TopKNeverInflates pins that they stay below these.
p(1)=(0.476, 0.0)
p(2)=(0.524, 0.0)
p(3) is impossible
