-- A named helper whose result is an if-selected lambda, called with both
-- arguments at once: `(mk True) Normal`. Was the known-issues pin
-- forwardChainingSelectedLambdaCrash (ForwardChaining's
-- constructEquivalenceClauses: "expected chain name to be a Lambda"). mk is
-- now eta-expanded into `mk b p = (if b then .. else ..) p` (task
-- arrow-result-main-entry-points), so the result is N(1, 1).
p(1.0)=(0.3989423, 1)
p(2.0)=(0.2419707, 1)
cdf(1.0)=(0.5, 0)
cdf(2.0)=(0.8413447, 0)
