-- anyLeafReadAgainThroughAlias (one alias) with a second alias in the chain
-- (`draw e2 = e in draw y = e2`), the AliasIntro rewrite at its outer site.
-- With two aliases the ANY query was a runtime refusal ("binding 'e' is
-- unobserved (ANY in its witnessing slot)"): the witness chain's wildcard
-- test counted steps toward other occurrences, so the leaf-sum's witness
-- read as unevaluable. Fixed with task
-- aliased-parameter-plus-zero-marginal-loses-dim (readsAnyChain over the
-- needed steps); was the known-issues pin aliasChainOfStructuredDrawAnyMarginalRefused.
-- Docs task alias-chain-of-structured-draw-any-marginal-refused.
p(((0.0, ANY), 1.0))=(0.119683, 1.0)
p(((0.0, ANY), 2.0))=(0.279260, 1.0)
p(((0.0, 0), 1.0))=(0.119683, 1.0)
p(((ANY, ANY), 1.0))=(0.3, 0.0)
p(((0.0, 1), 1.0)) is impossible
