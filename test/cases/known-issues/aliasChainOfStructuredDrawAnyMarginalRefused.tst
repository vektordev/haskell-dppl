-- anyLeafReadAgainThroughAlias (one alias, answers) with a second alias in
-- the chain (`draw e2 = e in draw y = e2`), the AliasIntro rewrite at its
-- outer site. With one alias the same query answers 0.119683; with two it is a
-- runtime refusal. Verified at 8924628 on dev. Docs task
-- alias-chain-of-structured-draw-any-marginal-refused.
backends: interpreter
expect-failure: broken
p(((0.0, ANY), 1.0))=(0.119683, 1.0)
