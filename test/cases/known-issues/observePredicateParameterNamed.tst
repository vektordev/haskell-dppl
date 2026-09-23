-- Verified at commit 8bb0a44 on dev: observePredicateParameterLambda with a named
-- top-level predicate passed as the argument instead of a lambda. This one does
-- not even reach the tagged-invocation refusal: forward chaining crashes on an
-- internal lookup of the call site's chain name (ForwardChaining.hs,
-- "Expression with given chain name not found"). Idealized, as
-- observeKeywordNamedPred: p(Right 1) = (0.3, 0.0), p(Left ()) = (0.7, 0.0)
expect-failure: diagnostic "Expression with given chain name not found"
