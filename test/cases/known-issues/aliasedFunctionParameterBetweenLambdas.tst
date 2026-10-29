-- namedHofForwardsRandomArg (`app f x = f x`) with the function parameter
-- aliased between the curried helper's two lambdas, the AliasIntro rewrite at
-- its outer site. The original answers p(1.0) = 0.39894228 (Normal + 1.0), and
-- so does the alias inside both lambdas (`app f x = draw g = f in g x`).
-- Verified at 76152ac on dev. Docs task
-- alias-between-curried-lambdas-refuses-enumerable-and-function-arguments.
expect-failure: refused "no inference engine applies to the parameter bound by the call of 'app'"
