-- leadingRandomArgumentCurried (`g c n = (if c then 1 else 0) + n`) with the
-- leading parameter aliased between the curried helper's two lambdas, the
-- AliasIntro rewrite at its outer site. The original answers p(6) = 0.3; so do
-- the alias inside both lambdas and the in-place twin
-- `draw d = Uniform < 0.3 in (\n -> ...) 5`. An aliased Normal parameter in
-- the same position answers (`f x = draw a = x in \y -> (a, y)`). Verified at
-- 76152ac on dev. Docs task
-- alias-between-curried-lambdas-refuses-enumerable-and-function-arguments.
expect-failure: refused "has no inference rule for its arguments"
