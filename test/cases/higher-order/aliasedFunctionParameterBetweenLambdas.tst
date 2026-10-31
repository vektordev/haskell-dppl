-- namedHofForwardsRandomArg (`app f x = f x`) with the function parameter
-- aliased between the curried helper's two lambdas, the AliasIntro rewrite at
-- its outer site: the same answers, Normal + 1.0. Eta expansion makes the body
-- `draw g = f in draw x = p in g x`, where the set-witness walk met the read of
-- `g` in a nested let's body and could not enter the alias in place; an alias
-- of a local is now entered at every read (task
-- alias-between-curried-lambdas-refuses-enumerable-and-function-arguments).
p(0.5)=(0.35206533, 1.0, False)
p(1.0)=(0.39894228, 1.0, False)
p(ANY)=(1.0, 0.0, False)
cdf(1.0)=(0.5, 0.0)
