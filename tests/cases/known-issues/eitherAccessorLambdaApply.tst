-- A callee selected via `fromLeftPartial` of an Either
-- literal is not reduced to its lambda body by CalleeNormalize, so applying
-- it still crashes instead of resolving. The idealized result is the density
-- of 1.0 + Normal, i.e. N(1, 1), same family as the sibling Gap 1 case.
expect-failure: diagnostic "should resolve to a lambda"
