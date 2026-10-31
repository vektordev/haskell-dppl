-- leadingRandomArgumentCurried (`g c n = (if c then 1 else 0) + n`) with the
-- leading parameter aliased between the curried helper's two lambdas, the
-- AliasIntro rewrite at its outer site: the same answers. Inside the closure
-- the modality engine evaluates at the call, `c` is a parameter the compiler
-- holds at a point, so the alias `d = c` needs no engine of its own; it was
-- floored sample-only (task
-- alias-between-curried-lambdas-refuses-enumerable-and-function-arguments).
p(6)=(0.3, 0.0)
p(5)=(0.7, 0.0)
