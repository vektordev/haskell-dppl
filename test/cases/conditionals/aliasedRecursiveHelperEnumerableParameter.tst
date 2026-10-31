-- decreasingRecursionEnumeratedArgument with the recursive helper's parameter
-- aliased (`draw q = r in ...`), the AliasIntro rewrite at the helper's site:
-- the same answer, p(7) = 1.0. Inside the closure the modality engine
-- evaluates at the call, `r` is a parameter the compiler holds at a point, so
-- the alias needs no engine of its own; it was floored sample-only. Fixed by
-- task alias-between-curried-lambdas-refuses-enumerable-and-function-arguments
-- (pin of task alias-of-recursive-helper-parameter-refuses-with-random-argument).
p(7)=(1.0, 0.0)
