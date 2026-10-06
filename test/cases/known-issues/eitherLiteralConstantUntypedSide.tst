-- An Either value literal (`Left True`, capitalised, a Constant (VEither ..))
-- leaves its other side's type NotSetYet, so this is refused by RInfer with
-- "Couldn't match type 'Bool' with 'NotSetYet'" (and `main = Left True` alone
-- crashes with "Comparison not implemented for type: NotSetYet"). The builtin
-- `left True`/`right False` spelling compiles. Docs task
-- either-literal-constant-untyped-side.
expect-failure: broken
p(Left True) = (0.5, 0.0)
p(Right False) = (0.5, 0.0)
