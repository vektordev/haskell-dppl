-- either-maybe/observeChainedDiscrete with main's observe binder renamed
-- from u to m, observeIsOne's parameter name. The enumeration over the
-- argument's support binds the loop variable under the parameter's name, and
-- the argument's measure is compiled at it: the observe's own `\m` shadowed
-- it, and `w == 1` read the Maybe ("Equals can only evaluate on two values:
-- (VInt 1, VEither (Right (VInt 1)))"). Docs task
-- callee-body-name-sensitive-across-call.
p(Right 1)=(0.3, 0.0)
p(Right 2) is impossible
p(Right 0) is impossible
p(Left ())=(0.7, 0.0)
p(Right ANY)=(0.3, 0.0)
p(Left ANY)=(0.7, 0.0)
