-- A named function applied to two random arguments, both point witnesses in the
-- returned tuple. The let spelling `draw x = Normal in draw y = Normal in (x, y)`
-- answers; here the outer application (argument y) is compiled at callee
-- `f Normal`, which has a random leading argument, so its body factor cannot be
-- the callee's probability function at a deterministic argument list (task
-- named-function-list-head-witness-not-recovered). Point inversion is withheld
-- there rather than dropping the x field, and the set-witness engine refuses a
-- tagged invocation (cps-list-witness-construction-failure, G0).
-- Idealized: p((0.0, 0.0)) = phi(0)^2 = (0.15915494, 2).
expect-failure: refused "tagged invocation"
