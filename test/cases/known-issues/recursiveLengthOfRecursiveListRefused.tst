-- A recursive consumer (len) of a recursively generated random list is
-- refused. Either half alone compiles: len of a non-recursive random list
-- (`len (if Uniform < 0.5 then [] else [1])`) and a non-recursive predicate on
-- the recursive list (`isNull (tail (rollout 3))`) both answer exactly.
-- `main = len (rollout 3)` (no comparison) refuses the same way.
-- Idealized: lengths 0/1/2/3 have mass 0.5/0.25/0.125/0.125, so
-- p(True) = 0.75. Docs task recursive-consumer-of-recursive-random-list-refused
-- (found by experiments_nest llm-lookahead-constraints, spelling 2).
expect-failure: refused "set-valued witness construction failed for the binding of 'xs'"
