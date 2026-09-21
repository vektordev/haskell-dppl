-- Found by the let/set-witness fuzz generator (~72% of its crashes): the else-arm draws
-- a fresh Normal while the then-arm is deterministic given the outer
-- lambda's parameter, which the set-witness engine cannot invert. Idealized
-- behavior: a graceful `Left` refusal for probability/integrate (not an
-- uncaught exception), while `generate` still compiles -- no numeric value
-- is at issue, this is a refusal-channel bug.
expect-failure: diagnostic "set-valued witness construction failed"
