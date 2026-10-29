p(((0.0, ANY), 1.0))=(0.119683, 1.0)
p(((0.0, ANY), 2.0))=(0.279260, 1.0)
p(((0.0, 0), 1.0))=(0.119683, 1.0)
p(((0.0, 1), 1.0))=(0.0, 1.0)
-- anyLeafReadAgainInCondition with the body reading the drawn tuple through
-- an alias: the wildcard-leaf sum follows the reads through `draw y = e`.
-- Before, the alias hid the second read and the first row answered 0.
-- Slow-tier follow-up of task any-mark-passed-as-recursive-call-state.
