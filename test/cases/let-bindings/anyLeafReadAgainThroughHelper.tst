p(((0.0, ANY), 1))=(0.279260, 1.0)
p(((0.0, ANY), 0))=(0.119683, 1.0)
p(((0.0, 0), 1))=(0.0, 1.0)
-- anyLeafReadAgainInOutput with the body in a helper and the bound value a
-- projection of a nullary declaration: the reads are followed into the
-- callee's body, the domain through `fst` and `mark`. Before, the first row
-- answered phi(0) = 0.398942.
-- Slow-tier follow-up of task any-mark-passed-as-recursive-call-state.
