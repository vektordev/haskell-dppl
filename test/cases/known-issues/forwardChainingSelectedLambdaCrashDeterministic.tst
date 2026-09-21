-- Same root cause as forwardChainingSelectedLambdaCrash,
-- fully deterministic variant (no probabilistic value anywhere). `mk True`
-- selects `\x -> x + 1.0`, applied to 3.0 gives 4.0 deterministically -- the
-- idealized row below states that value. The doc's cross-reference confirms
-- this crashes the same way but doesn't requote this exact program's message,
-- so the mechanism is left unpinned (`broken`) rather than guessing a
-- diagnostic substring.
expect-failure: broken
p(4.0)=(1.0, 0.0)
