p(((0.0, ANY), 1))=(0.279260, 1.0)
p(((0.0, ANY), 0))=(0.119683, 1.0)
p(((0.0, 0), 1))=(0.0, 1.0)
-- The ANY leaf of a drawn tuple read again in a second output slot: the
-- second slot's 1 was compared against the ANY as a wildcard, and the first
-- row answered phi(0) = 0.398942 (the leaf constrained by nothing) instead
-- of phi(0) * P(snd e = 1). Task any-mark-passed-as-recursive-call-state.
