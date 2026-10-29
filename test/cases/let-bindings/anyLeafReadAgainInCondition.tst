p(((0.0, ANY), 1.0))=(0.119683, 1.0)
p(((0.0, ANY), 2.0))=(0.279260, 1.0)
p(((0.0, 0), 1.0))=(0.119683, 1.0)
p(((0.0, 1), 1.0))=(0.0, 1.0)
p(((0.0, ANY), ANY))=(0.398942, 1.0)
-- The ANY leaf of a drawn tuple that the body reads again, in a condition.
-- The ANY reached `snd e == 0` as a value and compared False, so the first
-- row answered 0 (impossible). The binding now sums the leaf over its domain
-- {0, 1}. Task any-mark-passed-as-recursive-call-state.
