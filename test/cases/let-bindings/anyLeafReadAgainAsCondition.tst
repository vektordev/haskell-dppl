p(((0.0, ANY), 1.0))=(0.119683, 1.0)
p(((0.0, ANY), 2.0))=(0.279260, 1.0)
p(((0.0, True), 2.0))=(0.0, 1.0)
-- The Bool ANY leaf of a drawn tuple used as an if condition in the body:
-- it raised "Condition is not a boolean: VAny". The binding now sums the
-- leaf over {True, False}. Task any-mark-passed-as-recursive-call-state.
