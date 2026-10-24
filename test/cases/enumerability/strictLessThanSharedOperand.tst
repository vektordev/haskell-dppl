-- A strict Int `<` whose right operand is also read by the sibling `&&`
-- operand: `y` is enumerated and `x < y` is answered as x's CDF at the known
-- value, which must be asked at y - 1 (task
-- strict-int-less-than-non-strict-when-operand-shared). Only x = 0, y = 1
-- satisfies it; the inclusive CDF answered P(x <= y) = 0.75.
dense
p(True)=(0.25, 0.0)
p(False)=(0.75, 0.0)
