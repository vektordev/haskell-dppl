-- The `>` spelling of strictLessThanSharedOperand, with the shared operand on
-- the left: `y > x` is x's mass strictly below y, so x = 0, y = 1 only
-- (task strict-int-less-than-non-strict-when-operand-shared; was 0.5).
dense
p(True)=(0.25, 0.0)
p(False)=(0.75, 0.0)
