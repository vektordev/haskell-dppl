-- A helper whose parameter has the same name as the enumerated draw it is
-- called on. The enumeration loop binds the helper's parameter around the
-- argument's own measure, which read `b == b` (always true) and dropped the
-- draw's weight: p(1) = p(0) = 1.0. Renaming the helper's parameter gave 0.3
-- and 0.7. Found by the rewrite-invariance net's helper extraction (task
-- rewrite-invariance-net-draw-apply-helper-alias), which names a helper's
-- parameters after the caller's variables.
p(1)=(0.3, 0.0)
p(0)=(0.7, 0.0)
p(2) is impossible
