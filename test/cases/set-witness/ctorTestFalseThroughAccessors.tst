-- Task point-inversion-vanyexcept-witness-crashes. A constructor test reached
-- through a field accessor and head: observed False, its inverse is "any
-- value but Green", which the accessors' inverses bury inside Obj and a list.
-- The point inversion declines it; the set-witness engine splits the test as
-- the complement of the point "head's col is Green" (1 - 0.4).
p(False)=(0.6, 0.0)
p(True)=(0.4, 0.0)
cdf(False)=(0.6, 0.0)
cdf(True)=(1.0, 0.0)
