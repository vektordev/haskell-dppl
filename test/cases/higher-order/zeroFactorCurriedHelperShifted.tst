-- A curried helper returning the point 0.0 whatever its two arguments, then
-- shifted by 1.0: the call carries the point through both applications and
-- the sum folds it (task dirac-law-point-lost-under-plus-or-helper).
batched
p(1.0)=(1.0, 0.0)
p(0.0) is impossible
