-- A continuous `==` on a nested-let-bound value, then a second comparison
-- (task sampling-matches-pdf-continuous-equality-density). Crashed before the
-- complement of a point became a WSet of its own -- even with the `==` alone
-- (`if y == 1.0 then 0 else 2`: `OpSub VAnyExcept .. 1.0` in forceOp), since
-- the sentinel was carried through y = x + 1.0's inverse. y == 1.0 iff
-- x == 0.0, so p(0) is N(0) (unit Jacobian); the complement costs the
-- intervals nothing.
p(0)=(0.3989422804014327, 1.0)
p(1)=(0.15865525393145707, 0.0)
p(2)=(0.8413447460685429, 0.0)
