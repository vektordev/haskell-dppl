-- A user ADT constructor is a field constructor too (its field accessors
-- are the deconstructing inverses), so the transport through `a` dropped
-- the `b` field the same way.
p(P 0.7 1.0)=(1.0, 1.0)
p(P 0.3 0.0)=(1.0, 1.0)
p(P 0.7 0.0) is impossible
p(P 0.3 1.0) is impossible
