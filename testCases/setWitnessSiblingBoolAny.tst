-- A discrete sibling and an x-free deterministic arm: the else arm is a
-- membership test of (False, 0.0) against the sample, whose first slot may
-- be the marginal wildcard. memberGuard's point case is wildcard-aware for
-- this row (a static OpEq on a bare VAny answers False, i.e. 0 mass).
p((ANY, 0.0))=(0.5, 0.0)
p((ANY, 0.7))=(1.0, 1.0)
p((True, 0.7))=(1.0, 1.0)
p((False, 0.0))=(0.5, 0.0)
p((True, 0.3)) is impossible
p((False, 0.3)) is impossible
