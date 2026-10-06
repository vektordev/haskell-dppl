-- The helper-extracted twin of set-witness/setWitnessSiblingConst (task
-- named-function-list-head-witness-not-recovered). Once forward chaining sees
-- through h's tuple, the set-witness transport inverts `h x` as `fst s`; the
-- call then carries the same residue factor a syntactic tuple does, so h's
-- constant field is still checked against the sample.
p((0.7, 1.0))=(1.0, 1.0)
p((0.3, 0.0))=(1.0, 1.0)
p((0.7, 0.0)) is impossible
p((0.3, 1.0)) is impossible
