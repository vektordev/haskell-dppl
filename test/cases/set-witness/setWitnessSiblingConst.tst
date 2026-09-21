-- task set-witness-transport-drops-sibling-field-constraint: the root is an
-- if, so the set-witness engine transports the point through fst onto x. The
-- constant sibling field must still be checked against snd of the sample
-- (a residue factor, dim 0); it used to be dropped, answering 1.0 everywhere
-- and 1.0 (not 0.5) on each ANY row.
p((0.3, 1.0)) is impossible
p((0.7, 0.0)) is impossible
p((0.7, 1.0))=(1.0, 1.0)
p((0.3, 0.0))=(1.0, 1.0)
p((ANY, 1.0))=(0.5, 0.0)
p((ANY, 0.0))=(0.5, 0.0)
p((0.7, ANY))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
