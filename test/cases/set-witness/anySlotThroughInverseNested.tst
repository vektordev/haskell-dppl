-- anySlotThroughPlusInverse one tuple deeper and through log, whose inverse
-- (exp) carries no domain guard but whose forward image is bounded: the
-- wildcard can sit in the inner slot, the outer one, or both, and the
-- residue factor's field-by-field comparison has to see through the inner
-- tuple's own let-binding. Then-arm: log x for x in (0.5, 1], density
-- e^y at y. Task any-slot-through-injf-inverse-reaches-condition.
p(((ANY, 2.0), 1.0))=(0.5, 0.0)
p(((ANY, 3.0), 1.0)) is impossible
p(((-0.3, 2.0), 1.0))=(0.7408182206817179, 1.0)
p(((-0.9, 2.0), 1.0)) is impossible
p(((0.5, 2.0), 1.0)) is impossible
p(((ANY, 2.0), 0.0))=(0.5, 0.0)
p(((0.3, 2.0), 0.0))=(1.0, 1.0)
p((ANY, 1.0))=(0.5, 0.0)
p(((ANY, ANY), ANY))=(1.0, 0.0)
