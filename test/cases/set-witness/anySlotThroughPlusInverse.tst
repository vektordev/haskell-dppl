-- set-witness/setWitnessSiblingConst with the then-arm's first field spelled
-- x + 0.0. Masking that field (ANY) recovered x through plus's inverse as
-- the ANY value itself, which the condition then compared at run time ("less
-- than can only compare two numbers ... (VAny, VFloat 0.5)"), and at -O0 the
-- inverse's own Minus died on it. The transported witness now reads a
-- wildcard as "unconstrained" (WFull), and the sibling-field residue factor
-- compares field by field so x + 0.0 at the wildcard witness is never
-- evaluated. Must agree with setWitnessSiblingConst row for row. Task
-- any-slot-through-injf-inverse-reaches-condition.
p((0.3, 1.0)) is impossible
p((0.7, 0.0)) is impossible
p((0.7, 1.0))=(1.0, 1.0)
p((0.3, 0.0))=(1.0, 1.0)
p((ANY, 1.0))=(0.5, 0.0)
p((ANY, 0.0))=(0.5, 0.0)
p((0.7, ANY))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
