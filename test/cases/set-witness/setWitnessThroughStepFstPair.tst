-- set-witness/setWitnessSiblingConst with the compared x spelled
-- fst (x, 0.0). An interval does not transport through fst, so the
-- comparison used to be refused; a projection of a literal pair is now
-- inverted as that field. Must agree with setWitnessSiblingConst row for
-- row. Task set-witness-walk-stops-at-identity-injf-wrapper.
p((0.3, 1.0)) is impossible
p((0.7, 0.0)) is impossible
p((0.7, 1.0))=(1.0, 1.0)
p((0.3, 0.0))=(1.0, 1.0)
p((ANY, 1.0))=(0.5, 0.0)
p((ANY, 0.0))=(0.5, 0.0)
p((0.7, ANY))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
