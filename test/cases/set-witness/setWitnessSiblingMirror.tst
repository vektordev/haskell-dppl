-- The mirror of setWitnessSiblingConst: the bound variable in the second
-- field, the constant sibling in the first.
p((1.0, 0.3)) is impossible
p((0.0, 0.7)) is impossible
p((1.0, 0.7))=(1.0, 1.0)
p((0.0, 0.3))=(1.0, 1.0)
p((1.0, ANY))=(0.5, 0.0)
p((0.0, ANY))=(0.5, 0.0)
p((ANY, 0.3))=(1.0, 1.0)
