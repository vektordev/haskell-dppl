-- The ANY in the bound variable's own slot, read through + 0.0's inverse
-- inside the set-witness engine's per-component tuple split, with a fresh
-- sibling factor (exp Uniform, density 1/y on [1, e]) beside it. It raised on
-- every backend. Then-arm: P(h < 0.5) times the sibling's density; else-arm:
-- P(h >= 0.5) times Uniform's. Task
-- any-slot-through-injf-inverse-reaches-condition (second repro).
p((ANY, 0.3))=(0.5, 1.0)
p((ANY, 1.5))=(0.3333333333333333, 1.0)
p((0.2, 1.5))=(0.6666666666666666, 2.0)
p((ANY, ANY))=(1.0, 0.0)
