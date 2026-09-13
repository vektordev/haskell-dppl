-- Two occurrences: the outer tuple is split structurally, and the first
-- field's transport still carries its own sibling as a residue factor while
-- the second occurrence's point must agree with the first.
p(((0.7, 1.0), 0.7))=(1.0, 1.0)
p(((0.3, 0.0), 0.3))=(1.0, 1.0)
p(((0.7, 0.0), 0.7)) is impossible
p(((0.7, 1.0), 0.6)) is impossible
