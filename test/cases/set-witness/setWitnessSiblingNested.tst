-- A structured sibling: the whole residue is checked, not just a leaf.
p((0.7, (1.0, 2.0)))=(1.0, 1.0)
p((0.3, (0.0, 0.0)))=(1.0, 1.0)
p((0.7, (1.0, 0.0))) is impossible
p((0.3, (1.0, 2.0))) is impossible
p((ANY, (0.0, 0.0)))=(0.5, 0.0)
p((0.7, (ANY, 2.0)))=(1.0, 1.0)
