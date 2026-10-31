-- tupleCtorTestOfSharedDraw with its second slot behind the pair-fst tuple
-- law. The constructor test's witness (Face ANY ANY, or the VAnyExcept
-- sentinel on False) loses the merge to the whole value, but its let prefix
-- stayed in the merged chain, dead, and 6ce80d3's rule that a chain holding
-- the sentinel is no point inverse then declined the whole chain: 1.0 at every
-- True first slot (slow-tier triage 2026-10-31). The losing prefix is pruned.
p((True, Face True False))=(0.56, 0.0)
p((True, Face False False))=(0.24, 0.0)
p((True, Face ANY True))=(0.2, 0.0)
p((ANY, Face True True))=(0.14, 0.0)
p((False, Face True True)) is impossible
