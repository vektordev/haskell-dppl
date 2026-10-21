-- setWitnessEqFalseInTupleArm through a lambda applied in place, the spelling
-- BackendsAgree seed 801831 shrank to (task slow-fuzz-seed-findings-2026-10-06).
batched
p((0.0, False))=(1.0, 0.0)
p((0.0, True))=(0.24197072, 1.0)
p((0.0, ANY))=(1.0, 0.0)
p((1.0, False)) is impossible
