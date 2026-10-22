-- Task slow-fuzz-seed-findings-2026-10-06 (BackendsAgree seed 801831). The
-- then arm transports its snd slot through `v0 == 1.0`; observed False that
-- is the exclusion set "any v0 but 1.0". Crossing the tuple constructor also
-- carried a residue factor, which bound v0 to the VAnyExcept sentinel: no
-- text backend compiled the module, and the interpreter died on `==` at
-- (0.0, False). The transport is now declined there and the tuple split
-- answers. A wildcard in the Bool slot used to be branched on as the
-- polarity ("Condition is not a boolean: VAny").
p((0.0, False))=(0.5, 0.0)
p((1.0, True))=(0.5, 0.0)
p((0.0, True))=(0.12098536, 1.0)
p((0.0, ANY))=(0.5, 0.0)
p((1.0, ANY))=(0.5, 0.0)
p((ANY, True))=(0.5, 0.0)
p((1.0, False)) is impossible
p(ANY)=(1.0, 0.0)
