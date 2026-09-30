p((0.5, (1.1, 0.2)))=(1.1483826789389478e-2, 3.0, False)
-- Task let-alias-of-random-binding-crashes-toirnormalparams, the accumulator
-- shape, fixed by task reinfer-body-under-recovered-bindings
-- (law-carrying-modality M1). A witnessed running sum (`p2 = s1 + s2`, pinned
-- by observing s1 and s2) feeds a further Normal; p2 kept a stale PNormal
-- after s1 and s2 were recovered, and toIRNormalParams was handed
-- `Var "p2"`. This is how a physics simulation accumulates position from
-- speed. p = phi(0.5) * phi(1.1) * phi(0.2 - 1.6).
