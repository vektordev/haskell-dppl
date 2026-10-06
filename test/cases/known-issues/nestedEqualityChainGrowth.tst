-- A nest of D `== True` tests over one random Bool. The AnyExcept split
-- compiles its operand three times per level (the marginal arm, which is
-- always the constant (1, 0), and the excepted point twice), so the IR grows
-- about 8.5x per level. The -O2 module is a constant 1.8 KB because the
-- optimizer folds it all away again; the user pays in compile time (0.5 s at
-- D=4, 7 s at D=5, at 5c4627b). The pin reads the compile's allocation at the
-- default -O2. It holds until both halves are fixed: docs tasks
-- anyexcept-any-arm-compiled-instead-of-constant (about 5x per level after it)
-- and anyexcept-twin-point-compiled-twice.
expect-failure: growth above polynomial 2
knob: D = 1, 2, 3, 4
metric: alloc
flags: --noIntegrate
