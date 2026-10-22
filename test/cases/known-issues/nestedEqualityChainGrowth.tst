-- A nest of D `== True` tests over one random Bool. The AnyExcept split
-- compiles its operand three times per level (the marginal arm, which is
-- always the constant (1, 0), and the excepted point twice), so the IR grows
-- about 8.5x per level. The -O2 module is a constant 1.8 KB because the
-- optimizer folds it all away again; the user pays in compile time (0.5 s at
-- D=4, 7 s at D=5, at 5c4627b). The pin reads the compile's allocation at the
-- default -O2. It holds until both halves are fixed: docs tasks
-- anyexcept-any-arm-compiled-instead-of-constant (about 5x per level after it)
-- and anyexcept-twin-point-compiled-twice. Since
-- presult-unbound-block-copied-per-field shares the Any-safe blocks the levels
-- copied, it is about 2.2x per level (the twin point; 0.4 s at D=8), so the
-- knob reaches further to see it: at D = 1..4 the slopes stayed under the bound.
expect-failure: growth above polynomial 2
knob: D = 2, 4, 6, 8
metric: alloc
flags: --noIntegrate
