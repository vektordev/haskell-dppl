p((3.0, (ANY, 2.0)))=(1.0, 0.0, False)
p((3.0, (1.0, 2.0)))=(1.0, 0.0, False)
p((3.0, (1.0, ANY)))=(1.0, 0.0, False)
p((3.0, (1.0, 2.5))) is impossible
p((ANY, (2.0, ANY))) is impossible
-- A deterministic `draw` compared with a query holding a nested ANY. Its
-- compiled comparison was a bare `==`, which read `(ANY, 2.0)` against
-- `(1.0, 2.0)` as a mismatch and answered impossible, while the literal
-- `(3.0, (1.0, 2.0))` answered 1.0. Task reinfer-body-under-recovered-bindings
-- found it: once re-inference types a `draw` over a recovered variable
-- Deterministic, this comparison is what compiles it, so the rewrite net's
-- draw-intro of setWitnessSiblingNested hit it. The deterministic-application
-- arm now uses equalityGuard, as every other deterministic leaf does.
