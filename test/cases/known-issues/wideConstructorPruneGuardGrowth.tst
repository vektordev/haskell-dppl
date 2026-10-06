-- A record with N constant Int fields and one random field: the
-- field-constructor equation of toIRInference ORs each field's impossibility
-- flag into an accumulator it never binds, so the flag holds 2^N copies of the
-- first field's. Measured at 5c4627b, -O0 emitted Python: N=2 21 KB, 4 56 KB,
-- 6 208 KB, 8 859 KB, 10 3.7 MB (slope 3.2 between 4 and 6, rising). Bound,
-- the module is linear (about 59 KB at N=14). -O2 folds the module back to
-- linear, so the pin reads the -O0 module, where the wall is visible without
-- paying for it. Docs task field-constructor-prune-guard-exponential-in-width.
expect-failure: growth above polynomial 2
knob: N = 2, 4, 6, 8, 10
metric: code-size
flags: -O 0 --noIntegrate
