-- A cross-slot conditional edit: "if object 1 is metal, object 2 becomes
-- rubber". The emitted forward answers one-slot queries correctly
-- (p(Scene ANY (Obj Rubber) ANY) = 0.268, p(Scene ANY ANY (Obj Metal)) = 0.36
-- at the logits below) but the all-ANY query raises in Python:
--   Exception: isNil: constructor test on an unobserved value (ANY); the
--   enclosing inference must marginalise or refuse before testing a hole
-- and so does writeLogits, whose first line asks for exactly that normaliser.
-- The same edit over a 10-slot CLEVR scene does not crash. Found by
-- experiments_nest symbolic-latent-scene-editing. Docs task
-- cross-slot-conditional-all-any-query-crashes.
-- Idealized: the total mass, 1.
expect-failure: broken
backends: python
p(Scene ANY ANY ANY, (2, [0.4, 0.6, 0.3, 0.7, 0.5, 0.5, 0.2, 0.8, 0.1, 0.9, 0.6, 0.4]))=(1.0, 0.0)
