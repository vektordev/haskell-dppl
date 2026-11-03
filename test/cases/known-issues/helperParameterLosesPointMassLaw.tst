-- A point mass drawn in main and passed to a helper loses its law at the
-- helper's parameter: (0.0 * z) + rwv0 is treated as a continuous sum, so a
-- point query at 0.0 answers impossible. `(0.0 * z) + 0.0` inline answers
-- 1.0 at dim 0. stagediff diverges first at Modality Inference ("a point mass
-- at VFloat 0.0 vs of no known value"). Docs-repo task
-- helper-parameter-loses-point-mass-law. Verified on dev at compiler cc35ee7.
-- Pinned is the wrong answer (0.0, impossible); the idealized row is
-- p(0.0) = (1.0, 0.0).
backends: interpreter, python
expect-failure: wrong-result
p(0.0) is impossible
