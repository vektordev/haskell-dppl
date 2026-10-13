-- Probe row 5 of design law-carrying-modality's evidence table, the
-- rewritten (helper-extracted) half; its twin is
--   main = draw x = Uniform in (x, x * Normal)
-- Was a known issue (no probability function, modality Bottom) until task
-- binding-resolver-one-application-rule: the modality engine asks the witness
-- question of a named callee's binding too.
batched
p((0.5, 0.2))=(0.73654028, 2.0, False)
p((0.25, -0.1))=(1.47308056, 2.0, False)
p((0.5, ANY))=(1.0, 1.0, False)
