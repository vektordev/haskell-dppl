-- Probe row 2 of design law-carrying-modality's evidence table, the
-- rewritten (helper-extracted) half; its twin is
--   main = draw x = Uniform in (x, x)
-- Was a known issue ("tagged invocation") until task
-- named-function-list-head-witness-not-recovered.
p((0.3, 0.3))=(1.0, 1.0, False)
p((0.3, ANY))=(1.0, 1.0, False)
p((0.3, 0.4)) is impossible
