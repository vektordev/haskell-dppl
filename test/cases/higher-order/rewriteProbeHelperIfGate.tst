-- Probe row 4 of design law-carrying-modality's evidence table, the
-- rewritten (helper-extracted) half; its twin is
--   main = draw x = Uniform in if x < 0.5 then x else x * 3.0
-- Was a known issue ("tagged invocation") until task
-- binding-resolver-one-application-rule.
p(0.3)=(1.0, 1.0, False)
p(0.6) is impossible
p(2.0)=(0.33333333, 1.0, False)
p(2.5)=(0.33333333, 1.0, False)
p(ANY)=(1.0, 0.0, False)
cdf(0.3)=(0.3, 0.0)
cdf(1.5)=(0.5, 0.0)
