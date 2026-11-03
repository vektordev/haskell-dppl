-- Probe row 4 of design law-carrying-modality's evidence table, the
-- rewritten (helper-extracted) half; its twin is
--   main = draw x = Uniform in if x < 0.5 then x else x * 3.0
-- p(1.5) pins the `if` threshold x < 0.5 on a continuous draw: the else arm's
-- lower edge 0.5 * 3.0 = 1.5 belongs to the else arm, a jump from density 0
-- below to 1/3 above. The sampler window straddles the jump, so it opts out.
-- Was a known issue ("tagged invocation") until task
-- binding-resolver-one-application-rule.
p(0.3)=(1.0, 1.0, False)
p(0.6) is impossible
p(2.0)=(0.33333333, 1.0, False)
p(2.5)=(0.33333333, 1.0, False)
p(1.5)=(0.33333333, 1.0, False) no-sample
p(ANY)=(1.0, 0.0, False)
cdf(0.3)=(0.3, 0.0)
cdf(1.5)=(0.5, 0.0)
