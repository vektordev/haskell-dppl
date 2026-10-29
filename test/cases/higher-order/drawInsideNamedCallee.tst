-- higher-order/rewriteProbeHelperScaledNoise with the noise drawn into a
-- binding inside the callee; its in-place twin is
--   main = draw x = Uniform in draw z = x * Normal in (x, z)
-- Was Bottom (no probability function) until task
-- named-callee-binding-not-floored: forward chaining's per-invocation copy of
-- f's body held nothing behind the draw, so x was not witnessed from main's
-- observation (M6's class C of dispatch-on-law-certificates).
p((0.5, 0.2))=(0.73654028, 2.0)
p((0.25, -0.1))=(1.47308056, 2.0)
p((0.5, ANY))=(1.0, 1.0)
p((1.5, 0.2)) is impossible
