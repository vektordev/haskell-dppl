-- Idealized values (what the fixed compiler should produce), hand-derived as in
-- test/cases/neural/categoricalProductFusion.tst:
--   camNN = [0.5, 0.3, 0.2], depthNN = [0.1, 0.6, 0.3]
--   p(True)  = 0.5*0.1 + 0.3*0.6 + 0.2*0.3 = 0.29
--   p(False) = 1 - 0.29                   = 0.71
-- Verified at haskell-dppl 92365e7 (dev): compiling throws an uncaught `error`
-- from IRCompiler.setWitnessApply instead.
expect-failure: broken
p(True,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.29, 0.0)
p(False,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.71, 0.0)
