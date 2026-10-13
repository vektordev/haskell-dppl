backends: interpreter, julia, python, batched
p((2.5, (2.1, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(13.97119230165127, 4.0, False)
p((ANY, (2.1, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(5.27207776367064, 3.0, False)
p((2.5, (ANY, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(5.27207776367064, 3.0, False)
p((2.5, (2.1, (ANY, 1.2))), ThetaTree [0.45, 0.2] [])=(5.272077763670639, 3.0, False)
p((2.5, (2.1, (1.6, ANY))), ThetaTree [0.45, 0.2] [])=(7.226451674977263, 3.0, False)
p((ANY, (ANY, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(2.203453599534207, 2.0, False)
p((2.5, (ANY, (ANY, 1.2))), ThetaTree [0.45, 0.2] [])=(2.2034535995342073, 2.0, False)
p((ANY, (2.1, (ANY, 1.2))), ThetaTree [0.45, 0.2] [])=(1.9894367886486908, 2.0, False)
-- Task short-gaussian-trajectory-module-larger-than-long. gaussianTrajectory8 at
-- four steps, which is within --marginalSlots, so every mask of the four
-- correlated slots gets its own variant. The rows are a hand-derived oracle at
-- a = 0.45, sigma = 0.2: one-step densities N(s_k; s_{k-1} - a, sigma), and an
-- unobserved middle step widens the next one to N(s_{k+1}; s_{k-1} - 2a,
-- sqrt 2 sigma) (sqrt 3 for two). The variants used to re-guard the slots the
-- dispatcher had already shown concrete, so the -O2 module was 293 KB against
-- 53 KB at five steps (123 KB after the fix); the size is pinned by
-- TestInternals.shortGaussianTrajectoryVariantsCompact.
