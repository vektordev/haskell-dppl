backends: interpreter, julia, python, batched
p((2.5, (2.1, (1.6, (1.2, (0.7, (0.3, (-0.1, -0.6))))))), ThetaTree [0.45, 0.2] [])=(195.1942143297196, 8.0, False)
p((2.6, (2.0, (1.7, (1.1, (0.8, (0.2, (0.0, -0.5))))))), ThetaTree [0.45, 0.2] [])=(26.416664282460697, 8.0, False)
p((2.5, (2.1, (1.6, (1.2, (0.7, (0.3, (-0.1, ANY))))))), ThetaTree [0.45, 0.2] [])=(100.96214600969721, 7.0, False)
-- Task chained-gaussian-trajectory-compile-exponential. An 8-step Gaussian
-- random walk observed in full: s_k = s_{k-1} - a + sigma * eps_k from s_0 = 3,
-- at a = 0.45, sigma = 0.2. The likelihood is the product of the eight one-step
-- densities N(s_k; s_{k-1} - a, sigma); expected values are that hand-derived
-- oracle, not compiler output. The ANY row drops the last factor (s8 is a sink).
-- Before the fix this did not compile in three minutes (the -O0 IR grew ~6x
-- per step); the growth itself is pinned by
-- TestInternals.gaussianChainIRNotExponential.
