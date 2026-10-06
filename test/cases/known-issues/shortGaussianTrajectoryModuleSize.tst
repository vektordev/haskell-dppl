-- The same random-walk trajectory as gaussianTrajectoryUnprunedModuleSize,
-- at 4 steps. Below 5 steps the compile takes a different, superlinear path:
-- the -O2 module is 42 / 142 / 374 KB at K = 2 / 3 / 4, then 57 / 73 / 91 KB at
-- K = 5 / 6 / 7 (5c4627b). So this 4-step module is 6.5x the 5-step one.
-- Docs task short-gaussian-trajectory-module-larger-than-long.
expect-failure: code-size above 200 KB
