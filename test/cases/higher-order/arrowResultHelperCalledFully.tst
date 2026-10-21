-- A helper whose result is a function value, reached through a point-free
-- main. main is expanded first (main a = pick a), which makes every use of
-- pick a full call, so pick is expanded on the second round. Task
-- arrow-result-main-entry-points.
p(2.0, 1.0)=(0.5, 0)
p(3.0, 1.0)=(0.5, 0)
p(2.5, 1.0) is impossible
