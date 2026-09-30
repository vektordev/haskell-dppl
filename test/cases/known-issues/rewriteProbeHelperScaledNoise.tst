-- Probe row 5 of design law-carrying-modality's evidence table, the
-- rewritten half. Its working twin, which answers correctly, is
--   main = draw x = Uniform in (x, x * Normal)
-- Verified at 2d50350 on dev. Pinned by task
-- rewrite-invariance-net-draw-apply-helper-alias, whose Probes group judges
-- the pair. Idealized (the twin's answer): p((0.5, 0.2)) = (0.7365, 2.0)
expect-failure: no-code
