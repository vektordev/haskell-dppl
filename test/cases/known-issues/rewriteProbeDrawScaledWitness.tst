-- Probe row 9 of design law-carrying-modality's evidence table, the
-- rewritten half. Its working twin, which answers correctly, is
--   main = draw x = Uniform in (x, x * 2.0 + Normal)
-- Verified at 2d50350 on dev. Pinned by task
-- rewrite-invariance-net-draw-apply-helper-alias, whose Probes group judges
-- the pair. Idealized (the twin's answer): p((0.3, 1.0)) = (0.3683, 2.0)
expect-failure: diagnostic "found no way to convert to IR"
