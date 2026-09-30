-- Probe row 1 of design law-carrying-modality's evidence table, the
-- rewritten half. Its working twin, which answers correctly, is
--   main = draw x = Normal in (x, x + 1.0)
-- Verified at 2d50350 on dev. Pinned by task
-- rewrite-invariance-net-draw-apply-helper-alias, whose Probes group judges
-- the pair. Idealized (the twin's answer): p((0.3, 1.3)) = (0.3814, 1.0)
expect-failure: diagnostic "tagged invocation"
