-- Probe row 7 of design law-carrying-modality's evidence table, the
-- rewritten half. Its working twin, which answers correctly, is
--   main = draw x = Normal in x * 2.0 + 1.0
-- Verified at 2d50350 on dev. Pinned by task
-- rewrite-invariance-net-draw-apply-helper-alias, whose Probes group judges
-- the pair. Idealized (the twin's answer): p(1.4) = (0.1955, 1.0)
expect-failure: diagnostic "cannot extract Normal params"
