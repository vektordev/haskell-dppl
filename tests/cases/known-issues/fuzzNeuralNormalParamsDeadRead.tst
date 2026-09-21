-- Found by the neural/plan-enumeration fuzz generator (rare, ~2/300 draws):
-- `toIRNormalParams` cannot extract Normal params from a
-- `PNormal` expression reached through nested tuple/Either projections, even
-- though the (unused) neural read `s` is dead. `snd (snd (right False,
-- (False, Normal)))` structurally reduces to `Normal`. Idealized: the
-- standard normal density, p(0.0) = (0.3989422804014327, 1.0). Pinned as
-- `crash` rather than `broken` since a correct row would need the mock-NN
-- logit-envelope parameter shape rather than a bare Symbol literal, which is
-- not confirmed here.
expect-failure: crash
