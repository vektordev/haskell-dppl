-- Task shared-enumerated-latent-loses-per-slot-factorization: a predicate
-- delivered as data (`readQ`), shared by `draw` across independent per-slot
-- reads -- the CLEVR "exist with a predicate input" shape. Given c the three
-- slots are independent, so the count is a Poisson-binomial mixed over c:
-- p(k) = sum_c P(c) * PB_k(P(o1 = c), P(o2 = c), P(o3 = c)).
-- Compiles to one loop over c with the per-slot convolution inside it; the
-- curried helper call `match c (readC s)` used to have no enumeration path at
-- all ("found no way to convert to IR"). Its hoisted twin is
-- sharedLatentPerSlotHoisted, which must agree row for row.
backends: interpreter, julia, python, batched
p(0, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.2637, 0.0)
p(1, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.5279, 0.0)
p(2, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.1931, 0.0)
p(3, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.0153, 0.0)
p(4, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8])) is impossible
p(0, (2, [0.0, 1.0, 0.0]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.315, 0.0)
p(2, (2, [0.0, 1.0, 0.0]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.185, 0.0)
cdf(1, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.7916, 0.0)
