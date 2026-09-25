-- Task shared-enumerated-latent-loses-per-slot-factorization: sharedLatentPerSlot
-- with every read hoisted into its own `draw`. Enumerated as written, the
-- stacked draws nest into the JOINT over c, o1, o2, o3 (3^4 terms here,
-- 8 * 97^N for the CLEVR program). SPLL.DrawSinking moves each o_i binding
-- into the one summand that reads it, which leaves only c shared and gives the
-- per-slot form of the unhoisted twin. Same rows as sharedLatentPerSlot; the
-- shape (no joint loop) is pinned by TestInternals.
backends: interpreter, julia, python, batched
p(0, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.2637, 0.0)
p(1, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.5279, 0.0)
p(2, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.1931, 0.0)
p(3, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.0153, 0.0)
p(4, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8])) is impossible
p(0, (2, [0.0, 1.0, 0.0]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.315, 0.0)
p(2, (2, [0.0, 1.0, 0.0]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.185, 0.0)
cdf(1, (2, [0.5, 0.3, 0.2]), (2, [0.6, 0.3, 0.1]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.1, 0.8]))=(0.7916, 0.0)
