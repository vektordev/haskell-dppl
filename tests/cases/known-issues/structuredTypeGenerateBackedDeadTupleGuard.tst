-- Found by the structured-type fuzz generator: the
-- generate-backed-prob guard fires on `Uniform < 0.327`, even though that
-- randomness lives in a tuple component `fst` provably discards. Reducing
-- the source: `head [Uniform] = Uniform`, `fst (-6.76, Uniform < 0.327) =
-- -6.76` (deterministic), so `main = Uniform < -6.76`, always False since
-- Uniform's support is [0,1]. Idealized: p(True) = (0.0, 0), p(False) =
-- (1.0, 0). As of the doc's 2026-09-16 correction the raw-error half of this
-- was already fixed elsewhere -- what remains is a graceful-but-wrong
-- refusal, hence `broken` rather than `diagnostic`/`crash`.
expect-failure: broken
p(True)=(0.0, 0.0)
p(False)=(1.0, 0.0)
