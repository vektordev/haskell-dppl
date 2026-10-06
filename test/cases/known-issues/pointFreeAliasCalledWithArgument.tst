-- Verified at bd494ae (dev): calling a point-free alias of a top-level
-- function with an argument crashes forward chaining. `main x = coin x` and
-- `main = alias 0.3`-free spellings compile; so does `alias x = coin x`.
-- Idealized: p(True, 0.3) = 0.3, p(False, 0.3) = 0.7. Found while building
-- per-value queries (task per-value-query-over-enumerated-slot), whose
-- __point helper is eta-expanded to avoid this shape. Docs task
-- point-free-alias-called-with-argument-crashes-forward-chaining.
expect-failure: diagnostic "to be a Lambda"
p(True, 0.3)=(0.3, 0.0)
p(False, 0.3)=(0.7, 0.0)
