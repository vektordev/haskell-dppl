-- A ReLU spelled with max. Admitted (pType Integrate), then refused by the
-- catch-all with a raw Expr dump: "found no way to convert to IR in
-- probability mode (pType Integrate): Expr {...}". max Normal 0.0 and
-- max 0.0 (Normal - 0.5) too; the if spelling of the same ReLU works.
-- Verified at b16b4d9 on dev. Docs task fuzz-admission-over-promises
-- (item 2).
-- Idealized: p(0.0) = 0.5 (atom), p(1.0) = phi(1) = 0.241971 (dim 1).
expect-failure: refused "found no way to convert to IR"
