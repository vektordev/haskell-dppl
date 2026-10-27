-- A conjunction of a fresh `Uniform < 0.5` and an equality between a
-- deterministic parameter and an enumerated draw has no probability function:
-- toIRInference's catch-all at the `and`. `||` and the swapped conjunct order
-- refuse the same way; `(Uniform < 0.5) && (c < t)` and the nested
-- `if Uniform < 0.5 then t == c else False` compile. Idealized:
-- p(True | t = 1) = 0.5 * 0.5 = 0.25. Docs task
-- uniform-conjunct-with-param-equality-refused (found by
-- experiments_nest llm-decoding-operator-stack, row 5).
expect-failure: refused "found no way to convert to IR in probability mode"
