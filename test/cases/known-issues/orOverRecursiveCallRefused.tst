-- `||` whose right operand is the recursive call. ModalityInfer types the
-- `or` Integrate, then IRCompiler's catch-all refuses ex's probability with
-- "found no way to convert to IR in probability mode (pType Integrate):"
-- followed by a raw Expr dump. The `if A then True else ex (n - 1)` spelling
-- answers 0.657; `&&` over a recursive call fails the same way. Found by the
-- publication-exploration C1 pilot (W1/W2). Verified at b16b4d9 on dev. Docs
-- task fuzz-admission-over-promises (item 2).
-- Idealized: p(True) = 1 - 0.7^3 = 0.657.
expect-failure: refused "found no way to convert to IR"
