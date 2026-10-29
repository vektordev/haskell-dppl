p(0.5)=(0.3520653267642995, 1.0)
p(-1.0)=(0.24197072451914337, 1.0)
-- A decreasing self-call (loop (r - 1)) behind `if False`, applied to an
-- enumerated argument (1 or 2). Both arguments take the final else branch, so
-- main is a standard Normal. Was the known issue
-- decreasingRecursionRefusedAsGenerateFallback: first refused as a generate
-- fallback (ticket decreasing-recursion-refused-as-generate-fallback), then
-- failing at query time because the enumerated sum over the density-valued
-- else branch reported a mass (task enumerated-sum-over-density-body). The
-- discrete twin is conditionals/decreasingRecursionEnumeratedArgument.
