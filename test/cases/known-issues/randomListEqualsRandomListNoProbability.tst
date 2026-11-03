-- Verified at haskell-dppl dev 437799d5. Idealized: sum over v of
-- p(coin xs = v) p(coin ys = v): 1/4 for two lengths-2 lists, 0 for different
-- lengths. Task random-list-equality-over-runtime-lists-no-probability.
expect-failure: refused "found no way to convert to IR in probability mode"
p(True, [1, 2], [3, 4])=(0.25, 0.0)
p(True, [1, 2], [3])=(0.0, 0.0)
