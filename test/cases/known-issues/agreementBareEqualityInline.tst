-- Idealized values: identical to agreementBareEqualityLetBound.tst (the two
-- programs denote the same distribution). Verified at haskell-dppl 92365e7
-- (dev): compiling throws "More than one probabilistic argument found".
expect-failure: broken
p(True,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.29, 0.0)
p(False,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.71, 0.0)
