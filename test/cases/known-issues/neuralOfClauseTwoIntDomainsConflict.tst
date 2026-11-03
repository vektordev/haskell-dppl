-- Verified at haskell-dppl dev 437799d5: compile returns a graceful Left,
-- "conflicting PartitionPlan annotations for type TInt", so no crash or
-- refused-variant shape fits. Idealized: readD a + readE b with
-- readD = [0.2, 0.5, 0.3], readE = [0.1, 0.2, 0.3, 0.4]:
-- p(0) = 0.2 * 0.1 = 0.02, p(5) = 0.3 * 0.4 = 0.12.
-- Task neural-of-clause-registers-layout-type-wide.
expect-failure: broken
no-normalization
p(0, (2, [0.2, 0.5, 0.3]), (3, [0.1, 0.2, 0.3, 0.4]))=(0.02, 0.0)
p(5, (2, [0.2, 0.5, 0.3]), (3, [0.1, 0.2, 0.3, 0.4]))=(0.12, 0.0)
