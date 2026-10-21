-- Scalar Python emitted the cumulative's materialized cell list, whose cells
-- carry CSE lets, as a comprehension iterable with walruses in it, which
-- CPython refuses to compile (task
-- backends-agree-python-walrus-in-comprehension-iterable; found by
-- prop_Fuzz_BackendsAgree). The middle factor is always 3 and the last always
-- 1, so the product is 6 or 3, each with probability 0.5.
p(6)=(0.5, 0.0)
p(3)=(0.5, 0.0)
p(2) is impossible
cdf(3)=(0.5, 0.0)
cdf(5)=(0.5, 0.0)
cdf(6)=(1.0, 0.0)
