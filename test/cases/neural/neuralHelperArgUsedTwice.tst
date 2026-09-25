-- A deterministic helper `d` whose argument occurs three times in its body:
-- `d`'s probability path evaluates `m` forward, through `m`'s generate method
-- (`m_gen(c)`), since `m c` is fixed once `c` is. The batched backend refused
-- that call as "not a forward/integrate method" (task
-- batched-prob-path-calls-helper-generate); it now inlines a deterministic,
-- non-recursive generator into the prob/integ body instead.
-- d c = m c + m c - m c = m c, so p(1) = P(Red) and p(0) = P(Blue).
backends: interpreter, julia, python, batched
p(0, (2, [0.3, 0.7]))=(0.7, 0.0)
p(1, (2, [0.3, 0.7]))=(0.3, 0.0)
p(2, (2, [0.3, 0.7])) is impossible
p(1, (2, [0.9, 0.1]))=(0.9, 0.0)
p(0, (2, [1.0, 0.0])) is impossible
cdf(0, (2, [0.3, 0.7]))=(0.7, 0.0)
cdf(1, (2, [0.9, 0.1]))=(1.0, 0.0)
