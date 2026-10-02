-- Exact per-object counting (`++` over one read per object) when the object
-- type also carries a continuous position the count never reads (task
-- of-annotation-continuous-leaf-disables-enumeration; formerly the known-issues
-- pin ofAnnotationRealLeafCounting). The read's domain has a `Real` leaf, so it
-- is not densely enumerable; each `match (readAttrs s)` is a call of a named
-- helper straight on a read (a tagged invocation), which the plan engine now
-- takes, and `px` integrates out as a free marginal.
-- Plan per read: [Nil, Obj, Red, Green, mu, sigma] = [0.2, 0.8, 0.5, 0.5, 0, 1]
-- so q = P(Obj) * P(Green) = 0.4 per slot:
--   p(0) = 0.36, p(1) = 2 q (1 - q) = 0.48, p(2) = 0.16.
p(0, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]))=(0.36, 0.0)
p(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]))=(0.48, 0.0)
p(2, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]))=(0.16, 0.0)
p(3, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0])) is impossible
p(ANY, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]))=(1.0, 0.0)
cdf(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]))=(0.84, 0.0)
