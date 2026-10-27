-- Int-field comparison across two cons levels of one read: generate-only even under
-- if/then 1 else 0. The product-scene spelling and a constant bound are exact.
-- Idealized: P(main=1) = P(SCons,Obj @0) * P(SCons,Obj @1) * sum_{i<j} p0(i) p1(j).
-- Task: enumerated-int-pair-comparison-no-probability.
expect-failure: refused "set-valued witness construction failed"
