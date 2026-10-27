-- Two enumerated Int leaves compared, returned as Bool: main has only generate.
-- Under if/then 1 else 0 it compiles forward and is exact.
-- Idealized: P(main = True) = sum_{i<j} pA(i) * pB(j).
-- Task: enumerated-int-pair-comparison-no-probability.
expect-failure: refused "set-valued witness construction failed"
