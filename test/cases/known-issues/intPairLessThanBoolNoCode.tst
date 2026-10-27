-- Two enumerated Int leaves compared, returned as Bool: main has only generate.
-- Under if/then 1 else 0 it compiles forward and is exact.
-- Idealized: P(main = True) = sum_{i<j} pA(i) * pB(j).
-- Task: enumerated-int-pair-comparison-no-probability. Since 9c2f380 the probability
-- variant carries a recorded reason (set-witness, then the plan path), so this is a refused pin.
expect-failure: refused "set-valued witness construction failed"
