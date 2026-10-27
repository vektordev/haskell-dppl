-- The shape llm-decoding-operator-stack's row 5 needs: a soft guard
-- `Uniform < cut` conjoined with an equality against a neural read. Same
-- refusal as uniformConjunctParamEqualityRefused (the neural read is not what
-- matters). Idealized: p(True | cut, t) = cut * P(lmAnti ctxC = t).
-- Docs task uniform-conjunct-with-param-equality-refused.
expect-failure: refused "found no way to convert to IR in probability mode"
