-- Division by a literal zero: generate draws Uniform / 0.0 = Infinity on
-- every run, so the comparison is always False, but probability answers
-- P(True) = 1.0 (and the CDF of Uniform / 0.0 is 1.0 even at -0.5). The
-- pinned row is the known-wrong value; whatever x / 0 should mean, the two
-- variants of one program must agree. Docs task
-- zero-divisor-probability-disagrees-with-generate.
expect-failure: wrong-result
backends: interpreter
p(True)=(1.0, 0.0)
