-- Two calls of one reading helper with the same arguments are two independent
-- reads: each call's traversal opens its own offset range, and a
-- specialization that opened a read is never memoized, so the second call does
-- not reuse the first's worlds (task plan-neural-read-inside-specialized-function).
-- The Float field keeps Object off the enumeration engine, so the plan
-- traversal answers. isObj a ~ 0.7, each isObj b ~ 0.4:
-- P(T,T) = 0.7*0.4^2 + 0.3*0.6^2 = 0.22 (one shared read would give 0.46),
-- P(T,F) = P(F,T) = 0.7*0.4*0.6 + 0.3*0.6*0.4 = 0.24,
-- P(F,F) = 0.7*0.6^2 + 0.3*0.4^2 = 0.3.
p((True, True), (2, [0.3, 0.7, 0.5, 0.5, 0.0, 1.0]), (2, [0.6, 0.4, 0.5, 0.5, 0.0, 1.0]))=(0.22, 0.0)
p((True, False), (2, [0.3, 0.7, 0.5, 0.5, 0.0, 1.0]), (2, [0.6, 0.4, 0.5, 0.5, 0.0, 1.0]))=(0.24, 0.0)
p((False, True), (2, [0.3, 0.7, 0.5, 0.5, 0.0, 1.0]), (2, [0.6, 0.4, 0.5, 0.5, 0.0, 1.0]))=(0.24, 0.0)
p((False, False), (2, [0.3, 0.7, 0.5, 0.5, 0.0, 1.0]), (2, [0.6, 0.4, 0.5, 0.5, 0.0, 1.0]))=(0.3, 0.0)
p((True, ANY), (2, [0.3, 0.7, 0.5, 0.5, 0.0, 1.0]), (2, [0.6, 0.4, 0.5, 0.5, 0.0, 1.0]))=(0.46, 0.0)
