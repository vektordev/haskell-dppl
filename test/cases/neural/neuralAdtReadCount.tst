-- Two neural reads of a scene slot (`Nil | Obj color`), each mapped to a
-- 0/1 match, summed with `++`. Combining the reads makes the compiler
-- enumerate each read's domain as ADT constants (`Nil`, `Obj Red`,
-- `Obj Blue`), which the batched backend refused outright, and whose
-- `color o` accessor under the structural `isNil o` test ran eagerly on the
-- `Nil` term (task batched-backend-refuses-neural-adt-constants).
-- Logit layout: [Nil, Obj, Red, Blue]. Point A: P(match=1) = 0.8*0.25 = 0.2
-- and 0.5*0.6 = 0.3, so p(0) = 0.8*0.7, p(1) = 0.8*0.3 + 0.2*0.7, p(2) = 0.2*0.3.
backends: interpreter, julia, python, batched
p(0, (2, [0.2, 0.8, 0.25, 0.75]), (2, [0.5, 0.5, 0.6, 0.4]))=(0.56, 0.0)
p(1, (2, [0.2, 0.8, 0.25, 0.75]), (2, [0.5, 0.5, 0.6, 0.4]))=(0.38, 0.0)
p(2, (2, [0.2, 0.8, 0.25, 0.75]), (2, [0.5, 0.5, 0.6, 0.4]))=(0.06, 0.0)
p(3, (2, [0.2, 0.8, 0.25, 0.75]), (2, [0.5, 0.5, 0.6, 0.4])) is impossible
p(0, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(0.095, 0.0)
p(1, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(0.86, 0.0)
p(2, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(0.045, 0.0)
cdf(0, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(0.095, 0.0)
cdf(1, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(0.955, 0.0)
cdf(2, (2, [0.9, 0.1, 0.5, 0.5]), (2, [0.1, 0.9, 1.0, 0.0]))=(1.0, 0.0)
