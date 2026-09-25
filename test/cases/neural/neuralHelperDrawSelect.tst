-- A query-select over two neural scene reads, with the predicate factored
-- into a helper `sel`: the enumerated probability path evaluates `sel a` and
-- `sel b` forward through `sel_gen`, which the batched backend refused (task
-- batched-prob-path-calls-helper-generate). `sel` draws nothing, so it is now
-- inlined into the batched kernel.
-- Logit layout: [Nil, Obj, Cube, Sphere, Red, Blue]. Point A:
-- P(sel a) = 0.6*0.5 = 0.3, P(sel b) = 0.8*0.25 = 0.2, so
-- p(Red) = 0.3*0.7 + 0.7*0.2*0.1 = 0.224.
backends: interpreter, julia, python, batched
p(Red, (2, [0.4, 0.6, 0.5, 0.5, 0.7, 0.3]), (2, [0.2, 0.8, 0.25, 0.75, 0.1, 0.9]))=(0.224, 0.0)
p(Blue, (2, [0.4, 0.6, 0.5, 0.5, 0.7, 0.3]), (2, [0.2, 0.8, 0.25, 0.75, 0.1, 0.9]))=(0.776, 0.0)
p(Red, (2, [1.0, 0.0, 0.5, 0.5, 0.7, 0.3]), (2, [0.0, 1.0, 1.0, 0.0, 1.0, 0.0]))=(1.0, 0.0)
p(Blue, (2, [1.0, 0.0, 0.5, 0.5, 0.7, 0.3]), (2, [0.0, 1.0, 1.0, 0.0, 1.0, 0.0])) is impossible
