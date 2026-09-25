backends: interpreter, julia, python, batched
p(Right 1)=(0.18, 0.0)
p(Right 2)=(0.28, 0.0)
p(Left 11)=(0.42, 0.0)
p(Left 12)=(0.12, 0.0)
-- The agreement shape (two enumerated latents compared with `==`) whose else
-- arm reads the INNER variable below its root: `left (b + 10)`. Agreement
-- fusion must decline it (the off-diagonal sum does not factor), but its
-- "arm reads the inner variable" test looked only at the arm's root node, so
-- it fused and the emitted body read an unbound `b` ("Variable b not
-- declared"). Values from the joint enumeration: P(Left 11) = P(a=2, b=1) =
-- 0.7 * 0.6. Found while working task enum-let-latent-gates-fresh-draw.
