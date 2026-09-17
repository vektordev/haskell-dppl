-- `a + 1 == a` has no solution, so the agreement branch is unreachable for
-- every class and all the mass is on the rejected branch. Independent of the
-- expert's logits, which is why the literal vector below is arbitrary.
p(Right 0,(2, [0.5, 0.3, 0.2])) is impossible
p(Right 1,(2, [0.5, 0.3, 0.2])) is impossible
p(Right 2,(2, [0.5, 0.3, 0.2])) is impossible
p(Left (),(2, [0.5, 0.3, 0.2]))=(1.0, 0.0)
p(Right ANY,(2, [0.5, 0.3, 0.2])) is impossible
