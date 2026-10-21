-- Idealized: p(Scene ANY (Obj Green 1.0)) = 0.4 phi(0)/2 at dim 1, p(Scene ANY Nil) = 0.6.
expect-failure: broken
p(Scene ANY (Obj Green 1.0), (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0]))=(0.07978845608028655, 1.0)
p(Scene ANY Nil, (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0]))=(0.6, 0.0)
