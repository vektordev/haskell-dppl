-- Pinned wrong value: 0.7 phi(0.5) at dim 1. Correct: 0, impossible (the two px points differ).
expect-failure: wrong-result
p(Scene (Obj Green 0.5) (Obj Green 0.7), (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0]))=(0.24644572873500964, 1.0)
