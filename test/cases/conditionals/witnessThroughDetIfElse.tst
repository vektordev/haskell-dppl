-- A point witness recovered through an if-then-else whose condition is
-- deterministic (task witness-through-deterministic-if-over-list-arms): each
-- arm is inverted on its own and the condition selects the chain. The
-- condition is false, so the value is x : [x]: p([a, a]) = phi(a), dim 1.
-- An ANY in the head slot stays a runtime refusal: the observation-mask
-- variants stop at an if root.
p([0.5, 0.5])=(0.35206533, 1.0)
p([0.0, 0.0])=(0.39894228, 1.0)
p([0.5, ANY])=(0.35206533, 1.0)
p([0.5, 0.6]) is impossible
p([0.5]) is impossible
p([]) is impossible
