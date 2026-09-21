-- Found by the neural/plan-enumeration fuzz generator, though not actually
-- neural-specific -- reproduces with no `neural` declaration at all:
-- `unionMultiValues` rejects an `if` whose arms are opposite `Either`
-- constructors. The condition here is the literal `False`, so `main` always
-- evaluates to `left (left 0.0)`. Idealized: p(Left Left 0.0) = (1.0, 0).
expect-failure: broken
p(Left Left 0.0)=(1.0, 0.0)
