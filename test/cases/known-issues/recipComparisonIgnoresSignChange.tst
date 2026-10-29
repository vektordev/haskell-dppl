-- A comparison on recip of a random value whose support crosses zero.
-- 1/x > 0.5 holds exactly for 0 < x < 2, so P = Phi(2) - 0.5 = 0.4772498681.
-- The compiler answers Phi(2) = 0.9772498681: the event is measured as
-- x < 2, as if recip were increasing and the line had no pole at 0. The
-- draw-bound spelling `draw x = Normal in recip x > 0.5` reached it too once
-- the in-place engine measured a single read (task
-- dispatch-on-law-certificates); before that it was refused. Docs-repo task
-- recip-comparison-ignores-sign-change. Verified on dev at compiler 1a09132.
-- Pinned is the interpreter's and Python's value; the idealized one is
-- p(True) = 0.4772498680518208.
backends: interpreter, python
expect-failure: wrong-result
p(True)=(0.9772498680518208, 0.0)
