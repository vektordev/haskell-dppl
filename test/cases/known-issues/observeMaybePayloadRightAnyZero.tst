-- Verified at commit 8bb0a44 on dev: a Maybe whose Just payload is itself the
-- draw-bound Maybe m (the shape `observe (observe Normal (> 0)) isRight`
-- desugars to). The point query is right -- p(Right Right 0.5) = phi(0.5) at
-- dim 1 -- but the marginal over the payload is silently zero: p(Right ANY)
-- should be P(v > 0) = 0.5, and generate does produce Right (Right _) about half
-- the time. p(Left ()) = 0.5 is right, so the two rows sum to 0.5, not 1.
-- The discrete-payload twin (`right 1.0` instead of `right v`) crashes in
-- unionMultiValues instead -- the known fuzzUnionMultiValuesOppositeEither shape.
-- Idealized: p(Right ANY) = (0.5, 0.0). The row below pins the wrong value.
expect-failure: wrong-result
p(Right Right 0.5)=(0.35206533, 1.0)
p(Left ())=(0.5, 0.0)
p(Right ANY)=(0.0, 0.0)
