-- Hand-derived expectations for the agreement (product-of-experts) fusion.
--
-- camNN   = [0.5, 0.3, 0.2]   (non-uniform)
-- depthNN = [0.1, 0.6, 0.3]   (non-uniform, and ordered differently, so a
--                              fusion that silently paired the wrong indices
--                              would not coincide with the right answer)
--
-- Conditioning on agreement keeps the elementwise product:
--   p(Right k) = P_cam(k) * P_depth(k)
--     k=0: 0.5 * 0.1 = 0.05
--     k=1: 0.3 * 0.6 = 0.18
--     k=2: 0.2 * 0.3 = 0.06
--   p(Right ANY) = Z = 0.05 + 0.18 + 0.06 = 0.29      (the fusion evidence)
--   p(Left ())   = 1 - Z = 0.71                        (the off-diagonal mass)
--
-- The Left row is the one that exercises the off-diagonal subtraction
-- (Sb - pb(j)), which is the numerically delicate half of the fusion; the
-- Right rows exercise the diagonal, i.e. the elementwise product itself.
-- A second, swapped pair of vectors pins that the product is not symmetric by
-- accident. The final block is a one-hot expert against a spread one: agreement
-- can only land on class 1, so the whole kept mass is that single product, the
-- two dead classes are structurally impossible, and the complement is exact.
p(Right 0,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.05, 0.0)
p(Right 1,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.18, 0.0)
p(Right 2,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.06, 0.0)
p(Right ANY,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.29, 0.0)
p(Left (),(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.71, 0.0)
p(Left ANY,(2, [0.5, 0.3, 0.2]),(2, [0.1, 0.6, 0.3]))=(0.71, 0.0)
p(Right 0,(2, [0.1, 0.6, 0.3]),(2, [0.5, 0.3, 0.2]))=(0.05, 0.0)
p(Right 1,(2, [0.1, 0.6, 0.3]),(2, [0.5, 0.3, 0.2]))=(0.18, 0.0)
p(Right 2,(2, [0.1, 0.6, 0.3]),(2, [0.5, 0.3, 0.2]))=(0.06, 0.0)
p(Right 0,(2, [0.0, 1.0, 0.0]),(2, [0.25, 0.5, 0.25])) is impossible
p(Right 1,(2, [0.0, 1.0, 0.0]),(2, [0.25, 0.5, 0.25]))=(0.5, 0.0)
p(Right 2,(2, [0.0, 1.0, 0.0]),(2, [0.25, 0.5, 0.25])) is impossible
p(Right ANY,(2, [0.0, 1.0, 0.0]),(2, [0.25, 0.5, 0.25]))=(0.5, 0.0)
p(Left (),(2, [0.0, 1.0, 0.0]),(2, [0.25, 0.5, 0.25]))=(0.5, 0.0)
