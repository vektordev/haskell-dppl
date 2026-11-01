-- Int-field comparison across two cons levels of one read (task
-- enumerated-int-pair-comparison-no-probability): generate-only even under
-- if/then 1 else 0 until the plan engine coupled two enumerated leaves (one
-- world per value of the left leaf). The scene domain is over the dense budget,
-- so this is the plan engine's path.
-- Logits per level: [Empty, SCons, Nil, Obj, Cube, Sphere, Cylinder, Red, Blue, x0..x3].
-- P(main=1) = P(SCons,Obj @0) * P(SCons,Obj @1) * sum_{i<j} p0(i) p1(j)
--           = 0.8*0.9 * 0.7*0.8 * 0.15 = 0.06048; P(main=0) the same times 0.85.
-- The rest (no object at level 0 or 1) is the accessors' failure mass, which
-- also makes the sampler throw, hence no-normalization.
no-normalization
p(1, (2, [0.2, 0.8, 0.1, 0.9, 0.5, 0.3, 0.2, 0.6, 0.4, 0.1, 0.2, 0.3, 0.4, 0.3, 0.7, 0.2, 0.8, 0.3, 0.3, 0.4, 0.5, 0.5, 0.4, 0.3, 0.2, 0.1, 0.5, 0.5, 0.5, 0.5, 0.3, 0.3, 0.4, 0.5, 0.5, 0.25, 0.25, 0.25, 0.25]))=(0.06048, 0.0)
p(0, (2, [0.2, 0.8, 0.1, 0.9, 0.5, 0.3, 0.2, 0.6, 0.4, 0.1, 0.2, 0.3, 0.4, 0.3, 0.7, 0.2, 0.8, 0.3, 0.3, 0.4, 0.5, 0.5, 0.4, 0.3, 0.2, 0.1, 0.5, 0.5, 0.5, 0.5, 0.3, 0.3, 0.4, 0.5, 0.5, 0.25, 0.25, 0.25, 0.25]))=(0.34272, 0.0)
