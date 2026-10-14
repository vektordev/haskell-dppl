-- Sibling of sceneRebuildFloatLeafSharedDrawNoCode with each slot draw-bound
-- from its own read (equivalent for a product read: its slots are
-- independent) and no arithmetic at all: slot 1 recoloured, px passed
-- through, slot 2 passed through whole. Compiles generate only. The same
-- edit over one `draw sc = readScene sym` compiles `forward`.
-- Idealized: p(Scene (Obj Red x1) Nil) = P(Obj_1) N(x1; mu1, s1) P(Nil_2).
-- Found by experiments_nest symbolic-latent-scene-editing. Docs task
-- scene-rebuild-with-float-leaf-loses-probability.
expect-failure: no-code
