-- A unary helper that rebuilds an object with its discrete field passed
-- through and its Float shifted, applied to two independent reads. Compiles
-- generate only. Each of these compiles `forward`: the helper applied to one
-- read; the helper without the `color` field (`Obj (px o - 1.0)`); and the
-- helper's body inlined at both call sites.
-- Idealized: p(P (Obj c1 x1) (Obj c2 x2)) = prod_i P(Obj_i) P(c_i) N(x_i + 1; mu_i, s_i).
-- Found by experiments_nest symbolic-latent-scene-editing. Docs task
-- scene-rebuild-with-float-leaf-loses-probability.
expect-failure: no-code
