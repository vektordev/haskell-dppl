-- thetaAnchorInSetWitnessedCallee read through a draw-bound alias, whose name
-- `t2` the caller binds too: the anchor is materialized outside the alias's
-- binder, so it reads the alias's value, the callee's parameter, under the
-- name the engine bound it to. Docs task
-- theta-anchor-through-callee-local-binding.
p(True, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.7000000000000002, 0.0)
p(False, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.2999999999999998, 0.0)
