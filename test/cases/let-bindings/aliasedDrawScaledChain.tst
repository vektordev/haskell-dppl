-- A Gaussian chain whose first step is re-bound through an alias:
-- phi(s1) * 2 phi(2 (s2 - s1)) * 2 phi(2 (s3 - s2)). The third step's |1/0.5|
-- used to be applied twice (the second step's witness path carried the third
-- step's recovery derivative; docs task
-- aliased-draw-chain-scaled-step-double-jacobian, fixed with
-- aliased-draw-scaled-sibling-double-jacobian). Found by the rewrite-invariance
-- sweep over let-bindings/gaussianTrajectory4.
p((0.0, (0.0, 0.0)))=(0.25397454373696393, 3.0)
p((0.0, (0.5, 1.0)))=(0.09343201322172633, 3.0)
