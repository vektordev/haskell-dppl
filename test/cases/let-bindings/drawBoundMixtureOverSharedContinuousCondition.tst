-- A continuous mixture bound with `draw y = ...` whose condition reads a shared
-- continuous draw x, returned next to a comparison on that same x. `y` is read
-- once, with no binder on the way, so the in-place engine measures the mixture
-- at the read (task dispatch-on-law-certificates), as the inline spelling
-- `(x > 0.0, if x > 0.0 then Normal + 1.0 else Normal)` compiles. Before it,
-- probability mode was refused, "no inference engine applies to the binding
-- of 'x'" (docs-repo task
-- draw-bound-mixture-over-shared-continuous-condition-refused; was a
-- known-issues pin). The integrate variant is still refused (the set-valued
-- witness of a correlated tuple has no CDF).
--   p((True, 1.5)) = 0.5 * N(1.5; 1, 1) = 0.17603266338214976 (dim 1)
--   p((False, 0.0)) = 0.5 * N(0; 0, 1) = 0.19947114020071635 (dim 1)
-- Found by experiments_nest systems-benchmarking-chapter (benchmark 3, model M3).
-- The (_, ANY) mask leaves `y` dead in the pruned body; the pruning drops the
-- binding, so x's binding sees one reader (docs-repo task
-- dead-draw-bound-mixture-blocks-shared-condition-inversion).
--   p((True, ANY)) = p(x > 0) = 0.5 (dim 0)
p((True, 1.5))=(0.17603266338214976, 1.0)
p((False, 0.0))=(0.19947114020071635, 1.0)
p((True, ANY))=(0.5, 0.0)
p((False, ANY))=(0.5, 0.0)
p((ANY, 1.5))=(0.24079146121509565, 1.0)
