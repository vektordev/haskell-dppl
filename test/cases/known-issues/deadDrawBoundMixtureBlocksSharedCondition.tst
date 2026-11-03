-- The (_, ANY) mask of let-bindings/drawBoundMixtureOverSharedContinuousCondition:
-- with y dead, x's binding still counts y's mixture condition as a reader and
-- no engine takes it ("no inference engine applies to the binding of 'x'").
-- Without the dead draw it is `draw x = Normal in x > 0.0`, p(True) = 0.5.
-- Verified on dev at bc08ffd. The masked query itself is fixed (pruneObservation
-- drops bindings a mask leaves dead); a dead binding written in the program is
-- docs-repo task dead-binding-argument-counts-as-reader-of-outer-binding. Docs task
-- dead-draw-bound-mixture-blocks-shared-condition-inversion.
expect-failure: refused "no inference engine applies"
p(True)=(0.5, 0.0)
p(False)=(0.5, 0.0)
