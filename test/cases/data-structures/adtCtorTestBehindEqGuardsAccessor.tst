p(0.5)=(1.0, 1.0)
p(0.2)=(1.0, 1.0)
-- The batched module used to raise "No match in field accessor 'mu'" at every
-- concrete point: the constructor test reaches codegen as `True == isOne(h)`,
-- and the guard on the `mu h` arm is the zero test of that arm's weight
-- (`isclose(if cse then 1.0 else 0.0, 0.0)`). Neither was recognised as
-- structural, so the arm became an eager torch.where that read the field of
-- the wrong constructor. h is read through a helper's parameter, since a
-- known-point law would fold `isOne h` to a constant. Found by the batched arm
-- of prop_Fuzz_BackendsAgree; task batched-ctor-test-behind-eq-evaluates-accessor.
