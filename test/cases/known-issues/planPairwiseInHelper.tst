-- planEnumContPair with the comparison moved into a helper function. Inline,
-- `fst p < snd p` answers Phi(-1/sqrt(5)) = 0.327360 at mu=(0,1),
-- sigma=(1,2). Through `before`, ModalityInfer types main Bottom and the
-- probability function is silently absent: compareGround's plan exemption is
-- keyed on hasReadNN over the *declaration*, and `before` contains no ReadNN,
-- so its two family-free Integrate operands type SampleOnly. Residue of task
-- comparison-closed-form-verdict-for-plan-leaves (the coarse per-declaration
-- flag); found by design clevr-position-experiments' arm-A readiness probe.
expect-failure: no-code
