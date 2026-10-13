-- Both comparison operands read the same enumerable latent t, so they are
-- correlated and the enumerated-bound equation (which needs independent
-- operands) does not apply. Idealized: p(True) = P(Uniform < 0.3) = 0.3. A
-- product of the operands' own laws would answer 0.321, so this pins
-- ModalityInfer's independence check in compareGround. Task
-- uniform-below-random-threshold-no-forward. Since task
-- engine-applicability-as-data the binding of t is refused first: its body
-- is not conditional, so enumeration does not apply, and no other engine
-- does either, so t is bound sample-only.
expect-failure: refused "no inference engine applies to the binding of 't'"
