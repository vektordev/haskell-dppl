-- Both comparison operands read the same enumerable latent t, so they are
-- correlated and the enumerated-bound equation (which needs independent
-- operands) does not apply. Idealized: p(True) = P(Uniform < 0.3) = 0.3. A
-- product of the operands' own laws would answer 0.321, so this pins
-- ModalityInfer's independence check in compareGround. Task
-- uniform-below-random-threshold-no-forward.
expect-failure: refused "has no closed form for its two random operands"
