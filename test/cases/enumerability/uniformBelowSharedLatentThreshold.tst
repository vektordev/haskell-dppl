p((True, True))=(0.27, 0.0)
p((True, False))=(0.03, 0.0)
p((False, True))=(0.07, 0.0)
p((False, False))=(0.63, 0.0)
-- The threshold's latent is also returned, so it is not sunk: the let
-- enumerates b and the comparison meets a fixed bound per world. Its two
-- operands still read no random variable in common, which is what
-- ModalityInfer's compareGround checks. Task
-- uniform-below-random-threshold-no-forward.
