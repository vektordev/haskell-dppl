-- docs task tuple-cdf-through-named-callee-measures-only-witnessed-slot: a
-- named callee's binding kept the single witness in integrate mode and
-- answered P(v <= 0.5) = 0.5 at (0.5, 1.0), never measuring the constant
-- second slot (2.0 <= 1.0 fails). Read once, its body is folded in through the
-- callee's own integrate function, as probability mode folds in its prob one.
p((0.5, 2.0))=(1.0, 1.0)
p((0.5, 1.0))=(0.0, 1.0)
cdf((0.5, 1.0))=(0.0, 0.0)
cdf((0.5, 3.0))=(0.5, 0.0)
cdf((1.0, 2.0))=(1.0, 0.0)
cdf((0.5, ANY))=(0.5, 0.0)
cdf((ANY, 1.0))=(0.0, 0.0)
cdf((ANY, 3.0))=(1.0, 0.0)
