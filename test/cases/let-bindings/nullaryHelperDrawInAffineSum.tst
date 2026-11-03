-- A helper without parameters whose body is a draw read twice, used inside
-- an affine expression: g is N(0, 2), so main is N(1, 4). The affine algebra
-- enters the reference as the call with no arguments it is and the draw as
-- a binding; the scalar extractor could resolve the name but not the draw
-- behind it (task gaussian-catch-all-dispatch-on-codegen-law).
p(1.5)=(0.0989594, 1.0)
p(1.0)=(0.0997356, 1.0)
cdf(1.0)=(0.5, 0.0)
cdf(5.0)=(0.8413447, 0.0)
