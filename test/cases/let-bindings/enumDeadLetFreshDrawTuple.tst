backends: interpreter, julia, python, batched
p((Left 5.605168764426174, 2))=(0.5, 0.0)
p((Left 5.605168764426174, 1))=(0.5, 0.0)
p((Left 5.605168764426174, ANY))=(1.0, 0.0)
p((Left 5.0, 2)) is impossible
-- Formerly known-issues/fuzzLetWitnessGenerateBackedFallback (found by the
-- let/set-witness fuzz generator, ~7% of its crashes). The enumerated `v0` is
-- dead; the body's `if Uniform < 0.5 then 2 else 1` is a fresh draw that used
-- to be compiled forward and refused as generate-backed. It is now measured
-- by the ordinary rules (task enum-let-latent-gates-fresh-draw).
