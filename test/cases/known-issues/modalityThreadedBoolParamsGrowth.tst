-- A recursive walk over a neural scene threading N Bool parameters, two of
-- its four recursive calls passing a literal in the first slot. Compile cost
-- grows about 6x per parameter, all of it in ModalityInfer (every other stage
-- together is under 0.5 s): 0.30 / 1.68 / 11.5 GB allocated, 0.3 / 2.3 /
-- 16.6 s CPU at N = 1 / 2 / 3, at 8f7c501. Depth of the Scene does not
-- matter (depth 1 shown). Docs task modality-threaded-params-compile-exponential.
expect-failure: growth above polynomial 3
knob: N = 1, 2, 3
metric: alloc
cap: 4 s, 8000 MB
flags: --noIntegrate
