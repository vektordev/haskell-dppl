-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- cdf-fst-of-nested-tuple-indexes-any), reduced by hand from replay 429141.
-- cdf() of `fst` of a tuple whose dropped component is itself a tuple fails
-- at query time on every backend: the dropped component is marginalised as
-- ANY, and the compiled cdf then indexes into it. Interpreter: "Type error:
-- Expression of Snd is not a tuple: VAny"; Python and batched: "TypeError:
-- '<' not supported between instances of 'str' and 'int'". With a scalar
-- second component (`(2, 3)`) it answers. The batched arm saw it as a
-- disagreement because batched evaluates both arms of a select: under a
-- dead arm (`if isLeft (left ..) then 0 else <this>`) the interpreter
-- answers and batched raises. Idealized values below.
backends: interpreter, python, batched
expect-failure: broken
cdf(0)=(0.85, 0.0)
cdf(2)=(1.0, 0.0)
