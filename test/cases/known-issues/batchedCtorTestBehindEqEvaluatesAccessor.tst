-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- batched-ctor-test-behind-eq-evaluates-accessor). The interpreter, scalar
-- Python and Julia answer p(0.5) = (1.0, 1.0): h is a Two, so the Uniform arm
-- is taken. The batched module raises "No match in field accessor 'mu'" at
-- every concrete point (p(ANY) is answered before the body runs): the
-- condition reaches it as `True == isOne(h)`, which the structural test does
-- not recognise, so the select evaluates both arms and a hoisted
-- `isAny(mu(h))` reads the field of the wrong constructor.
backends: batched
expect-failure: broken
p(0.5)=(1.0, 1.0)
