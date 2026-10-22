-- ModalityInfer admits `main` as Deterministic: `helper` ignores its argument,
-- because the inner lambda drops h1. The IR compiler's Bottom-argument Apply
-- arm refused, on the grounds that the callee "reads its value": it saw h0
-- occur in the redex `(\h1 -> 1.0) h0` and did not reduce it first.
-- Admission-oracle family 3 of fuzz-admission-over-promises; ticket
-- admitted-callee-ignores-bottom-argument. The call's law is a point at 1.0,
-- which the compiler now measures from that value (task
-- dispatch-on-law-certificates), so no binding is compiled at all.
slow
p(1.0)=(1.0, 0.0)
p(0.0) is impossible
cdf(1.0)=(1.0, 0.0)
cdf(0.5)=(0.0, 0.0)
