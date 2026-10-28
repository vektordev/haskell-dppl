-- ModalityInfer admits `main` as PNormal: `helper` ignores its argument,
-- because the inner lambda drops h1. The IR compiler's Bottom-argument Apply
-- arm used to refuse because h0 occurs in the redex `(\h1 -> Normal) h0`; the
-- dead-binding test now ignores an occurrence that only feeds a redex whose
-- lambda drops it. Task admitted-callee-ignores-bottom-argument.
p(0.0)=(0.3989422804014327, 1.0)
cdf(0.0)=(0.5, 0.0)
