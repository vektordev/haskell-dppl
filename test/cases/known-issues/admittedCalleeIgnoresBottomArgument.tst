-- ModalityInfer admits `main` as Deterministic: `helper` ignores its argument,
-- because the inner lambda drops h1. The IR compiler's Bottom-argument Apply
-- arm still refuses, on the grounds that the callee "reads its value": it sees
-- h0 occur in the redex `(\h1 -> 1.0) h0` and does not reduce it first. With
-- `helper h0 = 1.0` the program compiles. Idealized: p(1.0) = (1.0, dim 0),
-- p(0.0) is impossible. Admission-oracle family 3 of
-- fuzz-admission-over-promises; ticket admitted-callee-ignores-bottom-argument.
expect-failure: refused "the argument has pType Bottom"
