-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- adt-cdf-through-tuple-answers), shrunk from replay 505. An ADT has no order,
-- so cdf() on an ADT-valued program is refused (`main = if Uniform < 0.74
-- then Box else Grid` errors at query time on the interpreter, and the
-- batched module raises its NaN diagnostic). Reached through head/fst of a
-- tuple carrying an enumerated Int, the interpreter and scalar Python
-- instead answer cdf(Box) = 0.74, and the batched module raises
-- "TypeError: '<' not supported between instances of 'str' and 'int'".
-- Pinned is the interpreter's and Python's value; the fix is expected to
-- refuse it.
backends: interpreter, python
expect-failure: wrong-result
cdf(Box)=(0.74, 0.0)
