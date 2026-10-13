-- Found while reducing a batched-arm disagreement of prop_Fuzz_BackendsAgree
-- (docs task backend-agreement-batched-arm, 2026-10-09; filed as
-- sq-inverse-drops-nonpositive-preimages). sq's only inverse is the positive
-- square root, applicable where the observation is > 0, so a query on sq of
-- a value that can be zero or negative silently loses that mass:
-- p(1.0) answers 0.25 (the -1.0 preimage is dropped) and p(0.0) answers
-- impossible (0 is outside the inverse's domain). Every backend agrees, so
-- the agreement fuzzer cannot see it. Idealized values below.
backends: interpreter, python
expect-failure: broken
p(1.0)=(0.75, 0.0)
p(0.0)=(0.25, 0.0)
