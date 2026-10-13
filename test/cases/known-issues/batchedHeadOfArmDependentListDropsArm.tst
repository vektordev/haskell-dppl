-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- batched-head-of-arm-dependent-list-drops-arm), reduced by hand from
-- replay 606. A silent wrong answer, not a crash: the batched module answers
-- p(MkPt 0.05 True) as impossible and p(MkPt ANY True) as 0.7568, dropping
-- the 0.12 of the arm whose list has two elements. The interpreter and
-- scalar Python answer the rows below. With a one-element list in both arms
-- the batched answer is right.
backends: batched
expect-failure: broken
p(MkPt 0.05 True)=(0.12, 0.0)
p(MkPt ANY True)=(0.8768, 0.0)
