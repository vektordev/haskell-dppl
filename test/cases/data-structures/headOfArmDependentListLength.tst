-- head of a list whose length depends on a random branch. Found by the
-- batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- batched-head-of-arm-dependent-list-drops-arm), reduced by hand from
-- replay 606. Batched mode used to answer p(MkPt 0.05 True) as impossible
-- and p(MkPt ANY True) as 0.7568: its list equality required equal lengths,
-- so head's inverse Cons(x, ANY) never matched the two-element arm. Fixed
-- with task batched-refuses-list-constants-with-data; the batched value is
-- also checked directly in PythonPrelude ("a batched ANY list tail ...").
p(MkPt 0.05 True)=(0.12, 0.0)
p(MkPt ANY True)=(0.8768, 0.0)
p(MkPt 1.0 True)=(0.7568, 0.0)
