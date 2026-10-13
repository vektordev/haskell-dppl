-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09; filed as
-- batched-guarded-select-over-tuple-result). The shrunk draw had 0.0 where
-- this has 2.0 (so the row is not tangled with
-- sq-inverse-drops-nonpositive-preimages); hand simplifications beyond that
-- either stop reproducing or hit the batched OpMod codegen crash instead.
-- The interpreter, scalar Python and Julia answer p(4.0) = (1.0, 0.0). The
-- batched module raises a TypeError from torch.where at every concrete
-- point: the guard of sq's inverse (`sample > 0.0`) is emitted as
-- `where_anchored(sample > 0.0, _hs0, cse_3)` over two whole
-- (prob, (dim, imposs)) tuples, which torch.where does not take.
backends: batched
expect-failure: broken
p(4.0)=(1.0, 0.0)
