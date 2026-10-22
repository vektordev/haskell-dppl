-- Found by the batched arm of prop_Fuzz_BackendsAgree (docs task
-- backend-agreement-batched-arm, 2026-10-09). The guard of sq's inverse
-- (`sample > 0.0`) selects between two whole (prob, (dim, imposs)) results
-- that are not tuple literals -- a hoisted structural block `_hs0` and a CSE
-- name -- so distributeSelects cannot split it at compile time, and batched
-- mode raised a TypeError from torch.where(Tensor, T, T). where_anchored now
-- selects two tuples leaf by leaf (task
-- batched-guarded-select-over-tuple-result).
p(4.0)=(1.0, 0.0)
