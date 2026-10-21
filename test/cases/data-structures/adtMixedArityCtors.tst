-- No `batched` token: Slow.BatchedPython topk-is-per-element fails (torch.where(Tensor, T, T) TypeError); docs tasks batched-topk-per-element-failures-on-redeclared-programs, batched-guarded-select-over-tuple-result.
slow
p(Dot 0.5)=(0.3, 1.0, False)
p(Pair 0.5 0.25)=(0.7, 2.0, False)
p(Dot 0.9)=(0.3, 1.0, False)
p(Pair 0.1 0.9)=(0.7, 2.0, False)
p(Dot ANY)=(0.3, 0.0, False)
p(Pair ANY 0.25)=(0.7, 1.0, False)
p(Pair ANY ANY)=(0.7, 0.0, False)
