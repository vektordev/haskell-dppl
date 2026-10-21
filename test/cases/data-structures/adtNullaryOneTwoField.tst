-- No `batched` token: Slow.BatchedPython topk-is-per-element fails (torch.where(Tensor, T, T) TypeError); docs tasks batched-topk-per-element-failures-on-redeclared-programs, batched-guarded-select-over-tuple-result.
slow
p(Zero)=(0.2, 0.0, False)
p(One 0.5)=(0.4, 1.0, False)
p(Two 0.5 0.25)=(0.4, 2.0, False)
p(One 0.9)=(0.4, 1.0, False)
p(Two 0.1 0.9)=(0.4, 2.0, False)
p(One ANY)=(0.4, 0.0, False)
p(Two ANY 0.25)=(0.4, 1.0, False)
p(Two ANY ANY)=(0.4, 0.0, False)
