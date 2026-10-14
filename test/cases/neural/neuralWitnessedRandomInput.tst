-- No `batched` token: Slow.BatchedPython topk-is-per-element fails (no batched mock for a non-tensor network input); docs task batched-topk-per-element-failures-on-redeclared-programs.
slow
p((0.5, 0.5))=(0.14045374, 2.0)
p((1.0, 3.0))=(0.01306423, 2.0)
p((0.5, ANY))=(0.35206533, 1.0)
