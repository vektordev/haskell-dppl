-- Two syntactically identical conditions in two tuple slots are two independent
-- draws, not one shared draw (task stochastic-call-cse-unsound). The optimizer's
-- distributeIf rewrite used to hoist the shared condition out of the tuple,
-- fusing them -- generate() then only ever produced (0,0) and (1,1), silently.
-- The mixed points below are what a fused condition makes unreachable; Corpus
-- SamplingMatchesPDF is what compares them against generate().
backends: interpreter, julia, python, batched, dense
p((0, 0))=(0.25, 0.0, False)
p((0, 1))=(0.25, 0.0, False)
p((1, 0))=(0.25, 0.0, False)
p((1, 1))=(0.25, 0.0, False)
