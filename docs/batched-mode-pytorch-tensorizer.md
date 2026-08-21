# Batched Mode (PyTorch tensorizer)

`batched :: Bool` (CLI `--batched`) opts into batched inference: instead of
scalar Python evaluated one query point at a time, emit branch-free
elementwise PyTorch that runs a whole `[B]`-shaped batch at once
(`torch.where` instead of a data-dependent `if`). `SPLL.IRSelectPass`
retags eligible `IRIf` nodes as `IRSelect` (both arms evaluated, combined
by a mask) before the optimizer runs — a no-op for scalar backends, which
lower it back to `IRIf`. `CodeGenPyTorchBatched.generateFunctionsBatched`
then emits tensor code over the *tensor fragment*: fixed-shape tuples of
float/int/bool, neural/enumerable constructs, and list-valued/
constructor-tagged samples via *shape-signature bucketing*
(`pythonLibBatched.bucketed` partitions a batch by structural signature and
calls the kernel once per bucket). `OpLog`/`OpDiv` route through
`safe_log`/`safe_div` so autograd doesn't NaN through the untaken arm of a
select; a refused `IRError` arm emits as a NaN `poison()` constant the
select masks away.

A call-graph guard refuses value-dependent recursion (e.g. `dice`); other
non-fragment constructs (marginal `VAny`, composite enumeration,
mismatched-shape select arms) are refused with a diagnostic naming the
construct rather than compiling to something silently wrong. Runtime lib:
`pythonLibBatched.py`.

When a group's query domain is statically finite, **dense enumeration
mode** evaluates the kernel once over the whole domain, giving a `[V]`
probability vector any query gathers into — strictly additive (ordinary
methods stay byte-identical; an unrenderable domain just yields no dense
methods). `topK` pruning is per-element (both `torch.where` arms are
always evaluated, so pruning only picks which value survives), which
covers the dense `[V]` axis for free too.

Tested by the `BatchedPython` group, gated on the `.tst` `batched`/`dense`
header tokens and a torch-enabled Python (`NEST_TORCH_PYTHON` → a venv
path → `python3`; repo convention: `~/.cache/nest/torchvenv`) — skips with
a visible note if none is found. Refusal behaviour has separate
torch-independent coverage.

`benchmarks/batched_vs_scalar.py` times the emitted code: a scalar
per-point loop against one batched call for the same `ReadNN` program
(needs a torch-enabled Python, same lookup as `BatchedPython`).
