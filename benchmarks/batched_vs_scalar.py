"""M5 perf evidence for design pytorch-tensorizer: batched vs. scalar-loop
inference on a ReadNN program, plus a torch.compile smoke test.

The scalar backend evaluates one query point at a time, so a training loop over
N points fires the network N times with batch size 1. Batched mode runs the whole
[B]-shaped batch through branch-free torch.where code in one call, and the
network once with batch size B. This script measures that difference on the same
program, same network weights, same points -- and checks both paths agree.

Usage (from the repository root):

    stack run -- -i testCases/mNistAdd.ppl compile -l python -o /tmp/mnist_scalar.py
    stack run -- -i testCases/mNistAdd.ppl compile -l python -o /tmp/mnist_batched.py --batched
    python benchmarks/batched_vs_scalar.py --scalar /tmp/mnist_scalar.py \
                                           --batched /tmp/mnist_batched.py

Requires a torch-enabled interpreter (the same one the BatchedPython test group
uses; see NEST_TORCH_PYTHON).
"""

import argparse
import os
import sys
import time

import torch
from torch import nn

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)

IMG = 784      # MNIST image, flattened
DIGITS = 10


def make_net(seed=0):
    """A small MNIST-ish classifier. Softmax output, because the emitted decoder
    reads its output as a categorical distribution over the 10 digits."""
    torch.manual_seed(seed)
    return nn.Sequential(
        nn.Linear(IMG, 128), nn.ReLU(),
        nn.Linear(128, DIGITS), nn.Softmax(dim=-1),
    ).eval()


def load(path, net, batched):
    """Exec an emitted module in its own namespace and install the network.

    The scalar and batched files declare the same names; only the shapes they
    push through the network differ ([784] vs. [B, 784]), which a plain nn
    module handles by itself.
    """
    ns = {"__name__": "emitted"}
    # The emitted boilerplate imports its runtime lib by name from the repo root.
    exec(compile(open(path).read(), path, "exec"), ns)
    ns["readMNist"] = net
    return ns["main"]


def free_net():
    """A zero-cost stand-in for the network: returns a fixed distribution of the
    right shape. Isolates the cost of the *emitted inference code* from the cost
    of the network itself, which batches well no matter what the compiler does.
    """
    base = torch.full((DIGITS,), 1.0 / DIGITS)

    def f(x):
        if x.dim() == 1:
            return base
        return base.expand(x.shape[0], DIGITS)
    return f


def timeit(fn, repeats):
    # One untimed call: torch's first dispatch on a new shape allocates and
    # caches, which otherwise lands entirely in the first measurement.
    fn()
    t0 = time.perf_counter()
    for _ in range(repeats):
        fn()
    return (time.perf_counter() - t0) / repeats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scalar", required=True)
    ap.add_argument("--batched", required=True)
    ap.add_argument("--sizes", default="1,8,64,512,4096")
    ap.add_argument("--repeats", type=int, default=3)
    args = ap.parse_args()

    sizes = [int(s) for s in args.sizes.split(",")]
    torch.set_num_threads(1)   # a training loop shares the machine; keep it honest

    for label, net in (("real net (784->128->10)", make_net()),
                       ("free net (constant)", free_net())):
        scalar_main = load(args.scalar, net, batched=False)
        batched_main = load(args.batched, net, batched=True)
        print(f"\n=== {label} ===")
        print(f"{'B':>6} {'scalar loop':>14} {'batched':>12} {'speedup':>9} {'max |diff|':>12}")

        for b in sizes:
            torch.manual_seed(1)
            imgs_a = torch.rand(b, IMG)
            imgs_b = torch.rand(b, IMG)
            targets = torch.randint(0, 2 * DIGITS - 1, (b,))

            def run_scalar():
                return [scalar_main.forward(int(targets[i]), imgs_a[i], imgs_b[i])[0]
                        for i in range(b)]

            def run_batched():
                return batched_main.forward(targets, imgs_a, imgs_b)[0]

            with torch.no_grad():
                t_s = timeit(run_scalar, args.repeats)
                t_b = timeit(run_batched, args.repeats)
                ref = torch.tensor([float(x) for x in run_scalar()])
                got = run_batched()
                diff = float((ref - got).abs().max())

            print(f"{b:>6} {t_s*1e3:>12.2f}ms {t_b*1e3:>10.2f}ms "
                  f"{t_s/t_b:>8.1f}x {diff:>12.2e}")
            if diff > 1e-4:
                print("  !! scalar and batched disagree -- benchmark is not comparing "
                      "equivalent computations")

    # torch.compile smoke test: the batched forward has no data-dependent Python
    # control flow left (every conditional is a torch.where), so it should trace
    # into a single graph with no graph breaks.
    print("\n=== torch.compile smoke test (batched forward) ===")
    net = make_net()
    batched_main = load(args.batched, net, batched=True)
    b = 512
    torch.manual_seed(1)
    imgs_a, imgs_b = torch.rand(b, IMG), torch.rand(b, IMG)
    targets = torch.randint(0, 2 * DIGITS - 1, (b,))
    try:
        import torch._dynamo as dynamo
        dynamo.reset()
        explanation = dynamo.explain(batched_main.forward)(targets, imgs_a, imgs_b)
        print(f"  graph count : {explanation.graph_count}")
        print(f"  graph breaks: {explanation.graph_break_count}")
        for reason in explanation.break_reasons:
            print(f"    break: {reason}")

        # Inductor needs a working C++ toolchain; fall back to tracing-only
        # backends so the fullgraph claim is still checked where it is not
        # available (the graph_break_count above is the claim that matters).
        for backend in ("inductor", "aot_eager", "eager"):
            try:
                dynamo.reset()
                compiled = torch.compile(batched_main.forward, fullgraph=True,
                                         backend=backend)
                with torch.no_grad():
                    ref = batched_main.forward(targets, imgs_a, imgs_b)[0]
                    got = compiled(targets, imgs_a, imgs_b)[0]
                    print(f"  fullgraph=True compiled OK on backend={backend}; "
                          f"max |diff| vs eager: {float((ref - got).abs().max()):.2e}")
                    t_e = timeit(lambda: batched_main.forward(targets, imgs_a, imgs_b),
                                 args.repeats)
                    t_c = timeit(lambda: compiled(targets, imgs_a, imgs_b), args.repeats)
                    print(f"  eager {t_e*1e3:.2f}ms -> compiled {t_c*1e3:.2f}ms "
                          f"({t_e/t_c:.1f}x)")
                break
            except Exception as e:
                print(f"  backend={backend} unavailable: {type(e).__name__}: "
                      f"{str(e).splitlines()[0]}")
    except Exception as e:
        print(f"  torch.compile unavailable or failed: {type(e).__name__}: {e}")


if __name__ == "__main__":
    main()
