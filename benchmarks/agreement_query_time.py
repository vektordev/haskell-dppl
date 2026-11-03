"""Per-query time of the scalar Python agreement product (task
scalar-backend-tensor-ops-lower-to-torch; numbers in
benchmarks/stressAgreementProduct.ppl).

The program is stressAgreementProduct.ppl widened to V classes, with the
networks named lmA and lmB:

    neural lmA :: (Symbol -> Int) of [0, 1, ..., V-1]
    neural lmB :: (Symbol -> Int) of [0, 1, ..., V-1]
    main ctxA ctxB =
      draw a = lmA ctxA in
      draw b = lmB ctxB in
      if a == b then right a else left ()

compiled with `-G -I` (and `--materializationBudget V` past 10000):

    stack run -- -G -I -i /tmp/poe.ppl compile -l python -o /tmp/poe.py
    python benchmarks/agreement_query_time.py /tmp/poe.py V

Each network returns a fixed random Dirichlet vector, once as a Python list
and once as a float64 torch tensor; the script prints the best-of-7 time per
query and the error against the closed form. One torch thread. Needs a
torch-enabled interpreter (NEST_TORCH_PYTHON).
"""
import importlib.util
import os
import random
import sys
import timeit

import torch

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)


def main(path, v):
    torch.set_num_threads(1)
    spec = importlib.util.spec_from_file_location("poe", path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    vec = {}
    m.lmA = lambda s: vec[s]
    m.lmB = lambda s: vec[s]
    rnd = random.Random(1)

    def dirichlet():
        g = [rnd.gammavariate(1.0, 1.0) for _ in range(v)]
        s = sum(g)
        return [x / s for x in g]

    pa, pb = dirichlet(), dirichlet()
    z = sum(x * y for x, y in zip(pa, pb))
    k = v // 3
    queries = [("Right k", m.Right(k), pa[k] * pb[k]), ("Right ANY", m.Right("ANY"), z),
               ("Left ()", m.Left(None), 1 - z)]
    for mode in ("list", "tensor"):
        if mode == "tensor":
            vec["A"] = torch.tensor(pa, dtype=torch.float64)
            vec["B"] = torch.tensor(pb, dtype=torch.float64)
        else:
            vec["A"], vec["B"] = pa, pb
        for name, q, exact in queries:
            f = lambda: m.main.forward(q, "A", "B")[0]
            val = float(f())
            n = max(3, 2000 // v) if v > 100 else 2000
            t = min(timeit.repeat(f, number=n, repeat=7)) / n
            print("%-6s V=%-6d %-10s %10.1f us   |err| %.1e" % (mode, v, name, t * 1e6, abs(val - exact)))


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]))
