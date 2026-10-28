# Checks of the recursion memo (CLI --memoRecursion; docs task
# recursive-prob-calls-not-shared-across-branches), driven by
# test/TestMemoRecursion.hs.
#
#   python memo_recursion_probe.py <repo root> <module dir> <check>
#
# The Haskell side compiles the programs below through the real binary into
# <module dir>, as <name>.py (no flag), <name>_memo.py (--memoRecursion) and
# <name>_memo_b.py (--memoRecursion --batched). Each check raises on failure,
# so exit 0 means it passed. The call counts count executions of a recursive
# method's body (not calls answered from the table): they pin the cost, which
# nothing else in the suite can see.

import functools
import math
import os
import sys

ROOT, DIR, CHECK = sys.argv[1], sys.argv[2], sys.argv[3]
sys.path.insert(0, ROOT)

import torch  # noqa: E402  (the emitted modules import torch.nn.Module)

torch.set_default_dtype(torch.float64)


def fail(msg):
  raise SystemExit("memo_recursion_probe " + CHECK + ": " + msg)


def load(name, extra=None):
  path = os.path.join(DIR, name + ".py")
  ns = dict(extra or {})
  ns["__name__"] = "nest_" + name
  with open(path) as f:
    exec(compile(f.read(), path, "exec"), ns)
  return ns


def count_body(ns, cls, method):
  # Replace a memoised method by the memo wrapped around a counting copy of
  # its body: the count is then the number of table misses.
  wrapped = getattr(ns[cls], method)
  body = getattr(wrapped, "__wrapped__", None)
  if body is None:
    fail(cls + "." + method + " is not memoised (no @nest_memo)")
  counter = [0]

  @functools.wraps(body)
  def counted(*args):
    counter[0] += 1
    return body(*args)

  setattr(ns[cls], method, ns["nest_memo"](counted))
  return counter


def close(a, b, rel, what):
  a, b = float(a), float(b)
  if not abs(a - b) <= rel * max(abs(a), abs(b), 1e-300):
    fail(what + ": " + repr(a) + " != " + repr(b) + " (rel " + repr(rel) + ")")


def normal_pdf(x, mu):
  return math.exp(-0.5 * (x - mu) ** 2) / math.sqrt(2 * math.pi)


# --- the HMM repro ------------------------------------------------------------

HMM_TRANS = {0: (0.7, 0.3), 1: (0.4, 0.6)}


def hmm_forward(obs):
  # The forward recursion by hand: f(i, s) = P(gen s = obs[i:]).
  @functools.lru_cache(maxsize=None)
  def f(i, s):
    if i == len(obs):
      return 0.1
    return 0.9 * sum(HMM_TRANS[s][t] * normal_pdf(obs[i], 2.0 * t) * f(i + 1, t) for t in (0, 1))
  return f(0, 0)


def obs_seq(n):
  return [0.3 * ((i * 7) % 5) - 0.2 for i in range(n)]


def check_hmm():
  plain, memo = load("hmm"), load("hmm_memo")
  calls = count_body(memo, "Gen", "forward")
  for n in (0, 1, 4, 16):
    calls[0] = 0
    obs = obs_seq(n)
    r = memo["main"].forward(memo["toList"](obs))
    close(r[0], hmm_forward(obs), 1e-12, "hmm n=" + str(n) + " against the hand forward recursion")
    if calls[0] > 2 * n + 1:
      fail("hmm n=" + str(n) + ": " + str(calls[0]) + " executions of gen.forward, more than 2n+1")
  # The unmemoised module agrees (n = 10: 2047 calls there).
  obs = obs_seq(10)
  a = plain["main"].forward(plain["toList"](obs))
  b = memo["main"].forward(memo["toList"](obs))
  close(a[0], b[0], 1e-14, "hmm n=10, with and without the memo")
  if a[1][0] != b[1][0] or a[1][1] != b[1][1]:
    fail("hmm n=10: dims/flags differ with the memo: " + repr((a[1][0], a[1][1])) + " vs " + repr((b[1][0], b[1][1])))
  # Integrate is memoised too.
  close(plain["main"].integrate(plain["toList"](obs))[0], memo["main"].integrate(memo["toList"](obs))[0],
        1e-14, "hmm cdf n=10, with and without the memo")


# --- canFinish (the lookahead's surrogate) -------------------------------------

def can_finish_dp(pEnd, pOpen, pClose, n, k):
  @functools.lru_cache(maxsize=None)
  def f(n, k):
    if n < 0:
      return 0.0
    if k == 0:
      return 1.0 if n == 0 else 0.0
    rest = pOpen * f(n + 1, k - 1) + (1 - pOpen) * (pClose * f(n - 1, k - 1) + (1 - pClose) * f(n, k - 1))
    return pEnd * (1.0 if n == 0 else 0.0) + (1 - pEnd) * rest
  return f(n, k)


def reachable(n, k):
  seen, todo = set(), [(n, k)]
  while todo:
    s = todo.pop()
    if s in seen:
      continue
    seen.add(s)
    m, j = s
    if m >= 0 and j > 0:
      todo += [(m + 1, j - 1), (m - 1, j - 1), (m, j - 1)]
  return len(seen)


def check_canfinish():
  plain, memo = load("canfinish"), load("canfinish_memo")
  calls = count_body(memo, "CanFinish", "forward")
  args = (0.1, 0.3, 0.4, 2)
  for k in (50,):
    calls[0] = 0
    r = memo["main"].forward(True, *args, k)
    close(r[0], can_finish_dp(*args, k), 1e-12, "canFinish k=" + str(k) + " against a hand DP")
    if calls[0] > reachable(2, k):
      fail("canFinish k=" + str(k) + ": " + str(calls[0]) + " executions, more than the "
           + str(reachable(2, k)) + " reachable (n, k) pairs")
  r = memo["main"].forward(False, *args, 50)
  close(r[0], 1 - can_finish_dp(*args, 50), 1e-12, "canFinish k=50, False")
  for k in (0, 1, 6):
    close(plain["main"].forward(True, *args, k)[0], memo["main"].forward(True, *args, k)[0], 1e-14,
          "canFinish k=" + str(k) + ", with and without the memo")


# --- the rung-2 noisy channel ----------------------------------------------------
# Alphabet {0, 1, 2, 3}; `nbr c` is uniform over two confusable letters.

NBR = {0: (1, 2), 1: (0, 2), 2: (1, 3), 3: (2, 0)}


def channel_likelihood(cs, obs, pSub, pDel, pIns):
  n, m = len(cs), len(obs)

  def sub(c, o):
    return (1 - pSub) * (1.0 if o == c else 0.0) + pSub * 0.5 * NBR[c].count(o)

  @functools.lru_cache(maxsize=None)
  def f(i, j):
    if i == n:
      return 1.0 if j == m else 0.0
    r = pDel * ((1 - pIns) * f(i + 1, j) + (pIns / 4 * f(i + 1, j + 1) if j < m else 0.0))
    if j < m:
      e = (1 - pDel) * sub(cs[i], obs[j])
      r += e * ((1 - pIns) * f(i + 1, j + 1) + (pIns / 4 * f(i + 1, j + 2) if j + 1 < m else 0.0))
    return r
  return f(0, 0)


def check_corrupt():
  plain, memo = load("corrupt"), load("corrupt_memo")
  calls = count_body(memo, "Corrupt", "forward")
  ps = (0.2, 0.1, 0.15)
  cs = [(3 * i + 1) % 4 for i in range(20)]
  obs = list(cs)
  obs[3] = NBR[obs[3]][0]
  del obs[7]
  obs.insert(12, 2)
  del obs[15]
  tl = memo["toList"]
  r = memo["main"].forward(tl(obs), tl(cs), *ps)
  close(r[0], channel_likelihood(cs, obs, *ps), 1e-12, "corrupt, word length 20, against the alignment DP")
  bound = (len(cs) + 1) * (len(obs) + 1)
  if calls[0] > bound:
    fail("corrupt, word length 20: " + str(calls[0]) + " executions, more than the " + str(bound) + " (i, j) pairs")
  short, sobs = cs[:6], [1, 0, 3, 3, 2]
  close(plain["main"].forward(tl(sobs), tl(short), *ps)[0], memo["main"].forward(tl(sobs), tl(short), *ps)[0],
        1e-14, "corrupt, word length 6, with and without the memo")


# --- several entries into one cycle ------------------------------------------------

def check_walk():
  memo = load("walk_memo")
  r = memo["main"].forward(memo["toList"]([1.0, 1.0]))
  close(r[0], 0.5 * 0.7 ** 2 * 0.3 + 0.5 * 0.4 ** 2 * 0.6, 1e-12, "walk, two entries with p = 0.3 and 0.6")
  plain, memo = load("walkp"), load("walkp_memo")
  q = plain["toList"]([1.0, 1.0])
  for p1, p2 in ((0.3, 0.6), (0.6, 0.6)):
    close(memo["main"].forward(q, p1, p2)[0], plain["main"].forward(q, p1, p2)[0], 1e-14,
          "walkp " + repr((p1, p2)) + " as floats")
  # The rates as tensors carrying gradients: keyed by identity, so the two
  # entries never share, and each one's pass-through tensor shares within it.
  grads = []
  for ns in (plain, memo):
    a = torch.tensor(0.3, requires_grad=True)
    b = torch.tensor(0.6, requires_grad=True)
    r = ns["main"].forward(q, a, b)[0]
    close(r, 0.1215, 1e-12, "walkp with tensor rates")
    r.backward()
    grads.append((float(a.grad), float(b.grad)))
  close(grads[0][0], grads[1][0], 1e-12, "walkp d/dp with and without the memo")
  close(grads[0][1], grads[1][1], 1e-12, "walkp d/dq with and without the memo")
  calls = count_body(memo, "Walk", "forward")
  a = torch.tensor(0.3, requires_grad=True)
  memo["main"].forward(memo["toList"]([1.0] * 6), a, a)
  if calls[0] > 7:
    fail("walkp with one tensor for both rates: " + str(calls[0]) + " executions of walk.forward, more than 7")


# --- gradients through a neural transition ----------------------------------------

def check_neural():
  torch.manual_seed(0)
  w0 = torch.randn(3, 2, requires_grad=True)
  w1 = torch.randn(3, 2, requires_grad=True)
  nets = {"t0": lambda x: torch.softmax(x @ w0, 0), "t1": lambda x: torch.softmax(x @ w1, 0)}
  x = torch.tensor([0.5, -1.0, 2.0])
  obs = obs_seq(12)
  results = []
  for name in ("nhmm", "nhmm_memo"):
    ns = load(name, nets)
    w0.grad = None
    w1.grad = None
    nll = -torch.log(ns["main"].forward(ns["toList"](obs), x)[0])
    nll.backward()
    results.append((float(nll), w0.grad.clone(), w1.grad.clone()))
  (l0, a0, b0), (l1, a1, b1) = results
  close(l0, l1, 1e-12, "neural HMM -log p with and without the memo")
  if not (torch.allclose(a0, a1, rtol=1e-9, atol=1e-12) and torch.allclose(b0, b1, rtol=1e-9, atol=1e-12)):
    fail("neural HMM gradient differs with the memo: " + repr((a0, a1, b0, b1)))


# --- the batched backend ---------------------------------------------------------

def check_batched():
  b, s = load("hmm_memo_b"), load("hmm_memo")
  seqs = [obs_seq(8), [x + 0.1 for x in obs_seq(8)], obs_seq(5)]
  r = b["bucketed"](b["main"].forward, [b["toList"](o) for o in seqs])
  for i, o in enumerate(seqs):
    close(r[0][i], s["main"].forward(s["toList"](o))[0], 1e-12, "batched hmm, sample " + str(i))
  b = load("canfinish_memo_b")
  calls = count_body(b, "CanFinish", "forward")
  r = b["bucketed"](b["main"].forward, [True, False], 0.1, 0.3, 0.4, 2, 30)
  close(r[0][0], can_finish_dp(0.1, 0.3, 0.4, 2, 30), 1e-12, "batched canFinish, True")
  close(r[0][1], 1 - can_finish_dp(0.1, 0.3, 0.4, 2, 30), 1e-12, "batched canFinish, False")
  if calls[0] > reachable(2, 30):
    fail("batched canFinish k=30: " + str(calls[0]) + " executions, more than the reachable pairs")
  b = load("walk_memo_b")
  r = b["bucketed"](b["main"].forward, [b["toList"]([1.0, 1.0])])
  close(r[0][0], 0.1215, 1e-12, "batched walk")


{"hmm": check_hmm, "canfinish": check_canfinish, "corrupt": check_corrupt, "walk": check_walk,
 "neural": check_neural, "batched": check_batched}[CHECK]()
