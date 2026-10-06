# Numerical/autograd probe for the two Python runtime libraries, driven by
# test/TestPythonPrelude.hs (task python-codegen-silent-precision-traps).
#
# The preludes are hand-written Python the emitted code calls into, so nothing
# in the Haskell suite otherwise constrains how they behave under torch. Three
# defects of one class were each found by an experiment noticing a wrong
# number, never by this repository:
#
#   * pythonLib functions calling math.erf/exp/log convert a tensor through
#     __float__ and return a plain float: the value is right, the autograd
#     graph is silently severed;
#   * pythonLibBatched materialised python floats in torch's default dtype
#     (float32), so a folded constant carrying the whole answer lost half its
#     digits while the emitted source showed all of them.
#
# Usage: python prelude_numerics_probe.py <mode> <project root>
#   scalar-coverage  every public pythonLib function is classified below
#                    (needs no torch -- runs everywhere)
#   scalar-autograd  every float-path pythonLib function keeps the graph, and
#                    agrees with its float arm in value and gradient
#   batched-dtype    every pythonLibBatched helper answers python floats in
#                    float64, and agrees with the scalar library in value
# Exit status 0 on success; otherwise every violation is printed.

import inspect
import math
import sys
import warnings

mode, root = sys.argv[1], sys.argv[2]
sys.path.insert(0, root)

failures = []

def fail(msg):
  failures.append(msg)

# --- classification of pythonLib's public functions -------------------------
#
# FLOAT_PATH: functions the scalar codegen can apply to a probability or a
# query value, which is where a tensor arrives when a model is trained through
# the scalar backend. Each maps to the probe points and its gradient class:
#   "real" -- a genuinely non-zero derivative somewhere, which must survive
#             (investigation scalar-pythonlib-autograd-severing-inventory's
#             Class A, plus the already-safe Class C);
#   "zero" -- piecewise constant (Class B): may return a python number, since
#             the derivative it drops is zero.
FLOAT_PATH = {
  "safe_exp":               ("real", [-3.0, -0.2, 0.0, 0.37, 2.5]),
  "safe_log":               ("real", [1e-8, 0.37, 1.0, 7.5]),
  "cumulative_normal":      ("real", [-3.0, -1.3, 0.0, 0.37, 2.2]),
  "log_cumulative_normal":  ("real", [-3.0, -1.3, 0.0, 0.37, 2.2]),
  "cumulative_uniform":     ("real", [0.01, 0.37, 0.99]),
  "log_cumulative_uniform": ("real", [0.01, 0.37, 0.99]),
  "density_normal":         ("real", [-2.0, 0.0, 0.37, 1.5]),
  "log_density_normal":     ("real", [-2.0, 0.0, 0.37, 1.5]),
  "density_uniform":        ("zero", [-0.5, 0.37, 1.5]),
  "log_density_uniform":    ("zero", [0.37]),
  "sign":                   ("zero", [-0.5, 0.37]),
}

# logsumexp takes a list; probed separately below.
LIST_FLOAT_PATH = {"logsumexp"}

# Everything else: structure, control flow and sampling, not on the float
# path -- a tensor never flows through these as a differentiable quantity
# (listProd multiplies whatever its elements are, and is tensor-transparent).
NOT_FLOAT_PATH = {
  "rand", "randn", "categorical_index", "isAny", "eq", "isclose", "throw",
  "fromLeft", "fromRight", "toList", "mapList", "indexOf", "listProd",
  "listConcat",
  "isPossible",
}

def public_functions(mod):
  return {n for n, v in vars(mod).items()
          if inspect.isfunction(v) and v.__module__ == mod.__name__
          and not n.startswith("_")}

def as_float(v):
  return float(v.detach()) if hasattr(v, "detach") else float(v)

def same_value(a, b, rel=1e-12):
  a, b = as_float(a), as_float(b)
  if math.isnan(a) or math.isnan(b):
    return math.isnan(a) and math.isnan(b)
  if math.isinf(a) or math.isinf(b):
    return a == b
  return abs(a - b) <= rel * max(1.0, abs(a), abs(b))

def scalar_coverage():
  import pythonLib
  have = public_functions(pythonLib)
  known = set(FLOAT_PATH) | LIST_FLOAT_PATH | NOT_FLOAT_PATH
  for n in sorted(have - known):
    fail("pythonLib." + n + " is not classified in prelude_numerics_probe.py: "
         "decide whether a tensor can reach it on the float path, and if so "
         "add it to FLOAT_PATH so its autograd behaviour is checked")
  for n in sorted(known - have):
    fail("prelude_numerics_probe.py classifies pythonLib." + n + ", which no longer exists")

def central_difference(f, x, h=1e-6):
  return (f(x + h) - f(x - h)) / (2 * h)

def scalar_autograd():
  import torch
  import pythonLib
  for name, (kind, points) in FLOAT_PATH.items():
    f = getattr(pythonLib, name)
    for x in points:
      ref = f(x)
      xt = torch.tensor(x, dtype=torch.float64, requires_grad=True)
      with warnings.catch_warnings():
        # math.* on a tensor warns rather than raising; a severing function is
        # caught below by its result type, not by this warning.
        warnings.simplefilter("ignore")
        r = f(xt)
      where = "pythonLib." + name + "(" + repr(x) + ")"
      if not same_value(r, ref):
        fail(where + ": tensor arm " + repr(as_float(r)) + " != float arm " + repr(ref))
      if kind == "zero":
        if torch.is_tensor(r) and r.requires_grad:
          (g,) = torch.autograd.grad(r, xt, allow_unused=True)
          if g is not None and float(g) != 0.0:
            fail(where + ": piecewise-constant function has gradient " + repr(as_float(g)))
        continue
      if not torch.is_tensor(r):
        fail(where + ": returned " + type(r).__name__ + " for a tensor argument -- the autograd graph is severed")
        continue
      if not r.requires_grad:
        fail(where + ": result is detached from its argument -- the autograd graph is severed")
        continue
      if r.dtype != torch.float64:
        fail(where + ": demoted a float64 argument to " + str(r.dtype))
      (g,) = torch.autograd.grad(r, xt)
      want = central_difference(f, x)
      if math.isfinite(want) and not same_value(g, want, rel=1e-5):
        fail(where + ": gradient " + repr(as_float(g)) + " != finite difference " + repr(want))

  # logsumexp: the log-space enumerated sum. The gradient w.r.t. each element
  # is its softmax weight; a severed inner log/exp leaves only the max
  # element's constant 1.
  xs = [-1.0, -2.5, 0.3]
  ref = pythonLib.logsumexp(xs)
  ts = [torch.tensor(v, dtype=torch.float64, requires_grad=True) for v in xs]
  r = pythonLib.logsumexp(ts)
  if not torch.is_tensor(r) or not r.requires_grad:
    fail("pythonLib.logsumexp: autograd graph severed")
  else:
    if not same_value(r, ref):
      fail("pythonLib.logsumexp: tensor arm " + repr(as_float(r)) + " != float arm " + repr(ref))
    gs = torch.autograd.grad(r, ts, allow_unused=True)
    for v, g in zip(xs, gs):
      g = 0.0 if g is None else g
      want = math.exp(v - ref)
      if not same_value(g, want, rel=1e-9):
        fail("pythonLib.logsumexp: d/dx(" + repr(v) + ") = " + repr(as_float(g)) + ", softmax weight is " + repr(want))
  # Mixed python floats and tensors (a folded constant among live terms), and
  # an all-impossible (-inf) axis, must both still answer.
  r = pythonLib.logsumexp([-math.inf, torch.tensor(-1.0, dtype=torch.float64)])
  if not same_value(r, -1.0):
    fail("pythonLib.logsumexp([-inf, t(-1)]) = " + repr(as_float(r)))
  r = pythonLib.logsumexp([torch.tensor(-math.inf, dtype=torch.float64)] * 2)
  if float(r) != -math.inf:
    fail("pythonLib.logsumexp([t(-inf)] * 2) = " + repr(as_float(r)))

def batched_dtype():
  import torch
  import pythonLib
  import pythonLibBatched as B
  if torch.get_default_dtype() != torch.float32:
    fail("probe precondition: torch's global default dtype is already " + str(torch.get_default_dtype()))
  # Materialising a python float anywhere must not truncate it.
  x = 0.1 + 1e-12   # distinguishable from 0.1 in float64, not in float32
  checks = {
    "astensor(x)": lambda: B.astensor(x),
    "_pack([x, x])": lambda: B._pack([x, x]),
    "where_anchored(True, x, 0.0)": lambda: B.where_anchored(True, x, 0.0),
    "where_anchored(False, 0.0, x)": lambda: B.where_anchored(False, 0.0, x),
    "tensor_sum([x, t(x)])": lambda: B.tensor_sum([x, torch.tensor(x, dtype=torch.float64)]),
    "tensor_sum([])": lambda: B.tensor_sum([]),
    "tensor_logsumexp([])": lambda: B.tensor_logsumexp([]),
    "poison()": lambda: B.poison(),
    "rand(3)": lambda: B.rand(3),
    "randn(3)": lambda: B.randn(3),
  }
  for what, mk in checks.items():
    try:
      t = mk()
    except Exception as ex:
      fail("pythonLibBatched." + what + " raised " + repr(ex))
      continue
    if not torch.is_tensor(t):
      fail("pythonLibBatched." + what + " returned " + type(t).__name__)
    elif t.dtype != torch.float64:
      fail("pythonLibBatched." + what + " is " + str(t.dtype) + ", not float64")
  if hasattr(B, "where_anchored"):
    # A boolean or integer select stays boolean/integer ...
    if B.where_anchored(True, True, False).dtype != torch.bool:
      fail("pythonLibBatched.where_anchored on bool arms is not bool")
    if B.where_anchored(True, 3, 4).dtype != torch.int64:
      fail("pythonLibBatched.where_anchored on int arms is not int64")
    # ... and a live tensor arm is never promoted: the net's dtype is its own.
    if B.where_anchored(True, torch.tensor([1.0], dtype=torch.float32), 0.5).dtype != torch.float32:
      fail("pythonLibBatched.where_anchored promoted a float32 tensor arm")
  if hasattr(B, "table_select"):
    # The flat form of a constant select chain answers in the kind of its
    # values exactly as the chain's where_anchored would.
    if B.table_select(torch.tensor([2, 5]), [0, 2], [0, 1], 2).dtype != torch.int64:
      fail("pythonLibBatched.table_select on int values is not int64")
    t = B.table_select(torch.tensor([2, 5]), [0, 2], [0.5, x], 0.25)
    if t.dtype != torch.float64 or t.tolist() != [x, 0.25]:
      fail("pythonLibBatched.table_select on float values gave " + repr(t))

  # The tensor twins of the scalar library's float-path functions agree with
  # it in value, not merely to float32 precision.
  for name, (_, points) in FLOAT_PATH.items():
    fb = getattr(B, name, None)
    if fb is None:
      continue
    for x in points:
      r = fb(B.astensor(x))
      where = "pythonLibBatched." + name + "(" + repr(x) + ")"
      if torch.is_tensor(r) and r.is_floating_point() and r.dtype != torch.float64:
        fail(where + " is " + str(r.dtype) + ", not float64")
      if not same_value(r, getattr(pythonLib, name)(x)):
        fail(where + " = " + repr(as_float(r)) + ", pythonLib says " + repr(getattr(pythonLib, name)(x)))

  # Generic sweep: whatever a helper is, fed python floats it must not answer
  # a float tensor in anything but float64. A new helper is covered without
  # being listed.
  for name in sorted(public_functions(B)):
    f = getattr(B, name)
    try:
      params = inspect.signature(f).parameters.values()
    except (TypeError, ValueError):
      continue
    required = [p for p in params if p.default is p.empty
                and p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)]
    if not 1 <= len(required) <= 2:
      continue
    try:
      with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        r = f(*([0.37] * len(required)))
    except Exception:
      continue   # not a float-valued helper
    if torch.is_tensor(r) and r.is_floating_point() and r.dtype != torch.float64:
      fail("pythonLibBatched." + name + " answers python floats in " + str(r.dtype))

{"scalar-coverage": scalar_coverage,
 "scalar-autograd": scalar_autograd,
 "batched-dtype": batched_dtype}[mode]()

if failures:
  print("\n".join(failures))
  sys.exit(1)
