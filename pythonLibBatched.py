# Batched (tensor) runtime library for the PyTorch tensorizer backend
# (design pytorch-tensorizer, milestone M2).
#
# The scalar backend (pythonLib.py) works on Python floats: math.exp, random,
# linked lists, `if`. The batched backend feeds a whole batch of query points
# through branch-free, elementwise code (torch.where instead of `if`), so every
# helper here is the tensor twin of its pythonLib counterpart: the same formula,
# vectorised, taking and returning `[B]`-shaped tensors (scalars broadcast).
#
# Batch layout is structure-of-arrays: fixed tuple structure stays a Python `T`
# object whose leaves are `[B]` tensors, so the tuple helper is shared verbatim
# with the scalar lib.

import math
import torch

# --- distribution densities / cumulatives (tensor formulas) -----------------
# These are the exact vectorisations of pythonLib's hand-rolled scalar formulas.

def density_uniform(x):
  # 1 on [0,1], 0 elsewhere.
  return ((x >= 0.0) & (x <= 1.0)).to(_dtype(x))

def cumulative_uniform(x):
  return torch.clamp(astensor(x), 0.0, 1.0)

def density_normal(x):
  return torch.exp(-(x * x) / 2.0) / math.sqrt(2.0 * math.pi)

def cumulative_normal(x):
  return (1.0 + torch.erf(astensor(x) / math.sqrt(2.0))) / 2.0

def sign(x):
  return torch.sign(astensor(x))

# --- sampling (batched generate, milestone M4) -------------------------------
# The scalar twins (pythonLib's rand()/randn()) draw one Python float each; here
# every call draws a whole batch at once, shape [n]. A random `if` in generate
# mode becomes the same select machinery as prob/integ (torch.where): both arms
# draw independently for the whole batch, so an element gets one arm's fresh
# draw exactly as the scalar generate's taken branch would -- the untaken arm's
# draw is simply discarded, not reused, so this is a correct (if slightly
# wasteful) elementwise mixture.

def rand(n):
  return torch.rand(n)

def randn(n):
  return torch.randn(n)

# --- gradient-safe unsafe ops (double-where masking) -------------------------
# In batched mode both arms of a torch.where run over the whole batch, so an
# unsafe op (log of a non-positive value, division by zero) in an *untaken* arm
# produces a correct-but-discarded value yet a NaN *gradient*: autograd flows
# through the untaken branch, and 0 (the where mask) * inf (the op's derivative
# at the singularity) = NaN, which poisons the whole backward pass. The standard
# fix is the "double where": mask the op's input to a harmless dummy inside its
# safe domain, so its local derivative stays finite; the enclosing where then
# discards the harmless value. The compiler emits these for every OpLog/OpDiv
# (design pytorch-tensorizer, M3). On the taken (in-domain) elements the result
# is identical to the plain op, so forward values are unchanged.

def safe_log(x):
  xt = astensor(x)
  safe = xt > 0
  return torch.where(safe, torch.log(torch.where(safe, xt, torch.ones_like(xt))),
                     torch.full_like(xt, float('-inf')))

def safe_div(a, b):
  bt = astensor(b)
  safe = bt != 0
  return torch.where(safe, astensor(a) / torch.where(safe, bt, torch.ones_like(bt)),
                     torch.full_like(bt, float('nan')))

# --- poison: an IRError arm as a selected-away sentinel ----------------------
# A refusal/error arm (IRError) has no batched value; it is emitted as a NaN
# poison constant that the enclosing torch.where selects away on every element
# that does not hit the error. NaN is a constant (no grad), so it never causes a
# NaN gradient the way an unsafe op does; and a poison that *does* survive
# selection into the output shows up as NaN there, caught by the value
# differential (design pytorch-tensorizer, M3).

def poison():
  return torch.tensor(float('nan'))

# --- elementwise predicates --------------------------------------------------

def isclose(a, b):
  # Elementwise |a - b| <= tol, returning a bool tensor. Mirrors pythonLib's
  # scalar isclose tolerance.
  return torch.abs(astensor(a) - astensor(b)) <= 1e-9

# --- helpers -----------------------------------------------------------------
# astensor has no leading underscore so `from pythonLibBatched import *` exports
# it: generated code calls it to coerce a Python-bool mask into a broadcastable
# tensor before torch.where.

def astensor(x):
  return x if torch.is_tensor(x) else torch.tensor(float(x))

def asmask(x):
  # Coerce a torch.where condition to a bool tensor. Tensor comparison results
  # are already bool; a batch-independent Python-bool mask (e.g. a folded
  # constant) becomes a 0-d bool tensor that broadcasts against the arms.
  return x if torch.is_tensor(x) else torch.tensor(bool(x))

def _dtype(x):
  return x.dtype if torch.is_tensor(x) else torch.get_default_dtype()

# --- neural: gather a per-element logit slot ---------------------------------
# A neural decoder reads `logits[sample]`: for each batch element, the logit
# slot selected by that element's (integer) sample. `out` is the [B, n] logit
# tensor, `idx` a [B] integer tensor; the result is the [B] tensor of selected
# logits. (A constant slot is emitted inline as out[..., i]; this handles the
# data-dependent index.)

def nn_gather(out, idx):
  idx_t = idx.long() if torch.is_tensor(idx) else torch.tensor(int(idx))
  if idx_t.dim() == 0:
    return out[..., idx_t]
  return out[torch.arange(out.shape[0]), idx_t]

# --- enumeration membership -------------------------------------------------
# `x in {vals}` as an elementwise [B] bool mask (e.g. "is the residual c - a a
# valid digit?" in MNIST addition). x is evaluated once by the caller and passed
# in; vals is the compile-time-unrolled enumeration.

def is_member(x, vals):
  xt = astensor(x)
  mask = torch.zeros_like(xt, dtype=torch.bool)
  for v in vals:
    mask = mask | (xt == v)
  return mask

# --- tuple (structure-of-arrays leaf carrier) --------------------------------
# Identical to pythonLib.T; a fixed tuple whose leaves are [B] tensors.

class T:
  def __init__(self, t1, t2):
    self.t1 = t1
    self.t2 = t2

  def __eq__(self, other):
    # Structure-of-arrays tuple equality is elementwise: two batches of tuples
    # are equal per element iff every leaf is. Returns a [B] bool tensor (the
    # leaves recurse through this method for nested tuples).
    if not isinstance(other, T):
      return NotImplemented
    return (self.t1 == other.t1) & (self.t2 == other.t2)

  def __getitem__(self, index):
    if index == 0:
      return self.t1
    if index == 1:
      return self.t2
    raise ValueError("Tuple only has index 0 and 1")
