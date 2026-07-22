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
