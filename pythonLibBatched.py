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
#
# The index is clamped into range, for the same reason `safe_log`/`safe_div`
# mask their inputs: under select semantics both arms of a `torch.where` are
# evaluated, so an element whose index is out of range (the residual `c - a` in
# MNIST addition, for digit pairs that do not sum to `c`) still reaches this
# gather even though `is_member` will mask its value away. Without the clamp,
# such an element either indexes out of bounds and raises -- taking down a whole
# batch because of a value nothing reads -- or, for a negative index, silently
# wraps around and reads the wrong logit. The clamped read is discarded by the
# enclosing `where`, exactly like a masked `safe_log`.

def nn_gather(out, idx):
  idx_t = idx.long() if torch.is_tensor(idx) else torch.tensor(int(idx))
  idx_t = idx_t.clamp(0, out.shape[-1] - 1)
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

# --- structure-of-arrays lists (heterogeneous batching, M1) ------------------
# Design heterogeneous-batch-inference, Component 1. A batched list sample is a
# fixed-length linked list -- the same shape as pythonLib's InferenceList --
# whose *leaves* are [B] tensors. That representation is only well-defined when
# every sample in the batch has the same structure, which is exactly what the
# bucketing wrapper below guarantees: the batch is partitioned by structural
# signature first, so within one kernel call the list length (and any nested
# tuple/list shape) is a compile-time-uniform Python fact, and the emitted
# structural `if`s stay ordinary Python control flow over SoA data.

class InferenceList:
  def __init__(self, value=None):
    return NotImplemented

  def __len__(self):
    cnt = 0
    curr = self
    while curr is not None and isinstance(curr, ConsInferenceList):
      cnt += 1
      curr = curr.next
    return cnt

  def __iter__(self):
    curr = self
    while curr is not None and isinstance(curr, ConsInferenceList):
      yield curr.value
      curr = curr.next

  def __getitem__(self, index):
    if isinstance(index, slice):
      # Tail lists only, as in pythonLib: sample[1:] is the tail.
      if index.start > 0 and (index.stop == -1 or index.stop is None) and (index.step == 1 or index.step is None):
        current = self
        for _ in range(index.start - 1):
          current = current.next
        return current.next
      raise IndexError("Slices may only be used for tail lists")
    if index < 0:
      index += len(self)
    if index < 0 or index >= len(self):
      raise IndexError("InferenceList index out of range")
    current = self
    for _ in range(index):
      current = current.next
    return current.value

  def __eq__(self, other):
    # Length disagreement is a *structural* fact, uniform across the bucket, so
    # it answers with a plain Python bool (which `asmask` broadcasts). Equal
    # lengths compare elementwise through the leaves, like T.__eq__, giving a
    # [B] bool tensor. `sample == EmptyInferenceList()` -- the emptiness probe
    # the compiler emits -- therefore always lands in the Python-bool case.
    if not isinstance(other, InferenceList):
      return NotImplemented
    if len(self) != len(other):
      return False
    acc = True
    for a, b in zip(self, other):
      acc = (a == b) if acc is True else (acc & (a == b))
    return acc

  def prepend(self, value):
    return ConsInferenceList(value, self)

class EmptyInferenceList(InferenceList):
  def __init__(self):
    self.next = None
    self.value = None

class ConsInferenceList(InferenceList):
  def __init__(self, value, tail):
    self.value = value
    self.next = tail

def toList(xs):
  back = EmptyInferenceList()
  for x in reversed(list(xs)):
    back = ConsInferenceList(x, back)
  return back

# --- Either arms (heterogeneous batching, M2) --------------------------------
# The constructor tag is *structure*, so it is part of the bucket signature and
# uniform within a kernel call: `isinstance(x, Left)` is a plain Python bool
# there, and the arm accessor the emitted code takes is always the legal one.
# The payload is whatever the leaves are -- [B] tensors.

class Left:
  def __init__(self, val):
    self.val = val

  def __eq__(self, other):
    # Tag mismatch is structural (Python bool); matching tags compare payloads
    # elementwise, like T.__eq__ and InferenceList.__eq__.
    if not isinstance(other, Left):
      return False
    return self.val == other.val

class Right:
  def __init__(self, val):
    self.val = val

  def __eq__(self, other):
    if not isinstance(other, Right):
      return False
    return self.val == other.val

def fromLeft(l):
  if not isinstance(l, Left):
    raise Exception("Item is not a Left: " + str(l))
  return l.val

def fromRight(r):
  if not isinstance(r, Right):
    raise Exception("Item is not a Right: " + str(r))
  return r.val

# --- shape-signature bucketing (Component 1) ---------------------------------
# `bucketed(fn, samples, *args)` is the host wrapper the design calls for:
#
#   group batch by signature -> per bucket: SoA-pack leaves, run batched kernel
#   -> scatter results back to input order
#
# It costs O(#distinct shapes) kernel invocations instead of O(B), degrades
# gracefully (a fully heterogeneous batch is today's per-sample behaviour, a
# homogeneous one is a single call), and needs no cooperation from the emitted
# code: inside a bucket, structure is uniform, so the kernel's structural `if`s
# and structure-directed recursion run unchanged over [B_bucket] leaves.

def signature(v):
  # The full structural skeleton (the design's approved granularity): list
  # lengths and nested tuple shape, with every scalar leaf erased to 'x'.
  if isinstance(v, InferenceList):
    return ('L',) + tuple(signature(x) for x in v)
  if isinstance(v, T):
    return ('T', signature(v.t1), signature(v.t2))
  if isinstance(v, Left):
    return ('L?', signature(v.val))
  if isinstance(v, Right):
    return ('R?', signature(v.val))
  # An ADT value: the constructor tag *and* the field shapes. The tag must be
  # part of the key -- two constructors of the same arity are different
  # structures, and merging them into one bucket would run the wrong arm.
  # An ADT value (every emitted constructor class sets _fields, empty for a
  # nullary one): the constructor tag *and* the field shapes. The tag must be
  # part of the key -- two constructors of the same arity are different
  # structures, and merging them into one bucket would run the wrong arm.
  # Unexercised by the corpus today: the .tst value parser has no ADT literal,
  # so no corpus program can have an ADT-valued *sample*. It is here so that
  # such a sample would bucket correctly rather than silently merge.
  if hasattr(v, '_fields'):
    return ('A', type(v).__name__) + tuple(signature(f) for f in v._fields)
  return 'x'

def bucket_count(samples):
  return len(set(signature(s) for s in samples))

def _pack(vs):
  # Structure-of-arrays pack: a homogeneous list of samples becomes one sample
  # whose leaves are stacked [B] tensors.
  head = vs[0]
  if isinstance(head, InferenceList):
    return toList([_pack([s[i] for s in vs]) for i in range(len(head))])
  if isinstance(head, T):
    return T(_pack([s.t1 for s in vs]), _pack([s.t2 for s in vs]))
  if hasattr(head, '_fields'):
    return type(head)(*[_pack([s._fields[i] for s in vs])
                        for i in range(len(head._fields))])
  if isinstance(head, Left):
    return Left(_pack([s.val for s in vs]))
  if isinstance(head, Right):
    return Right(_pack([s.val for s in vs]))
  if torch.is_tensor(head) and head.dim() > 0:
    return torch.stack([astensor(v) for v in vs])
  if isinstance(head, bool):
    return torch.tensor([bool(v) for v in vs])
  if isinstance(head, int):
    return torch.tensor([int(v) for v in vs])
  return torch.tensor([float(v) for v in vs])

def _slice_arg(a, idx, total):
  # A per-point extra argument (e.g. a [B, n] neural symbol batch) is sliced to
  # the bucket; a shared/broadcast argument is passed through untouched.
  if torch.is_tensor(a) and a.dim() > 0 and a.shape[0] == total:
    return a[torch.tensor(idx)]
  return a

def _scatter(parts, idxs, total):
  # Reassemble per-bucket results into one [B] result in input order.
  head = parts[0]
  if isinstance(head, T):
    return T(_scatter([p.t1 for p in parts], idxs, total),
             _scatter([p.t2 for p in parts], idxs, total))
  if isinstance(head, InferenceList):
    return toList([_scatter([p[i] for p in parts], idxs, total) for i in range(len(head))])
  if isinstance(head, (Left, Right)):
    return type(head)(_scatter([p.val for p in parts], idxs, total))
  if hasattr(head, '_fields'):
    return type(head)(*[_scatter([p._fields[i] for p in parts], idxs, total)
                        for i in range(len(head._fields))])
  out = None
  for p, idx in zip(parts, idxs):
    t = astensor(p)
    if t.dim() == 0:
      t = t.expand(len(idx))
    if out is None:
      out = torch.empty(total, dtype=t.dtype)
    out[torch.tensor(idx)] = t.to(out.dtype)
  return out

def bucketed(fn, samples, *args):
  samples = list(samples)
  total = len(samples)
  order = []
  for i, s in enumerate(samples):
    sig = signature(s)
    for grp in order:
      if grp[0] == sig:
        grp[1].append(i)
        break
    else:
      order.append((sig, [i]))
  parts, idxs = [], []
  for _sig, idx in order:
    packed = _pack([samples[i] for i in idx])
    parts.append(fn(packed, *[_slice_arg(a, idx, total) for a in args]))
    idxs.append(idx)
  return _scatter(parts, idxs, total)
