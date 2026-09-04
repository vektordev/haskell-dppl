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

# --- runtime NaN guard (task batched-adt-cdf-refusal-becomes-nan) -----------
# A poison is meant to be selected away by an enclosing torch.where before it
# reaches a caller. That invariant does not always hold: an ADT-valued
# program's cdf() body (SPLL.IRCompiler.compareValueExpr's TADT case -- an ADT
# has no order to integrate along) is an IRError with nothing above it to
# select from, so the poison reaches the top-level return unmasked. Without
# this guard that surfaces as a plain NaN, indistinguishable from a genuine
# floating-point bug.
#
# The compiler routes every emitted forward/integrate/generate return through
# this function (SPLL.CodeGenPyTorchBatched.batchedBlock's 'ctx' parameter),
# so a NaN reaching any of them raises here instead. The message cannot say
# *which* of the two causes fired -- that would need the provenance an already
# NaN-valued float has lost -- but it gives the two live possibilities: a
# malformed floating-point operation upstream, or an unmasked poison(), most
# commonly a cdf() query on an ADT-valued program (compareValueExpr has no
# case for an ADT's order because there isn't one -- use p() instead).
def _has_nan(x):
  if torch.is_tensor(x):
    return bool(torch.isnan(x).any())
  if isinstance(x, T):
    return _has_nan(x.t1) or _has_nan(x.t2)
  if isinstance(x, float):
    return math.isnan(x)
  # int/bool/ADT instances/etc. carry no float to be NaN.
  return False

def check_result(x, ctx):
  if _has_nan(x):
    raise ValueError(
      ctx + ": result is NaN. This is either a malformed floating-point "
      "operation, or an unmasked poison() -- a refused computation (most "
      "commonly cdf() on an ADT-valued program, which has no order to "
      "integrate along; use p() instead) reaching the output because nothing "
      "selected it away.")
  return x

# --- elementwise predicates --------------------------------------------------

# Safety margin for isclose's tolerance, in ULPs of the looser operand dtype.
# A witness value is commonly reconstructed by one or more chained
# subtractions (x = observed - y), each losing on the order of one ULP of
# precision relative to the dtype actually in play -- so this has to absorb a
# short chain of those, not just one, while staying far below the magnitude
# of a genuine mismatch (a different branch/constructor, not roundoff).
#
# Calibrated against two corpus pairs that bound it from opposite sides, at
# float32 (eps ~1.19e-7): 'floatEquality' needs a *rejection* at a ~1e-6
# absolute difference around magnitude 0.3 (0.1+0.2 vs 0.299999/0.300001), and
# 'letWitnessedTupleFpUlp'/'letWitnessedEitherFpUlp' need an *acceptance* of a
# ~1.5e-8 subtraction residual around magnitude 0.2-0.9. 8 ULPs sits in that
# window with margin on both sides (~2.9e-7 at magnitude 0.3, comfortably
# under the 1e-6 rejection and comfortably over the 1.5e-8 residual) -- do not
# raise this without rechecking 'floatEquality' can still tell 0.299999/
# 0.300001 apart from 0.3.
_ISCLOSE_ULPS = 8

def isclose(a, b):
  # Elementwise |a - b| <= tol, returning a bool tensor. The tolerance used
  # to be a flat constant copied from pythonLib's scalar float64 tolerance
  # (1e-9), which sits *below one float32 ULP*: the batched runtime packs
  # query samples as float32 by default (see astensor/_pack), so a
  # subtraction-based witness check could never pass there -- task
  # batched-isclose-tolerance-below-float32-ulp. The tolerance here instead
  # tracks the dtype and magnitude actually being compared: a few ULPs of the
  # looser input dtype, scaled by the operands' own magnitude and floored at
  # that dtype's own eps -- not at 1.0, which would hand every sub-unit
  # comparison the same oversized tolerance and blind 'floatEquality' to a
  # genuine ~1e-6 mismatch -- so a near-zero comparison still gets a tolerance
  # rather than one that collapses to exactly zero.
  at = astensor(a)
  bt = astensor(b)
  eps = max(torch.finfo(at.dtype).eps, torch.finfo(bt.dtype).eps)
  scale = torch.maximum(torch.abs(at), torch.abs(bt)).clamp(min=eps)
  tol = _ISCLOSE_ULPS * eps * scale
  return torch.abs(at - bt) <= tol

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
# A neural read-logits network reads `logits[sample]`: for each batch element, the logit
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

# --- tensors (design ir-tensor-values) --------------------------------------
# A rank-1 tensor reaches emitted batched code as a Python list of [B] tensors
# -- one entry per element of a statically-known extent E. The list is what a
# BMap produces, because a map's body is arbitrary IR that has to be evaluated
# once per element; the vectorization opportunity is in the *consumers* below,
# which stack the list into one [E, B] tensor and run a single kernel over it
# instead of E-1 sequential ones.
#
# That stack is the "tensor of primitive lowers to a real tensor"
# specialization: here an element is a [B] tensor, so it always applies. A
# zero-extent axis reduces to the operator identity, and a lone element needs
# no stack at all.

def _tensor_stack(xs):
  # [E, B] from a list of [B] tensors. Elements that are Python scalars (a
  # folded constant arm) are broadcast up against the tensor elements, so a
  # partially-folded axis still stacks.
  ts = [x for x in xs if torch.is_tensor(x)]
  if not ts:
    return torch.stack([astensor(x) for x in xs])
  ref = ts[0]
  return torch.stack([x if torch.is_tensor(x) else torch.full_like(ref, float(x))
                      for x in xs])

def tensor_sum(xs):
  if not xs:
    return torch.tensor(0.0)
  if len(xs) == 1:
    return xs[0]
  return _tensor_stack(xs).sum(0)

def tensor_logsumexp(xs):
  if not xs:
    return torch.tensor(-math.inf)
  if len(xs) == 1:
    return xs[0]
  return torch.logsumexp(_tensor_stack(xs), 0)

def tensor_index(xs, idx):
  # Read one element per batch position: xs is the axis (length E, each [B]),
  # idx a [B] integer tensor choosing which element each position reads. One
  # gather over the [E, B] stack, rather than an E-arm torch.where cascade that
  # evaluates every arm.
  #
  # The index is clamped for the same reason nn_gather's is: under select
  # semantics an out-of-range position still reaches this read even though the
  # enclosing mask discards its value.
  if not xs:
    raise Exception("tensor_index on a zero-extent axis")
  stacked = _tensor_stack(xs)
  idx_t = idx.long() if torch.is_tensor(idx) else torch.tensor(int(idx))
  idx_t = idx_t.clamp(0, stacked.shape[0] - 1)
  if idx_t.dim() == 0:
    return stacked[idx_t]
  return stacked.gather(0, idx_t.unsqueeze(0).expand(1, stacked.shape[1])).squeeze(0)

# --- tuple (structure-of-arrays leaf carrier) --------------------------------
# Identical to pythonLib.T; a fixed tuple whose leaves are [B] tensors.

# --- ANY (design heterogeneous-batch-inference, Component 3/M4) -------------
# ANY-ness is a structural marker, exactly like a list length or a constructor
# tag (M1/M2): whether a given slot of the sample is a wildcard is part of its
# bucket *signature*, so within one bucket a slot is either always-ANY or
# always-concrete, never a per-element mix. That is what lets `isAny` answer a
# plain Python bool (no per-element mask tensor needed) and what lets `signature`
# below key on it the same way it already keys on length/tag. Mirrors
# pythonLib.py's two ANY spellings exactly, so a sample built by the scalar
# value renderer ('SPLL.CodeGenPyTorch.pyVal') is valid batched-sample syntax
# unchanged: a bare wildcard is the string "ANY" (`pyVal VAny`), a wildcard
# list is 'AnyInferenceList()' (`pyVal (VList AnyList)`).

def isAny(x):
  if x == "ANY":
    return True
  if isinstance(x, AnyInferenceList):
    return True
  return False

def eq(o1, o2):
  # A nested ANY is a wildcard (matches anything at that position) -- the
  # bucket-uniform counterpart of pythonLib.py's eq(). A *bare* top-level ANY
  # is never compared this way: it is intercepted by a structural isAny check
  # upstream (mirrors 'SPLL.IRCompiler.mkDeepAnyCheck'/'tolerateAny'), the same
  # invariant the scalar/interpreter backends already rely on.
  if isAny(o1) or isAny(o2):
    return True
  return o1 == o2

class T:
  def __init__(self, t1, t2):
    self.t1 = t1
    self.t2 = t2

  def __eq__(self, other):
    # Structure-of-arrays tuple equality is elementwise: two batches of tuples
    # are equal per element iff every leaf is. Returns a [B] bool tensor (the
    # leaves recurse through this method for nested tuples). A leaf that is a
    # bucket-uniform ANY wildcard (M4) compares equal via 'eq' rather than
    # torch's own (possibly erroring) comparison against a non-tensor.
    if not isinstance(other, T):
      return NotImplemented
    return eq(self.t1, other.t1) & eq(self.t2, other.t2)

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
    # lengths compare elementwise through the leaves via 'eq' (M4: a leaf may be
    # a bucket-uniform ANY wildcard), giving a [B] bool tensor. `sample ==
    # EmptyInferenceList()` -- the emptiness probe the compiler emits --
    # therefore always lands in the Python-bool case.
    if not isinstance(other, InferenceList):
      return NotImplemented
    if len(self) != len(other):
      return False
    acc = True
    for a, b in zip(self, other):
      acc = eq(a, b) if acc is True else (acc & eq(a, b))
    return acc

  def prepend(self, value):
    return ConsInferenceList(value, self)

class EmptyInferenceList(InferenceList):
  def __init__(self):
    self.next = None
    self.value = None

# A whole list that is a wildcard (design heterogeneous-batch-inference, M4):
# the batched twin of pythonLib.py's AnyInferenceList, matching its shape (no
# `.next`/`.value`) so 'pyVal (VList AnyList)' -- "AnyInferenceList()" -- is
# valid syntax against this library unchanged. Bucketed like any other shape
# ('signature' below); never iterated (nothing this length-0-looking, so a
# stray '==' against a concrete list falls through 'InferenceList.__eq__''s
# length check rather than an 'isAny' short-circuit -- reachable only if a
# comparison skips the compiler's own isAny guard, the same backstop
# 'pythonLib.py' documents for its own AnyInferenceList).
class AnyInferenceList(InferenceList):
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
    # elementwise via 'eq' (M4: the payload may be a bucket-uniform ANY
    # wildcard), like T.__eq__ and InferenceList.__eq__.
    if not isinstance(other, Left):
      return False
    return eq(self.val, other.val)

class Right:
  def __init__(self, val):
    self.val = val

  def __eq__(self, other):
    if not isinstance(other, Right):
      return False
    return eq(self.val, other.val)

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
  # ANY-ness (M4) is itself a structural marker, checked before every other
  # case: an 'AnyInferenceList' is also an 'InferenceList' (len 0, same as
  # Empty) and would otherwise silently collide with the empty-list bucket.
  if isAny(v):
    return 'ANY'
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
  # whose leaves are stacked [B] tensors. An ANY-marked slot (M4) is bucket-
  # uniform by construction -- every sample in this call shares 'signature',
  # so every element of 'vs' here is the *same* wildcard object -- and is
  # passed through unchanged rather than stacked, exactly like a structural
  # tag. Checked first for the same reason 'signature' checks it first.
  head = vs[0]
  if isAny(head):
    return head
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
  if head is None:
    # Unit payload (e.g. Left ()'s val, from `Nothing = left ()`): no
    # per-element data to stack, so the packed leaf stays a single None
    # rather than a [B] tensor. A kernel that reaches this arm at all
    # branches on the tag alone (isinstance(sample, Left/Right)) and never
    # indexes into a unit payload, so nothing downstream needs it shaped.
    return None
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

# --- dense enumeration mode (Component 2, M3) --------------------------------
# When the *query* domain is finite -- the program returns one of V statically
# known values -- batching query points is the wrong axis: evaluate the kernel
# once with the whole domain as the batch, giving the [V] probability vector,
# and answer any query by gathering into it. The [V] axis here is the ordinary
# *batch* axis, so nothing inside the kernel changes and enumeration the program
# does internally (IREnumSum) is untouched: dense mode sits above it, not
# instead of it.
#
# Cost: O(V) kernel work independent of B, so it wins when B > V (or when the
# caller reuses the vector across batches) and loses otherwise, structurally the
# same crossover batching itself has. That is why the emitted `forward` is
# unchanged and `forward_at` dispatches on the two sizes rather than the
# compiler committing to one path.
#
# Deliberately *not* cached: the vector depends on thetas and network weights,
# and nothing in the emitted class observes those changing, so an implicit cache
# would silently serve stale values -- and a stale autograd graph -- after every
# parameter update, which is precisely the training loop this exists for. A
# caller that wants amortisation holds the tensor itself.

def denskey(v):
  # A hashable structural rendering of a sample value, used to look a query up
  # in the domain. Mirrors `signature` but keeps the leaves, since here it is
  # the value and not just the shape that selects the slot. An ANY wildcard
  # (M4) has no single domain slot -- it is a marginal over (potentially) the
  # whole domain, not a point in it -- so it gets a key no real domain value
  # can ever produce (every domain entry is a finite concrete value), which
  # makes it a guaranteed miss and routes it through the existing off-domain
  # fallback below rather than crashing on 'float(\"ANY\")'.
  if isAny(v):
    return ('ANY',)
  if isinstance(v, InferenceList):
    return ('L',) + tuple(denskey(x) for x in v)
  if isinstance(v, T):
    return ('T', denskey(v.t1), denskey(v.t2))
  if isinstance(v, Left):
    return ('L?', denskey(v.val))
  if isinstance(v, Right):
    return ('R?', denskey(v.val))
  if hasattr(v, '_fields'):
    return ('A', type(v).__name__) + tuple(denskey(f) for f in v._fields)
  if torch.is_tensor(v):
    return denskey(v.item())
  if isinstance(v, bool):
    return ('b', v)
  return ('n', float(v))

def dense_positions(domain):
  return {denskey(v): i for i, v in enumerate(domain)}

def gather_dense(dense, idx):
  # Index every leaf of a nested result structure -- (prob, (dim, imposs)) and
  # friends -- with the same [B] index tensor, turning the [V] vector into the
  # [B] answer. A 0-d leaf (a folded constant dim/flag) broadcasts instead.
  if isinstance(dense, T):
    return T(gather_dense(dense.t1, idx), gather_dense(dense.t2, idx))
  if isinstance(dense, InferenceList):
    return toList([gather_dense(x, idx) for x in dense])
  if isinstance(dense, (Left, Right)):
    return type(dense)(gather_dense(dense.val, idx))
  if hasattr(dense, '_fields'):
    return type(dense)(*[gather_dense(f, idx) for f in dense._fields])
  t = astensor(dense)
  if t.dim() == 0:
    return t.expand(len(idx))
  return t[idx]

# The measured crossover, on a scalar domain with an already-packed [B] sample
# tensor (so index lookup is pure torch): dense+gather is 0.9x the direct kernel
# at B=16, 1.0x at B=256, 1.4x at B=4096 and 4.8x at B=65536 on `coin`. It is
# kernel-dependent -- a more expensive body moves it down -- so this is a
# conservative default, not a claim about every program.
#
# Note the marshalled path (a Python *list* of sample values) never reaches the
# crossover on small kernels: `denskey` per sample is O(B) Python and outweighs
# the O(V) torch saving. That path therefore stays direct unless forced, and the
# real amortisation idiom is a caller who holds the vector:
#
#     vec = main.forward_dense()          # once per parameter update
#     p1  = gather_dense(vec, idx1)       # 23-62x the direct kernel
#
DENSE_MIN_BATCH = 1024

def _scalar_domain_index(domain, samp):
  # Index lookup for a scalar domain against an already-packed [B] tensor: one
  # O(B*V) torch comparison, no per-sample Python. Returns (idx, all_present);
  # a sample matching no domain slot must not be answered from the vector.
  dom = torch.tensor([float(v) for v in domain], dtype=torch.get_default_dtype())
  eq = (samp.to(dom.dtype).unsqueeze(-1) == dom.unsqueeze(0))
  return eq.to(torch.int64).argmax(-1), bool(eq.any(-1).all())

def dense_query(dense_fn, kernel, domain, samples, args=(), dense=None):
  # The body of the emitted `<method>_at`. `dense=None` picks the cheaper axis
  # from the measured rule above; True/False force it, which is what a benchmark
  # or a differential test wants.
  #
  # Fast path first: an already-packed [B] tensor over a scalar domain needs no
  # Python per sample at all, which is the only shape where the automatic choice
  # can currently come out dense.
  if torch.is_tensor(samples) and samples.dim() > 0 and all(
       not isinstance(v, (T, InferenceList, Left, Right)) and not hasattr(v, '_fields')
       for v in domain):
    per_point = [a for a in args if torch.is_tensor(a) and a.dim() > 0 and a.shape[0] == samples.shape[0]]
    idx, all_present = _scalar_domain_index(domain, samples)
    use = ((not per_point) and all_present and samples.shape[0] >= DENSE_MIN_BATCH) \
          if dense is None else dense
    if not use:
      return kernel(samples, *args)
    if per_point:
      raise ValueError("dense_query(dense=True): a per-point argument cannot be evaluated over the domain")
    if not all_present:
      # Off-domain elements have no slot to gather; fall back wholesale rather
      # than silently answering them with slot 0.
      return kernel(samples, *args)
    return gather_dense(dense_fn(*args), idx)
  samples = list(samples)
  args = list(args)
  # An argument that varies per query point (a [B, n] neural symbol batch) has no
  # meaning over a domain of a different length, so it rules the dense axis out.
  # A shared one (a scalar topK accProb, a ThetaTree) broadcasts and is fine.
  per_point = [a for a in args if torch.is_tensor(a) and a.dim() > 0 and a.shape[0] == len(samples)]
  # A marshalled list of sample values: measured never to reach the crossover on
  # the corpus's kernels (see DENSE_MIN_BATCH), so the automatic choice is the
  # direct path. dense=True still forces it, which is what the differential does.
  use = False if dense is None else dense
  if use and per_point:
    raise ValueError("dense_query(dense=True): a per-point argument cannot be evaluated over the domain")
  if not use:
    return bucketed(kernel, samples, *args)
  pos = dense_positions(domain)
  keys = [denskey(s) for s in samples]
  hit = [i for i, k in enumerate(keys) if k in pos]
  miss = [i for i, k in enumerate(keys) if k not in pos]
  parts, idxs = [], []
  if hit:
    parts.append(gather_dense(dense_fn(*args), torch.tensor([pos[keys[i]] for i in hit])))
    idxs.append(hit)
  if miss:
    # A query *outside* the declared domain is still a legal query with a
    # well-defined answer (0 off the support -- e.g. discreteFloats' p(5.0)).
    # The dense vector cannot supply it, so those points fall back to the
    # ordinary kernel: a domain miss degrades to correctness, never to a wrong
    # value, which is also what makes the float-equality keying above safe.
    parts.append(bucketed(kernel, [samples[i] for i in miss], *args))
    idxs.append(miss)
  return _scatter(parts, idxs, len(samples))
