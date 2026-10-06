import math
from typing import Iterable
from math import *
from random import random, gauss
import itertools
import sys

def sign(x):
  return -1 if x < 0 else 0 if x == 0 else 1

# --- IEEE-conforming unary math ------------------------------------------
#
# The reference semantics for every backend is the interpreter's, i.e.
# Haskell's: `exp` saturates to `inf` past the representable range, `log 0` is
# `-inf` and `log` of a negative is `NaN`. CPython's `math` module instead
# *raises* on all three (`OverflowError` / `ValueError`), so emitted code that
# called `math.exp`/`math.log` directly crashed where the interpreter and Julia
# answer a number.
#
# This is reachable, not theoretical: an InjF inverse's monotonicity-direction
# guard evaluates the inverse derivative eagerly to read its sign, so
# `cdf(1000.0)` on `main = log Uniform` emits `math.exp(1000.0) > 0.0` and took
# down the whole query with `OverflowError` instead of answering 1.0.
#
# `log` is currently safe only by accident -- every reachable call site happens
# to sit behind an InjF `applicability` guard -- which is a property of today's
# inverse set, not an invariant. Both go through a wrapper so a future inverse
# cannot reintroduce the same class of bug. (The batched backend already did
# this: `safe_log` in `pythonLibBatched.py` is the torch-side twin.)

# --- torch-transparent math -------------------------------------------------
#
# The scalar backend is also the one a user trains through when a program has
# neural leaves: its arguments are then torch tensors, not floats. `math.erf`,
# `math.exp` and `math.log` do not raise on a tensor -- they convert it through
# `__float__` and return a plain float, with nothing but a UserWarning -- so a
# function calling them severs the autograd graph and a model trains through a
# dead gradient while still drawing a believable loss curve (task
# python-codegen-silent-precision-traps; the classification of every function
# here is investigation scalar-pythonlib-autograd-severing-inventory).
#
# Every function below with a real derivative that would otherwise pass through
# `math` therefore dispatches on `torch.is_tensor` first. torch is looked up in
# `sys.modules` rather than imported: a caller that passes a tensor has
# necessarily imported torch already, and a caller that has not keeps a
# torch-free runtime. The tensor arm computes the same formula as the float
# arm, so the two agree in value. `test/TestPythonPrelude.hs` (driving
# `test/prelude_numerics_probe.py`) pins value and gradient for each, and fails
# on any new public function nobody has classified -- add a new function there.

def _torch_for(x):
  t = sys.modules.get("torch")
  return t if t is not None and t.is_tensor(x) else None

def safe_exp(x):
  t = _torch_for(x)
  if t is not None:
    return t.exp(x)          # saturates to inf, as the float arm does
  try:
    return math.exp(x)
  except OverflowError:
    return math.inf

def safe_log(x):
  t = _torch_for(x)
  if t is not None:
    return t.log(x)          # -inf at 0, nan below, as the float arm does
  if x > 0:
    return math.log(x)
  return -math.inf if x == 0 else math.nan

def density_uniform(x):
  return 1 if 0 <= x <= 1 else 0

def cumulative_uniform(x):
  return 0 if x < 0 else x if x <= 1 else 1

def density_normal(x):
  return 1 / sqrt(2 * pi) * e**(-(x**2)/2)

# Phi(x) = erfc(-x / sqrt 2) / 2, not (1 + erf(x / sqrt 2)) / 2: the latter
# cancels in the lower tail (Phi(-8) came out 6.1e-16 for 6.2e-16), and the
# compiler spells an upper tail 1 - Phi(z) as Phi(-z) (Semiring.
# upperTailComplement), so the lower tail is where every small normal
# probability lands (task cumulative-normal-upper-tail-cancellation).
def cumulative_normal(x):
  t = _torch_for(x)
  if t is not None:
    return t.special.erfc(-x / sqrt(2.0)) / 2.0
  return erfc(-x / sqrt(2.0)) / 2.0

# Native log-pdf/log-cdf (task log-space-probability-computation), computed
# directly from the formula rather than as log(density_...(x)): the latter
# would underflow to a true float 0.0 in a deep tail before the log is taken,
# losing the tail entirely.
def log_density_uniform(x):
  return 0.0 if 0 <= x <= 1 else -math.inf

def log_cumulative_uniform(x):
  # Inside [0, 1] the CDF is x itself -- a tensor when x is -- and outside it a
  # python constant whose (zero) derivative is correctly dropped.
  return _log_cdf(cumulative_uniform(x))

def log_density_normal(x):
  return -(x**2) / 2 - 0.5 * math.log(2 * pi)

def log_cumulative_normal(x):
  return _log_cdf(cumulative_normal(x))

def _log_cdf(c):
  t = _torch_for(c)
  if t is not None:
    return t.log(c)          # -inf where the CDF is 0, as below
  return -math.inf if c <= 0 else math.log(c)

# Log-sum-exp reduction backing the log-space enumerated sum (BReduce
# ROpLogSumExp): the log-space sibling of a plain sum() over enumerated
# per-value log-probabilities. With tensor terms it must be torch's own: the
# float arm's math.exp/math.log would leave only the max term's constant
# derivative of 1 instead of each term's softmax weight. Python-float terms
# among tensor ones (a folded constant arm) are lifted to the tensors' dtype.
def logsumexp(xs):
  xs = list(xs)
  if not xs:
    return -math.inf
  ts = [x for x in xs if _torch_for(x) is not None]
  if ts:
    t = _torch_for(ts[0])
    ref = ts[0]
    return t.logsumexp(t.stack([x if t.is_tensor(x) else t.tensor(float(x), dtype=ref.dtype)
                                for x in xs]), 0)
  m = max(xs)
  if m == -math.inf:
    return -math.inf
  return m + math.log(sum(math.exp(x - m) for x in xs))

def rand():
  return random()

def randn():
  return gauss(0, 1)

def categorical_index(u, w, start, n):
  # Inverse-CDF categorical draw backing IR's BCategoricalIndex (task
  # neural-categorical-sampler-nests-v-deep): the smallest k in [0, n) with
  # u * S < w[start] + ... + w[start + k], S the sum of the n weights, clamped
  # to n - 1 (rounding at the top of the CDF, or all-zero weights). The
  # weights are unnormalised, so k is drawn with probability w[start + k] / S.
  #
  # w is a network's output: anything iterable (a list, or an InferenceList,
  # read in one walk rather than a cons walk per slot), or anything with a
  # cumsum (a torch tensor, a numpy array), which takes the vectorised path --
  # at vocabulary scale, one kernel instead of tens of thousands of scalar
  # reads.
  if hasattr(w, "cumsum"):
    c = w[start:start + n].cumsum(0)
    below = int((c <= u * c[-1]).sum())
    return min(below, n - 1)
  seg = list(itertools.islice(w, start, start + n))
  target = u * sum(seg)
  acc = 0.0
  for k, x in enumerate(seg):
    acc += x
    if target < acc:
      return k
  return n - 1

def isAny(x):
  if x == "ANY":
    return True
  if isinstance(x, AnyInferenceList):
    return True
  return False

def eq(o1, o2):
  if isAny(o1) or isAny(o2):
    return True
  else:
    return o1 == o2

def isclose(a, b):
    return abs(a - b) <= 10e-10

def throw(e):
  raise Exception(e)

# Tuple
class T:
  def __init__(self, t1, t2):
    self.t1 = t1
    self.t2 = t2

  def __eq__(self, other):
    if not isinstance(other, T):
      return False
    return eq(self.t1, other.t1) and eq(self.t2, other.t2)
  
  def __lt__(self, other):
    if not isinstance(other, T):
      raise ValueError("Cannot compare Tuple with non-Tuple")
    return self.t1 < other.t1 and self.t2 < other.t2
  
  def __gt__(self, other):
    if not isinstance(other, T):
      raise ValueError("Cannot compare Tuple with non-Tuple")
    return self.t1 > other.t1 and self.t2 > other.t2

  def __getitem__(self, index):
    if index == 0:
      return self.t1
    if index == 1:
      return self.t2
    raise ValueError("Tuple only has index 0 and 1")

class Left:
  def __init__(self, val):
    self.val = val

  def __eq__(self, other):
    if not isinstance(other, Left):
      return False
    return eq(other.val, self.val)
  
def fromLeft(l):
  if not isinstance(l, Left):
    raise Exception("Item is not a Left: " + str(l))
  return l.val

class Right:
  def __init__(self, val):
    self.val = val

  def __eq__(self, other):
    if not isinstance(other, Right):
      return False
    return eq(other.val, self.val)
  
def fromRight(r):
  if not isinstance(r, Right):
    raise Exception("Item is not a Right: " + str(r))
  return r.val

class InferenceList:
  def __init__(self, value = None):
    return NotImplemented

  def __len__(self):
    curr = self
    cnt = 0
    while curr is not None:
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
      # Tail lists
      if index.start > 0 and (index.stop == -1 or index.stop is None) and (index.step == 1 or index.step is None):
        current = self
        for _ in range(index.start - 1):
          current = current.next
        return current.next
      else:
        raise IndexError("Slices may only be used for tail lists")
    if index < 0:
      index += len(self)
    if index < 0 or index >= len(self):
      raise IndexError("LinkedList index out of range")
    current = self
    for _ in range(index):
      current = current.next
    return current.value
  
  def __eq__(self, other):
    if not isinstance(other, InferenceList):
      return False
    # An ANY list matches any list, as in the interpreter (task
    # python-list-eq-any-tail-not-wildcard): head's inverse queries
    # Cons(x, AnyInferenceList()), whose tail must match the rest of the list.
    # After the guard above, since isAny itself compares against "ANY".
    if isAny(self) or isAny(other):
      return True
    return eq(self.value, other.value) and self.next == other.next
  
  def __lt__(self, other):
    if not isinstance(other, InferenceList):
      raise ValueError("Cannot compare InferenceList with non-InferenceList (possible due to a length mismatch)")
    if isAny(self) or isAny(other):
      return True
    return self.value < other.value and self.next < other.next
  
  def __gt__(self, other):
    if not isinstance(other, InferenceList):
      raise ValueError("Cannot compare InferenceList with non-InferenceList (possible due to a length mismatch)")
    if isAny(self) or isAny(other):
      return True
    return self.value > other.value and self.next > other.next

  def prepend(self, value):
    return ConsInferenceList(value, self)

class EmptyInferenceList(InferenceList):
  def __init__(self):
    self.next = None
    self.value = None

class AnyInferenceList(InferenceList):
  def __init__(self):
    self.next = None
    self.value = None

class ConsInferenceList(InferenceList):
  def __init__(self, value, tail: InferenceList):
    # The scalar "ANY" is not a list, and a tail must be one. Nothing the
    # compiler emits should reach this any more -- an inverse that
    # reconstructs a list around a hole now uses the list-shaped any-value
    # (see PredefinedFunctions.anyOfType) -- but the coercion stays as a
    # backstop, and it is why the pre-fix -O0 output ran here while the same
    # value was a hard MethodError in Julia.
    if tail == "ANY":
      self.next = AnyInferenceList()
    else:
      self.next = tail
    self.value = value

def toList(lst):
  back = EmptyInferenceList()
  # Materialise first: callers may pass lazy iterables (map/itertools.product
  # results), which are not reversible.
  for x in reversed(list(lst)):
    back = back.prepend(x)
  return back

def mapList(f, lst):
  if isinstance(lst, EmptyInferenceList):
    return EmptyInferenceList()
  if isinstance(lst, AnyInferenceList):
    raise Exception("Cannot map AnyLists")
  if isinstance(lst, ConsInferenceList):
    val = f(lst[0])
    rst = mapList(f, lst[1:])
    return ConsInferenceList(val, rst)

# ===============================
# Start of standard lib functions
# ===============================

def indexOf(sample, lst):
  if isinstance(lst, EmptyInferenceList) or isinstance(lst, AnyInferenceList):
    raise ValueError("Element not found in list")
  elif isinstance(lst, ConsInferenceList):
    if lst.value == sample:
      return 0
    else:
      return 1 + indexOf(sample, lst.next)
    
def listProd(lst):
  if isinstance(lst, AnyInferenceList):
    raise ValueError("Element not found in list")
  elif isinstance(lst, EmptyInferenceList):
    return 1
  elif isinstance(lst, ConsInferenceList):
    return lst.value * listProd(lst.next)
    
def listConcat(lst1, lst2):
  # Iterative rather than recursive like its interpreter twin
  # (StandardLibrary.stdListConcat): a writeLogits vector can be longer than
  # Python's recursion limit.
  if isinstance(lst1, AnyInferenceList):
    raise ValueError("Cannot concatenate an AnyList")
  back = lst2
  for x in reversed(list(lst1)):
    back = ConsInferenceList(x, back)
  return back

def isPossible(multiVal, expr):
  if multiVal[0] == "C":
    return True
  elif multiVal[0] == "D":
    return expr in multiVal[1]
  elif multiVal[0] == "T" and isinstance(expr, tuple):
    return isPossible(multiVal[1][0], expr[0]) and isPossible(multiVal[1][1], expr[1])
  elif multiVal[0] == "E" and isinstance(expr, Left):
    return isPossible(multiVal[1][0], fromLeft(expr))
  elif multiVal[0] == "E" and isinstance(expr, Right):
    return isPossible(multiVal[1][1], fromRight(expr))
  elif multiVal[0] == "A":
    foundConstr = False
    for c in multiVal[1]:
      cClass = c[0]
      cMultiFields = c[1]
      if isinstance(expr, cClass):
        foundConstr = True
        for mf, ef in zip(cMultiFields, expr._fields):
          if not isPossible(mf, ef):
            return False
    return foundConstr
  
# NOTE (task retire-irenumsum): `multiValueToValueList` stood here, deriving a
# MultiValue's enumerated support at run time (with a memo cache, because a
# multi-object neural scene's cartesian product dominated the query). Nothing
# emits a call to it any more: an enumerated sum is now a tensor reduce over a
# map over a *literal* list of the domain's values, built at compile time, so
# the product is computed once by the compiler instead of on every query.
# `isPossible` above walks the description structurally and never needed it.
