import math
from typing import Iterable
from math import *
from random import random, gauss
import itertools

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

def safe_exp(x):
  try:
    return math.exp(x)
  except OverflowError:
    return math.inf

def safe_log(x):
  if x > 0:
    return math.log(x)
  return -math.inf if x == 0 else math.nan

def density_uniform(x):
  return 1 if 0 <= x <= 1 else 0

def cumulative_uniform(x):
  return 0 if x < 0 else x if x <= 1 else 1

def density_normal(x):
  return 1 / sqrt(2 * pi) * e**(-(x**2)/2)

def cumulative_normal(x):
  return (1.0 + erf(x / sqrt(2.0))) / 2.0

# Native log-pdf/log-cdf (task log-space-probability-computation), computed
# directly from the formula rather than as log(density_...(x)): the latter
# would underflow to a true float 0.0 in a deep tail before the log is taken,
# losing the tail entirely.
def log_density_uniform(x):
  return 0.0 if 0 <= x <= 1 else -math.inf

def log_cumulative_uniform(x):
  c = cumulative_uniform(x)
  return -math.inf if c <= 0 else math.log(c)

def log_density_normal(x):
  return -(x**2) / 2 - 0.5 * math.log(2 * pi)

def log_cumulative_normal(x):
  c = cumulative_normal(x)
  return -math.inf if c <= 0 else math.log(c)

# Log-sum-exp reduction backing IRLogEnumSum's emitted code: the log-space
# sibling of a plain sum() over enumerated per-value log-probabilities.
def logsumexp(xs):
  xs = list(xs)
  if not xs:
    return -math.inf
  m = max(xs)
  if m == -math.inf:
    return -math.inf
  return m + math.log(sum(math.exp(x - m) for x in xs))

def rand():
  return random()

def randn():
  return gauss(0, 1)

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
