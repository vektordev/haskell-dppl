from typing import Iterable
from math import *
from random import random, gauss

def sign(x):
  return -1 if x < 0 else 0 if x == 0 else 1

def density_IRUniform(x):
  return 1 if 0 <= x <= 1 else 0

def cumulative_IRUniform(x):
  return 0 if x < 0 else x if x <= 1 else 1

def density_IRNormal(x):
  return 1 / sqrt(2 * pi) * e**(-(x**2)/2)

def cumulative_IRNormal(x):
  return (1.0 + erf(x / sqrt(2.0))) / 2.0

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

class T:
  def __init__(self, t1, t2):
    self.t1 = t1
    self.t2 = t2

  def __eq__(self, other):
    if not isinstance(other, T):
      return False
    return eq(self.t1, other.t1) and eq(self.t2, other.t2)

  def __getitem__(self, index):
    if index == 0:
      return self.t1
    if index == 1:
      return self.t2
    raise ValueError("Tuple only has index 0 and 1")

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
    if tail == "ANY":
      self.next = AnyInferenceList()
    else:
      self.next = tail
    self.value = value

def toList(lst):
  back = EmptyInferenceList()
  for x in reversed(lst):
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
    raise ValueError("Element Not found in list")
  elif isinstance(lst, ConsInferenceList):
    if lst.value == sample:
      return 0
    else:
      return 1 + indexOf(sample, lst.next)
    
