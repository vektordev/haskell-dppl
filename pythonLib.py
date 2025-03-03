from typing import Iterable
from math import *

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


def isAny(x):
  if x == "ANY":
    return True
  if isinstance(x, AnyInferenceList):
    return True
  return False

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
    while curr is not None:
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