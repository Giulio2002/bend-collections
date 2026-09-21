import Base
import ../../src/lru/fast.bend as F

# Public capacity boundaries are independent of the current proof premises.
# These construct empty caches, so large capacities do not allocate huge arenas.
def new_capacity(cap: U32, pair: F.Fast<U32> & U32) -> Bool:
  (f, actual) = pair
  U32.is_eq(actual, cap)

def new_result(cap: U32, result: F.Made<U32>) -> Bool:
  match result:
    case F.Made{f}:
      new_capacity(cap, F.capacity(~U32, f))
    case F.Rejected{reason}:
      False{}

def new_ok(+cap: U32) -> Bool:
  new_result(cap, F.new(~U32, cap))

def resize_result(cap: U32, actual: U32, result: Result<&2, &2, String, U32>) -> Bool:
  match result:
    case Done{evicted}:
      Bool.and(U32.is_eq(actual, cap), U32.is_eq(evicted, 0))
    case Fail{reason}:
      False{}

def resize_capacity(cap: U32, result: Result<&2, &2, String, U32>, pair: F.Fast<U32> & U32) -> Bool:
  (f, actual) = pair
  resize_result(cap, actual, result)

def resize_pair(cap: U32, pair: F.Fast<U32> & Result<&2, &2, String, U32>) -> Bool:
  (f, result) = pair
  resize_capacity(cap, result, F.capacity(~U32, f))

def resize_ok(+cap: U32) -> Bool:
  resize_pair(cap, F.resize(~U32, F.init(~U32, 1), cap))

def mismatch(b: Bool) -> U32:
  match b:
    case True{}:
      0
    case False{}:
      1

def main() -> List<&2, U32>:
  [mismatch(new_ok(1)), mismatch(new_ok(2147483648)),
   mismatch(new_ok(2147483649)), mismatch(new_ok(4294967294)),
   mismatch(resize_ok(2147483649)), mismatch(resize_ok(4294967295))]
