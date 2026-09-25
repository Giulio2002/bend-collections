import Base
import ./common.bend as C

# Sequences of U32 values with wrapping (mod 2^32) addition, shared by the
# Fenwick and segment tree specifications. Imports only spec/ and Base.

# Sum of all elements, wrapping modulo 2^32 (U32.add).
def sum(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      U32.add(h, sum(t))

# The elements with index in [l, r).
def slice(xs: List<&2, U32>, +l: Nat, r: Nat) -> List<&2, U32>:
  C.take(U32, C.drop(U32, xs, l), Nat.sub(r, l))

def zeros(n: Nat) -> List<&2, U32>:
  C.replicate(U32, n, 0)

# Every element increased by v (wrapping).
def add_each(xs: List<&2, U32>, +v: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{U32.add(h, v), add_each(t, v)}
