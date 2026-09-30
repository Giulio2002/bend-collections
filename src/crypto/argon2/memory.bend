import Base
import ./types.bend as A
import ./access.bend as X

# The Argon2 memory: a packed Array<U32> of 2^(8 + k) words, block b at words
# 256 b .. 256 b + 255 (lane n of the block at words 256 b + 2 n, low half,
# and 256 b + 2 n + 1, high half). Blocks are read and written word by word
# with Base's Array.get and Array.set, which the compiler turns into O(1)
# accesses of the packed buffer.

# Block b; the memory is handed back (access.bend: 256 Array.get, row by row).
def get(+b: Nat, a: Array<U32>) -> Array<U32> & A.Block:
  X.get(b, a)

# The memory with block b replaced by v (access.bend: 256 Array.set).
def set(+b: Nat, v: A.Block, a: Array<U32>) -> Array<U32>:
  X.put(b, v, a)

def pw(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pw(p))

# The smallest k >= k0 with 2^k >= n.
def levels_go(fuel: Nat, +n: Nat, +k: Nat, done: Bool) -> Nat:
  match fuel done:
    case _ True{}:
      k
    case 0n False{}:
      k
    case 1n+f False{}:
      levels_go(f, n, 1n+k, Nat.is_le(n, pw(1n+k)))

def levels(+n: Nat) -> Nat:
  levels_go(32n, n, 0n, Nat.is_le(n, 1n))

# A zeroed memory of 2^k blocks.
def new(+k: Nat) -> Array<U32>:
  Array.new(U32, Nat.add(8n, k), 0)
