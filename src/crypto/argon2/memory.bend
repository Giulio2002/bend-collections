import Base
import ./types.bend as A
import ./sub.bend as SB

# The Argon2 memory: a packed Array<U32> of 2^(8 + k) words, block b at words
# 256 b .. 256 b + 255 (lane n of the block at words 256 b + 2 n, low half,
# and 256 b + 2 n + 1, high half). Blocks are read and written word by word
# with Base's Array.get and Array.set, which the compiler turns into O(1)
# accesses of the packed buffer.

# Words i - n .. i, prepended to acc: pair holds the memory and word i.
def rd(n: Nat, +i: U32, acc: List<&2, U32>, pair: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match n pair:
    case 0n Tuple{a, w}:
      (a, w <> acc)
    case 1n+p Tuple{a, w}:
      +j = U32.sub(i, 1)
      rd(p, j, w <> acc, Array.get(U32, a, j))

def read_fin(pair: Array<U32> & List<&2, U32>) -> Array<U32> & A.Block:
  (a, ws) = pair
  (a, SB.rows8(ws))

# The word index of block b.
def base(+b: Nat) -> U32:
  U32.from_nat(Nat.mul(256n, b))

# Block b; the memory is handed back.
def get(+b: Nat, a: Array<U32>) -> Array<U32> & A.Block:
  +last = U32.add(base(b), 255)
  read_fin(rd(255n, last, Nil{}, Array.get(U32, a, last)))

# The words stored from index i on.
def wr(ws: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case w <> rest:
      wr(rest, U32.inc(i), Array.set(U32, a, i, w))

# The memory with block b replaced by v.
def set(+b: Nat, v: A.Block, a: Array<U32>) -> Array<U32>:
  wr(SB.words(v), base(b), a)

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
  Array.new(U32, Nat.add(k, 8n), 0)
