import Base
import ./types.bend as A
import ./sub.bend as SB
import ./blamka.bend as G

# The Argon2 memory: a packed Array<U32> of depth 8 + k, block b being the
# depth-8 subtree at position b (words 256 b .. 256 b + 255, lane n of the block
# at words 256 b + 2 n and 256 b + 2 n + 1). A block is reached by descending
# the k levels above the block subtrees, as Base's Array.get descends to a
# word, and read or rebuilt whole: one descent per block instead of 256 word
# accesses.

# 2^k
def pw(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pw(p))

# The branch at a node with k levels below: is block b in the left half?
def dec(k: Nat, +b: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+q:
      Nat.is_lt(b, pw(q))

def get_lo(r: Array<U32>, p: Array<U32> & A.Block) -> Array<U32> & A.Block:
  (l, x) = p
  (ANode{l, r}, x)

def get_hi(l: Array<U32>, p: Array<U32> & A.Block) -> Array<U32> & A.Block:
  (r, x) = p
  (ANode{l, r}, x)

def get_go(k: Nat, a: Array<U32>, +b: Nat, left: Bool) -> Array<U32> & A.Block:
  match k a left:
    case 0n ALeaf{x} _:
      SB.read(ALeaf{x})
    case 0n ANode{l, r} _:
      SB.read(ANode{l, r})
    case 1n+p ALeaf{x} _:
      (ALeaf{x}, G.zero())
    case 1n+ +p ANode{l, r} True{}:
      get_lo(r, get_go(p, l, b, dec(p, b)))
    case 1n+ +p ANode{l, r} False{}:
      +c = Nat.sub(b, pw(p))
      get_hi(l, get_go(p, r, c, dec(p, c)))

# Block b of a memory with k levels above the blocks; the memory is handed back.
def get(+k: Nat, +b: Nat, a: Array<U32>) -> Array<U32> & A.Block:
  get_go(k, a, b, dec(k, b))

def set_go(k: Nat, a: Array<U32>, +b: Nat, v: A.Block, left: Bool) -> Array<U32>:
  match k a left:
    case 0n ALeaf{x} _:
      SB.build(v)
    case 0n ANode{l, r} _:
      SB.build(v)
    case 1n+p ALeaf{x} _:
      ALeaf{x}
    case 1n+ +p ANode{l, r} True{}:
      ANode{set_go(p, l, b, v, dec(p, b)), r}
    case 1n+ +p ANode{l, r} False{}:
      +c = Nat.sub(b, pw(p))
      ANode{l, set_go(p, r, c, v, dec(p, c))}

# The memory with block b replaced by v.
def set(+k: Nat, +b: Nat, v: A.Block, a: Array<U32>) -> Array<U32>:
  set_go(k, a, b, v, dec(k, b))

# The smallest k with 2^k >= n, searching up from k.
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
