import Base
import ../u64.bend as W
import ./chacha8/block.bend as B

# ChaCha8: Go's math/rand/v2.ChaCha8, the C2SP chacha8rand generator
# (https://c2sp.org/chacha8rand; Go's internal/chacha8rand), bit for bit.
#
#   new(seed)          Some{g} for a 32-byte seed (a list of 32 bytes < 256),
#                      None otherwise (Go's NewChaCha8([32]byte))
#   of_key(k)          the generator of a key given as eight little-endian
#                      words (B.K{k0, ..., k7}); new(seed) is of_key of its words
#   next(g)            the next 64-bit output and the advanced generator
#                      (Go's (*ChaCha8).Uint64); the Source interface of
#                      rand.bend: R.uint64n(~ChaCha8, ~next, g, n), ...
#
# Each iteration keys ChaCha8 with the 32-byte input, runs the sixteen
# blocks 0..15 in four groups of four (chacha8/block.bend), outputs the first
# 124 64-bit words and takes the last four (32 bytes) as the next key: the
# key is erased every 992 bytes of output (C2SP "fast key erasure"; Go
# reseeds the same way in (*State).Refill). The generator keeps the key, the
# next group and the unread words of the current group, so next is one list
# pop, and one group computation every 32 (the last group of an iteration:
# 28) outputs.
#
# Proved to produce the C2SP stream of spec/math/random/chacha8rand.bend for
# every seed (proofs/math/random/chacha8/); tested against Go's vectors
# (tests/math/random/, tools/check_random.py).

# the next group of the iteration: blocks 0-3, 4-7, 8-11 or 12-15
type Phase is Data:
  G0{}
  G1{}
  G2{}
  G3{}

type ChaCha8 is Data:
  C{key: B.Key, phase: Phase, buf: List<&2, W.U64>}

def zero() -> W.U64:
  W.U64{0, 0}

def of_key(k: B.Key) -> ChaCha8:
  C{k, G0{}, []}

# the key of the next iteration: the last four words of the last group
def rekey(l: List<&2, W.U64>) -> B.Key:
  match l:
    case [W.U64{k0, k1}, W.U64{k2, k3}, W.U64{k4, k5}, W.U64{k6, k7}]:
      B.K{k0, k1, k2, k3, k4, k5, k6, k7}
    case _:
      B.K{0, 0, 0, 0, 0, 0, 0, 0}

# the last group: 28 words of output, then the next key
def last(+g: List<&2, W.U64>) -> ChaCha8:
  C{rekey(List.drop(&2, W.U64, g, 28n)), G0{}, List.take(&2, W.U64, g, 28n)}

def refill(+k: B.Key, p: Phase) -> ChaCha8:
  match p:
    case G0{}:
      C{k, G1{}, B.group(k, 0)}
    case G1{}:
      C{k, G2{}, B.group(k, 4)}
    case G2{}:
      C{k, G3{}, B.group(k, 8)}
    case G3{}:
      last(B.group(k, 12))

def pop(g: ChaCha8) -> W.U64 & ChaCha8:
  match g:
    case C{k, p, buf}:
      match buf:
        case Con{x, rest}:
          (x, C{k, p, rest})
        case Nil{}:
          (zero(), C{k, p, []})

# the next 64-bit output (a refill always yields a nonempty buffer)
def next(g: ChaCha8) -> W.U64 & ChaCha8:
  match g:
    case C{+k, p, buf}:
      match buf:
        case Con{x, rest}:
          (x, C{k, p, rest})
        case Nil{}:
          pop(refill(k, p))

# ---- seeds ----

# the little-endian word of four bytes (Go's byteorder.LEUint32)
def le32(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.shln(b2, 16n)), U32.shln(b3, 24n))

def all_bytes(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+b, rest}:
      Bool.and(U32.is_lt(b, 256), all_bytes(rest))

def key_of(bs: List<&2, U32>) -> Maybe<&2, B.Key>:
  match bs:
    case [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3, e0, e1, e2, e3, f0, f1, f2, f3, g0, g1, g2, g3, h0, h1, h2, h3]:
      Some{B.K{le32(a0, a1, a2, a3), le32(b0, b1, b2, b3), le32(c0, c1, c2, c3), le32(d0, d1, d2, d3), le32(e0, e1, e2, e3), le32(f0, f1, f2, f3), le32(g0, g1, g2, g3), le32(h0, h1, h2, h3)}}
    case _:
      None{}

def lift(m: Maybe<&2, B.Key>) -> Maybe<&2, ChaCha8>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{of_key(k)}

def seed_ok(bs: List<&2, U32>, ok: Bool) -> Maybe<&2, ChaCha8>:
  match ok:
    case False{}:
      None{}
    case True{}:
      lift(key_of(bs))

# Go's NewChaCha8(seed): the seed is 32 bytes, each below 256
def new(+seed: List<&2, U32>) -> Maybe<&2, ChaCha8>:
  seed_ok(seed, all_bytes(seed))
