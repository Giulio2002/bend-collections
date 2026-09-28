import Base
import ./field.bend as F

# X25519 (RFC 7748 section 5): the Montgomery ladder on Curve25519 over the
# field of field.bend. Scalars and u-coordinates are 32-byte little-endian
# lists (U32 values below 256); implementation == the RFC's pseudo-code
# (spec/crypto/curve25519/x25519.bend) is proved for every input.
#
# The ladder runs the same operations for every scalar: the conditional
# swap is arithmetic selection (field.bend `select`) driven by bit masks,
# bit t of the scalar is read at a public position, and the loop count is
# fixed (255). Bend has no timing model: this is branch-free by
# construction, not proved constant-time.

type St is Data:
  St{x2: List<&2, U32>, z2: List<&2, U32>, x3: List<&2, U32>, z3: List<&2, U32>, swap: U32}

# bit t of a little-endian byte string
def kbit(bs: List<&2, U32>, t: Nat) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, bt}:
      match t:
        case 0n:
          U32.and(b, 1)
        case 1n:
          U32.and(U32.shrn(b, 1n), 1)
        case 2n:
          U32.and(U32.shrn(b, 2n), 1)
        case 3n:
          U32.and(U32.shrn(b, 3n), 1)
        case 4n:
          U32.and(U32.shrn(b, 4n), 1)
        case 5n:
          U32.and(U32.shrn(b, 5n), 1)
        case 6n:
          U32.and(U32.shrn(b, 6n), 1)
        case 7n:
          U32.and(U32.shrn(b, 7n), 1)
        case 8n+q:
          kbit(bt, q)

# RFC 7748 decodeScalar25519's clamping: k[0] &= 248, k[31] &= 127, k[31] |= 64
def clamp_top(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.or(U32.and(x, 127), 64), Nil{}}
        case Con{y, yt}:
          Con{x, clamp_top(Con{y, yt})}

def clamp(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, bt}:
      clamp_top(Con{U32.and(b, 248), bt})

# one ladder step on the swapped pair (x2 : z2), (x3 : z3)
def step(+x1: List<&2, U32>, +x2: List<&2, U32>, +z2: List<&2, U32>, +x3: List<&2, U32>, +z3: List<&2, U32>, kt: U32) -> St:
  +a = F.add(x2, z2)
  +aa = F.sq(a)
  +b = F.sub(x2, z2)
  +bb = F.sq(b)
  +e = F.sub(aa, bb)
  +c = F.add(x3, z3)
  +d = F.sub(x3, z3)
  +da = F.mul(d, a)
  +cb = F.mul(c, b)
  St{F.mul(aa, bb), F.mul(e, F.add(aa, F.mul_small(e, 121665))), F.sq(F.add(da, cb)), F.mul(x1, F.sq(F.sub(da, cb))), kt}

# swap ^= k_t; cswap; the step; swap = k_t
def rung(+x1: List<&2, U32>, st: St, +kt: U32) -> St:
  match st:
    case St{+x2, +z2, +x3, +z3, swap}:
      +sw = U32.xor(swap, kt)
      step(x1, F.select(sw, x2, x3), F.select(sw, z2, z3), F.select(sw, x3, x2), F.select(sw, z3, z2), kt)

# the ladder's bit count, 8 len(k) - 1: 255 for a 32-byte scalar (RFC 7748
# `bits`). Taken from the scalar, it keeps the proof checker from unfolding
# the 255 steps for an unknown scalar.
def len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      1n+len(xt)

def nbits(+k: List<&2, U32>) -> Nat:
  Nat.sub(Nat.mul(8n, len(k)), 1n)

# bits t = n - 1 down to 0
def ladder(n: Nat, +k: List<&2, U32>, +x1: List<&2, U32>, st: St) -> St:
  match n:
    case 0n:
      st
    case 1n+ +t:
      ladder(t, k, x1, rung(x1, st, kbit(k, t)))

# the final cswap, then x2 * z2^(p - 2), encoded
def finish(st: St) -> List<&2, U32>:
  match st:
    case St{+x2, +z2, +x3, +z3, +swap}:
      F.to_bytes(F.mul(F.select(swap, x2, x3), F.inv(F.select(swap, z2, z3))))

# X25519 on two 32-byte strings of bytes below 256
def x25519_raw(k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  +x1 = F.of_bytes(u)
  +kc = clamp(k)
  finish(ladder(nbits(kc), kc, x1, St{F.one(), F.zero(), x1, F.one(), 0}))

# 32 values, each below 256
def valid_bytes(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          True{}
        case Con{x, xt}:
          False{}
    case 1n+m:
      match xs:
        case Nil{}:
          False{}
        case Con{x, xt}:
          Bool.and(U32.is_lt(x, 256), valid_bytes(m, xt))

def x25519_if(ok: Bool, k: List<&2, U32>, u: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{x25519_raw(k, u)}
    case False{}:
      None{}

# X25519(k, u); None unless both are 32 bytes below 256
def x25519(+k: List<&2, U32>, +u: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  x25519_if(Bool.and(valid_bytes(32n, k), valid_bytes(32n, u)), k, u)

# the base point u = 9
def base() -> List<&2, U32>:
  F.small(9)
