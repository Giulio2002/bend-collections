import Base
import ./field.bend as F
import ./fe.bend as FE

# X25519 (RFC 7748 section 5): the Montgomery ladder on Curve25519 over the
# fast field of fe.bend (15 limbs of 17 bits). Scalars and u-coordinates are
# 32-byte little-endian lists (U32 values below 256); implementation == the
# RFC's pseudo-code (spec/crypto/curve25519/x25519.bend) is proved for every
# input.
#
# The ladder runs the same operations for every scalar: the conditional
# swap is arithmetic selection (fe.bend `select`) driven by bit masks, bit
# t of the scalar is read at a public position, and the loop count is fixed
# (255). Bend has no timing model: this is branch-free by construction, not
# proved constant-time.

type St is Data:
  St{x2: FE.Fe, z2: FE.Fe, x3: FE.Fe, z3: FE.Fe, swap: U32}

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

# the little-endian base-256 digits ds, each scaled by the symbolic one
def digits(+one: Nat, ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, dt}:
      Nat.add(Nat.mul(one, d), FE.pow2(8n, digits(one, dt)))

# a24 = 121665
def a24(+one: Nat) -> Nat:
  digits(one, [65n, 219n, 1n])

# one ladder step on the swapped pair (x2 : z2), (x3 : z3); R is the radix,
# c24 is a24
def step(+R: Nat, +c24: Nat, +x1: FE.Fe, +x2: FE.Fe, +z2: FE.Fe, +x3: FE.Fe, +z3: FE.Fe, kt: U32) -> St:
  +a = FE.add(R, x2, z2)
  +aa = FE.sq(R, a)
  +b = FE.sub(R, x2, z2)
  +bb = FE.sq(R, b)
  +e = FE.sub(R, aa, bb)
  +c = FE.add(R, x3, z3)
  +d = FE.sub(R, x3, z3)
  +da = FE.mul(R, d, a)
  +cb = FE.mul(R, c, b)
  St{FE.mul(R, aa, bb), FE.mul(R, e, FE.add(R, aa, FE.mul_small(R, e, c24))), FE.sq(R, FE.add(R, da, cb)), FE.mul(R, x1, FE.sq(R, FE.sub(R, da, cb))), kt}

# swap ^= k_t; cswap; the step; swap = k_t
def rung(+R: Nat, +c24: Nat, +x1: FE.Fe, st: St, +kt: U32) -> St:
  match st:
    case St{+x2, +z2, +x3, +z3, swap}:
      +sw = U32.xor(swap, kt)
      step(R, c24, x1, FE.select(sw, x2, x3), FE.select(sw, z2, z3), FE.select(sw, x3, x2), FE.select(sw, z3, z2), kt)

# the ladder's bit count, 8 len(k) - 1: 255 for a 32-byte scalar (RFC 7748
# `bits`). Taken from the scalar, it keeps the proof checker from unfolding
# the 255 steps for an unknown scalar.
def len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      1n+len(xt)

# 8 len(xs), the bit count of a byte string
def bitlen(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, xt}:
      Nat.add(8n, bitlen(xt))

def nbits(+k: List<&2, U32>) -> Nat:
  Nat.sub(Nat.mul(8n, len(k)), 1n)

# bits t = n - 1 down to 0
def ladder(n: Nat, +R: Nat, +c24: Nat, +k: List<&2, U32>, +x1: FE.Fe, st: St) -> St:
  match n:
    case 0n:
      st
    case 1n+ +t:
      ladder(t, R, c24, k, x1, rung(R, c24, x1, st, kbit(k, t)))

# the final cswap, then x2 * z2^(p - 2), encoded
def finish(+R: Nat, st: St) -> List<&2, U32>:
  match st:
    case St{+x2, +z2, +x3, +z3, +swap}:
      FE.to_bytes(R, FE.mul(R, FE.select(swap, x2, x3), FE.inv(R, FE.select(swap, z2, z3))))

# X25519 given the radix R = 2^17 and c24 = a24
def x25519_g(+R: Nat, +c24: Nat, +k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  +x1 = FE.of_bytes(u)
  finish(R, ladder(nbits(k), R, c24, clamp(k), x1, St{FE.one(), FE.zero(), x1, FE.one(), 0}))

# the constants, computed once per call from the run-time one: one_of
# takes an input list, which keeps the proof checker from evaluating a
# closed 2^17 while the list is unknown
def one_of(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      1n
    case Con{h, t}:
      1n

def radix_of(+xs: List<&2, U32>) -> Nat:
  FE.radix(one_of(xs))

def a24_of(+xs: List<&2, U32>) -> Nat:
  a24(one_of(xs))

# X25519 on two 32-byte strings of bytes below 256
def x25519_raw(+k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  x25519_g(radix_of(k), a24_of(k), k, u)

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
