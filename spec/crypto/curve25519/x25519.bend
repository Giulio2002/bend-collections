import Base
import ../../lib/common.bend as C
import ./field.bend as FS
import ../../../src/crypto/curve25519/x25519.bend as X

# X25519, RFC 7748 section 5, over the natural numbers: a transcription of
# the RFC's decodeScalar25519, decodeUCoordinate, encodeUCoordinate and the
# Montgomery ladder pseudo-code, every operation mod p (FS.fadd, FS.fsub,
# FS.fmul, FS.finv). HACL*'s Spec.Curve25519 is the same transcription.
# `one` is the symbolic 1 of field.bend.
#
#   clause          statement
#   X25519.value    the implementation equals this specification on every
#                   pair of 32-byte strings (bytes below 256)
#   X25519.checked  the checked entry point: Some of it on valid input,
#                   None otherwise

# decodeScalar25519's clamping: k[0] &= 248; k[31] &= 127; k[31] |= 64
def clamp_last(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.or(U32.and(x, 127), 64), Nil{}}
        case Con{y, yt}:
          Con{x, clamp_last(Con{y, yt})}

def clamp(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, bt}:
      clamp_last(Con{U32.and(b, 248), bt})

def decode_scalar(bs: List<&2, U32>) -> Nat:
  FS.value(clamp(bs))

# decodeUCoordinate: the last byte's top bit masked (bits = 255)
def mask_last(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.and(x, 127), Nil{}}
        case Con{y, yt}:
          Con{x, mask_last(Con{y, yt})}

def decode_u(bs: List<&2, U32>) -> Nat:
  FS.value(mask_last(bs))

# encodeUCoordinate: u mod p as 32 little-endian bytes
def le_bytes(n: Nat, +x: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{U32.from_nat(Nat.mod(x, 256n)), le_bytes(m, Nat.div(x, 256n))}

def encode_u(+p: Nat, u: Nat) -> List<&2, U32>:
  le_bytes(32n, Nat.mod(u, p))

# k_t = (k >> t) & 1
def kbit(+k: Nat, t: Nat) -> Nat:
  C.bit(C.high(t, k))

# swap ^= k_t, on bits
def bxor(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+q:
      Nat.sub(1n, b)

# cswap(swap, a, b), RFC 7748: (a, b) when swap is 0, (b, a) when it is 1;
# cs_fst and cs_snd are its two components
def cs_fst(swap: Nat, a: Nat, b: Nat) -> Nat:
  match swap:
    case 0n:
      a
    case 1n+q:
      b

def cs_snd(swap: Nat, a: Nat, b: Nat) -> Nat:
  match swap:
    case 0n:
      b
    case 1n+q:
      a

type LSt is Data:
  LSt{x2: Nat, z2: Nat, x3: Nat, z3: Nat, swap: Nat}

# a24 = 121665
def a24(+one: Nat) -> Nat:
  FS.digits(one, [65n, 219n, 1n])

def step(+one: Nat, +p: Nat, +x1: Nat, +x2: Nat, +z2: Nat, +x3: Nat, +z3: Nat, kt: Nat) -> LSt:
  +a = FS.fadd(p, x2, z2)
  +aa = FS.fmul(p, a, a)
  +b = FS.fsub(p, x2, z2)
  +bb = FS.fmul(p, b, b)
  +e = FS.fsub(p, aa, bb)
  +c = FS.fadd(p, x3, z3)
  +d = FS.fsub(p, x3, z3)
  +da = FS.fmul(p, d, a)
  +cb = FS.fmul(p, c, b)
  +s = FS.fadd(p, da, cb)
  +t = FS.fsub(p, da, cb)
  LSt{FS.fmul(p, aa, bb), FS.fmul(p, e, FS.fadd(p, aa, FS.fmul(p, e, a24(one)))), FS.fmul(p, s, s), FS.fmul(p, x1, FS.fmul(p, t, t)), kt}

def rung(+one: Nat, +p: Nat, +x1: Nat, st: LSt, +kt: Nat) -> LSt:
  match st:
    case LSt{+x2, +z2, +x3, +z3, swap}:
      +sw = bxor(swap, kt)
      step(one, p, x1, cs_fst(sw, x2, x3), cs_fst(sw, z2, z3), cs_snd(sw, x2, x3), cs_snd(sw, z2, z3), kt)

# for t = n - 1 down to 0
def ladder(+one: Nat, +p: Nat, n: Nat, +k: Nat, +x1: Nat, st: LSt) -> LSt:
  match n:
    case 0n:
      st
    case 1n+ +t:
      ladder(one, p, t, k, x1, rung(one, p, x1, st, kbit(k, t)))

def finish(+p: Nat, st: LSt) -> List<&2, U32>:
  match st:
    case LSt{x2, z2, x3, z3, +swap}:
      encode_u(p, FS.fmul(p, cs_fst(swap, x2, x3), FS.finv(p, cs_fst(swap, z2, z3))))

# RFC 7748's `bits` (255 for X25519) as 8 * len(k) - 1 of the 32-byte scalar
def bits(k: List<&2, U32>) -> Nat:
  Nat.sub(Nat.mul(8n, C.length(U32, k)), 1n)

def x25519_p(+one: Nat, +p: Nat, +k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  +x1 = Nat.mod(decode_u(u), p)
  finish(p, ladder(one, p, bits(k), decode_scalar(k), x1, LSt{1n, 0n, x1, 1n, 0n}))

def x25519(+one: Nat, k: List<&2, U32>, u: List<&2, U32>) -> List<&2, U32>:
  x25519_p(one, FS.prime(one), k, u)

# ---- clauses ----

def X25519.value(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>, +hk: {FS.tight(k) == True{} : Bool}, +hu: {FS.tight(u) == True{} : Bool}) -> Type:
  {X.x25519_raw(k, u) == x25519(one, k, u) : List<&2, U32>}

def X25519.checked(+one: Nat, +h1: {one == 1n : Nat}, +k: List<&2, U32>, +u: List<&2, U32>) -> Type:
  {X.x25519(k, u) == Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(FS.tight(k), FS.tight(u)), Some{x25519(one, k, u)}, None{}) : Maybe<&2, List<&2, U32>>}
