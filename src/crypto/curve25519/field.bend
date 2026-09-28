import Base

# Arithmetic in GF(p), p = 2^255 - 19, for X25519 and Ed25519.
#
# A field element is a list of 32 U32 limbs, little-endian in radix 2^8:
# value(a) = a0 + 2^8 a1 + ... + 2^248 a31 (spec/crypto/curve25519/field.bend).
# Every operation returns a "tight" element: 32 limbs, each below 2^8, so
# its value is below 2^256 (not necessarily below p; `freeze` gives the
# canonical representative, which is also its 32-byte encoding).
#
# Only U32 addition, multiplication, subtraction and division/remainder by
# the constant 256 (a shift and a mask after compilation) are used, and no
# intermediate reaches 2^32 (proved: proofs/crypto/curve25519). The schoolbook
# product of two tight elements has limbs below 32 * 255^2 < 2^21; folding
# the high half by 2^256 == 38 (mod p) keeps them below 2^27; three carry
# passes bring the result back to tight (TweetNaCl's car25519, in radix
# 2^8; Fiat-Crypto's unsaturated-limb reduction, Erbsen et al. 2019).
#
# No function branches on a limb value: selection is arithmetic
# (a * (1 - s) + b * s), list shapes are fixed (32 limbs), and exponents
# are public. Bend has no timing model, so constant time is by
# construction, not proved.

# ---- limb lists ----

# limbwise sum; the longer tail is kept
def addl(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Con{x, xt}
        case Con{y, yt}:
          Con{U32.add(x, y), addl(xt, yt)}

# every limb times a
def scal(+a: U32, ys: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, yt}:
      Con{U32.mul(a, y), scal(a, yt)}

# the product polynomial: conv(x :: xs, ys) = x ys + 2^8 conv(xs, ys)
def conv(xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      addl(scal(x, ys), Con{0, conv(xt, ys)})

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          Con{x, take(m, xt)}

def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, xt}:
          drop(m, xt)

# ---- carries ----

# limbs and the carry out of the top one
type Cr is Data:
  Cr{limbs: List<&2, U32>, out: U32}

def carry_con(l: U32, r: Cr) -> Cr:
  match r:
    case Cr{a, c}:
      Cr{Con{l, a}, c}

# one carry pass: limbs below 2^8 and the carry out of the top limb
def carry(xs: List<&2, U32>, c: U32) -> Cr:
  match xs:
    case Nil{}:
      Cr{Nil{}, c}
    case Con{h, t}:
      +s = U32.add(h, c)
      carry_con(U32.mod(s, 256), carry(t, U32.div(s, 256)))

# add k to the lowest limb
def add0(xs: List<&2, U32>, k: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      Con{U32.add(x, k), xt}

# carry, then fold the carry out back in: 2^256 == 38 (mod p)
def pass_fin(r: Cr) -> List<&2, U32>:
  match r:
    case Cr{a, c}:
      add0(a, U32.mul(38, c))

def pass(xs: List<&2, U32>) -> List<&2, U32>:
  pass_fin(carry(xs, 0))

# 32 limbs below 2^27 to a tight element of the same value mod p
def reduce(xs: List<&2, U32>) -> List<&2, U32>:
  pass(pass(pass(xs)))

# ---- constants ----

def zero() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def one() -> List<&2, U32>:
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# a small constant k < 2^8 as an element
def small(k: U32) -> List<&2, U32>:
  [k, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

# 8p limbwise: every limb at least 2^10 - 8, so a + 8p - b never borrows
def eight_p() -> List<&2, U32>:
  [1896, 2040, 2040, 2040, 2040, 2040, 2040, 2040,
   2040, 2040, 2040, 2040, 2040, 2040, 2040, 2040,
   2040, 2040, 2040, 2040, 2040, 2040, 2040, 2040,
   2040, 2040, 2040, 2040, 2040, 2040, 2040, 1016]

# 2^256 - p = 2^255 + 19
def comp_p() -> List<&2, U32>:
  [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128]

# ---- field operations (tight in, tight out) ----

# a + k - b limbwise
def subl(xs: List<&2, U32>, ys: List<&2, U32>, ks: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{y, yt}:
          match ks:
            case Nil{}:
              Nil{}
            case Con{k, kt}:
              Con{U32.sub(U32.add(x, k), y), subl(xt, yt, kt)}

def add(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  reduce(addl(a, b))

def sub(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  reduce(subl(a, b, eight_p()))

# fold the product: low 32 limbs + 38 * high limbs
def wide(+zs: List<&2, U32>) -> List<&2, U32>:
  addl(take(32n, zs), scal(38, drop(32n, zs)))

def mul(a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  reduce(wide(conv(a, b)))

def sq(+a: List<&2, U32>) -> List<&2, U32>:
  mul(a, a)

# a * k for a constant k < 2^17
def mul_small(a: List<&2, U32>, +k: U32) -> List<&2, U32>:
  reduce(scal(k, a))

def neg(a: List<&2, U32>) -> List<&2, U32>:
  sub(zero(), a)

# ---- selection (s is 0 or 1) ----

# s == 0: a; s == 1: b; limbwise a * (1 - s) + b * s
def select(+s: U32, xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Nil{}
        case Con{y, yt}:
          Con{U32.add(U32.mul(x, U32.sub(1, s)), U32.mul(y, s)), select(s, xt, yt)}

# ---- powers (public exponents) ----

# acc^(2^n) * x^(2^n - 1): n steps of acc = acc^2 * x
def pow_ones(n: Nat, +x: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+m:
      pow_ones(m, x, mul(sq(acc), x))

# one bit of a public exponent, most significant first: acc^2 (* x)
def pow_bit(b: Bool, +x: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match b:
    case True{}:
      mul(sq(acc), x)
    case False{}:
      sq(acc)

def pow_bits(bs: List<&2, Bool>, +x: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      acc
    case Con{b, bt}:
      pow_bits(bt, x, pow_bit(b, x, acc))

# x^(p - 2) = x^(2^255 - 21): 250 one bits, then 0 1 0 1 1
def inv(+x: List<&2, U32>) -> List<&2, U32>:
  pow_bits([False{}, True{}, False{}, True{}, True{}], x, pow_ones(250n, x, one()))

# x^((p - 5) / 8) = x^(2^252 - 3): 250 one bits, then 0 1
def pow_p58(+x: List<&2, U32>) -> List<&2, U32>:
  pow_bits([False{}, True{}], x, pow_ones(250n, x, one()))

# ---- canonical form ----

def csub_fin(r: Cr, x: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Cr{s, c}:
      select(c, x, s)

# x - p when x >= p, else x (x tight): x + 2^256 - p carries out iff x >= p
def csub(+x: List<&2, U32>) -> List<&2, U32>:
  csub_fin(carry(addl(x, comp_p()), 0), x)

# the canonical representative, below p: 2^256 < 3p
def freeze(+x: List<&2, U32>) -> List<&2, U32>:
  csub(csub(x))

# ---- bytes ----

# the 32-byte little-endian encoding of a canonical element is its limbs
def to_bytes(+x: List<&2, U32>) -> List<&2, U32>:
  freeze(x)

# the last byte with its top bit cleared (RFC 7748 decodeUCoordinate)
def mask_top(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      match xt:
        case Nil{}:
          Con{U32.and(x, 127), Nil{}}
        case Con{y, yt}:
          Con{x, mask_top(Con{y, yt})}

# bytes to an element, bit 255 ignored
def of_bytes(bs: List<&2, U32>) -> List<&2, U32>:
  mask_top(bs)

# 1 when every limb is 0 (x canonical), else 0; no early exit
def or_all(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{x, xt}:
      or_all(xt, U32.or(acc, x))

def is_zero(+x: List<&2, U32>) -> Bool:
  U32.is_eq(or_all(freeze(x), 0), 0)

# a == b in the field
def eq(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  is_zero(sub(a, b))

# the parity of the canonical representative (RFC 8032 x_0)
def low_bit(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{l, lt}:
      U32.and(l, 1)

def parity(+x: List<&2, U32>) -> U32:
  low_bit(freeze(x))
