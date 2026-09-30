import Base
import ../../lib/common.bend as C

# GF(p) and Z/nZ for secp256k1 (SEC 2 section 2.4.1), over the natural
# numbers: p = 2^256 - 2^32 - 977, n the group order. Nothing of the
# implementation is used; this is the arithmetic of HACL*'s Spec.K256
# (felem / qelem: add, sub, mul, finv by Fermat, fsqrt by (p + 1) / 4).
#
# The proof checker keeps closed natural numbers in unary, so no 256-bit
# constant is ever written closed: 2^k is C.shift(k, one) and a constant is
# digits(one, ds), both with `one` a variable that every clause takes with
# the hypothesis {one == 1n : Nat}. For one == 1 they are the usual
# constants; no other value satisfies the hypothesis, so each clause says
# exactly what it says with the constants written out (the device of
# spec/math/w64.bend and spec/crypto/curve25519/field.bend).

# a number from its little-endian radix-2^16 digits, each scaled by one:
# digits(1, [d0, d1, ...]) = d0 + 2^16 d1 + ...
def digits(+one: Nat, ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> dt:
      Nat.add(Nat.mul(one, d), C.shift(16n, digits(one, dt)))

# 2^256
def w256(+one: Nat) -> Nat:
  C.shift(256n, one)

# 2^256 - p = 2^32 + 977, and p
def cp(+one: Nat) -> Nat:
  digits(one, [977n, 0n, 1n])

def prime(+one: Nat) -> Nat:
  Nat.sub(w256(one), cp(one))

# 2^256 - n = 432420386565659656852420866390673177327, and n
def cn(+one: Nat) -> Nat:
  digits(one, [48831n, 12233n, 41331n, 16429n, 24516n, 20663n, 8985n, 17745n, 1n])

def order(+one: Nat) -> Nat:
  Nat.sub(w256(one), cn(one))

# ---- arithmetic modulo m (m = p for the field, m = n for scalars) ----

def madd(+m: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.add(a, b), m)

# a - b mod m
def msub(+m: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.sub(Nat.add(a, m), Nat.mod(b, m)), m)

def mneg(+m: Nat, a: Nat) -> Nat:
  msub(m, 0n, a)

def mmul(+m: Nat, a: Nat, b: Nat) -> Nat:
  Nat.mod(Nat.mul(a, b), m)

def mpow(+m: Nat, a: Nat, e: Nat) -> Nat:
  Nat.mod(Nat.pow(a, e), m)

# a^(m - 2): for a prime m the inverse of a nonzero a (Fermat); 0 for 0
def minv(+m: Nat, a: Nat) -> Nat:
  mpow(m, a, Nat.sub(m, 2n))

# a^((p + 1) / 4): a square root of a whenever a is a square mod p
# (p = 3 mod 4)
def fsqrt(+m: Nat, a: Nat) -> Nat:
  mpow(m, a, Nat.div(Nat.add(m, 1n), 4n))

# ---- the representation (for the clauses) ----

# the value of little-endian radix-2^16 limbs
def value(+one: Nat, xs: List<&2, Nat>) -> Nat:
  digits(one, xs)

# exactly 16 limbs, each below 2^16
def limbs16(+one: Nat, n: Nat, xs: List<&2, Nat>) -> Bool:
  match n xs:
    case 0n Nil{}:
      True{}
    case 0n x <> t:
      False{}
    case 1n+k Nil{}:
      False{}
    case 1n+k x <> t:
      Bool.and(Nat.is_lt(x, C.shift(16n, one)), limbs16(one, k, t))

# a reduced element mod m: 16 limbs below 2^16 of value below m
def reduced(+one: Nat, +m: Nat, +xs: List<&2, Nat>) -> Bool:
  Bool.and(limbs16(one, 16n, xs), Nat.is_lt(value(one, xs), m))
