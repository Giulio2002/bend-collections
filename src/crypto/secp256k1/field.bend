import Base
import ./limbs.bend as L

# GF(p), p = 2^256 - 2^32 - 977 (SEC 2 section 2.4.1), on 16 limbs of
# radix 2^16 (src/crypto/secp256k1/limbs.bend). Every operation takes and
# returns reduced elements: exactly 16 limbs below 2^16, value below p.
# The contract is spec/crypto/secp256k1/field.bend; the proofs are in
# proofs/crypto/secp256k1/.
#
# Inversion and square root are exponentiations by the public exponents
# p - 2 (Fermat) and (p + 1) / 4 (p = 3 mod 4), square-and-multiply over
# the exponent's bits: the branch is on the public exponent, never on the
# base.

# 2^256 - p = 2^32 + 977
def c() -> List<&2, Nat>:
  [977n, 0n, 1n]

def reduce(xs: List<&2, Nat>) -> List<&2, Nat>:
  L.reduce(c(), 3n, xs)

def zero() -> List<&2, Nat>:
  L.norm16([])

def small(+k: Nat) -> List<&2, Nat>:
  L.norm16([k])

def one() -> List<&2, Nat>:
  small(1n)

def add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.add(a, b))

def sub(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.add(a, L.negraw(c(), b)))

def neg(a: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.negraw(c(), a))

def mul(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.conv(a, b))

def sq(+a: List<&2, Nat>) -> List<&2, Nat>:
  mul(a, a)

# x^e for the exponent e given by its bits, most significant first
def pow_step(b: Nat, +x: List<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case 0n: s
    case 1n+k: mul(s, x)

def pow(+x: List<&2, Nat>, bits: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}: acc
    case b <> t: pow(x, t, pow_step(b, x, sq(acc)))

# p - 2 = 2^256 - 1 - (c + 1)
def exp_inv() -> List<&2, Nat>:
  L.comp(16n, L.norm16(L.add(c(), [1n])))

# p + 1 = (2^256 - 1 - c) + 2
def exp_p1() -> List<&2, Nat>:
  L.norm16(L.add(L.comp(16n, c()), [2n]))

# a^(p - 2): the inverse of a nonzero a, 0 for 0
def inv(+a: List<&2, Nat>) -> List<&2, Nat>:
  pow(a, L.bits(exp_inv()), one())

def init2(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse(&2, Nat, L.drop(2n, List.reverse(&2, Nat, xs)))

# a^((p + 1) / 4): a square root of a when a is a square (p = 3 mod 4);
# the bits of (p + 1) / 4 are those of p + 1 without the last two
def sqrt(+a: List<&2, Nat>) -> List<&2, Nat>:
  pow(a, init2(L.bits(exp_p1())), one())

def is_zero(a: List<&2, Nat>) -> Bool:
  L.is_zero(a)

def eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  L.eq(a, b)

# a mod 2 (the parity of the canonical representative)
def parity(a: List<&2, Nat>) -> Nat:
  Nat.mod(L.hd0(a), 2n)

def modulus() -> List<&2, Nat>:
  L.modulus(c())

# a < p, for 16 limbs below 2^16
def lt_p(a: List<&2, Nat>) -> Bool:
  L.lt(a, modulus())

# b ? x : y, branch-free, for b in {0, 1}
def select(+b: Nat, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  L.select(b, x, y)
