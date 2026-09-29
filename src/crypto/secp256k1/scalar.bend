import Base
import ./limbs.bend as L

# Integers modulo the group order
# n = 2^256 - 432420386565659656852420866390673177327 (SEC 2 section 2.4.1),
# on 16 limbs of radix 2^16 (src/crypto/secp256k1/limbs.bend), reduced
# (exactly 16 limbs below 2^16, value below n). The contract is
# spec/crypto/secp256k1/scalar.bend.

# 2^256 - n, in radix 2^16
def c() -> List<&2, Nat>:
  [48831n, 12233n, 41331n, 16429n, 24516n, 20663n, 8985n, 17745n, 1n]

def reduce(xs: List<&2, Nat>) -> List<&2, Nat>:
  L.reduce(c(), 4n, xs)

def zero() -> List<&2, Nat>:
  L.norm16([])

def one() -> List<&2, Nat>:
  L.norm16([1n])

def add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.add(a, b))

def neg(a: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.negraw(c(), a))

def mul(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.conv(a, b))

def pow_step(b: Nat, +x: List<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case 0n: s
    case 1n+k: mul(s, x)

def pow(+x: List<&2, Nat>, bits: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}: acc
    case b <> t: pow(x, t, pow_step(b, x, mul(acc, acc)))

# n - 2 = 2^256 - 1 - (c + 1)
def exp_inv() -> List<&2, Nat>:
  L.comp(16n, L.norm16(L.add(c(), [1n])))

# a^(n - 2): the inverse of a nonzero a, 0 for 0
def inv(+a: List<&2, Nat>) -> List<&2, Nat>:
  pow(a, L.bits(exp_inv()), one())

def is_zero(a: List<&2, Nat>) -> Bool:
  L.is_zero(a)

def eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  L.eq(a, b)

def modulus() -> List<&2, Nat>:
  L.modulus(c())

# a < n, for 16 limbs below 2^16
def lt_n(a: List<&2, Nat>) -> Bool:
  L.lt(a, modulus())

# a > n / 2, i.e. n < 2 a (n is odd), for a reduced scalar
def is_high(+a: List<&2, Nat>) -> Bool:
  L.lt(List.append(&2, Nat, modulus(), [0n]), L.take(17n, L.carry(32n, L.scal(2n, a), 0n)))

def select(+b: Nat, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  L.select(b, x, y)
