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

def small(+k: Nat) -> List<&2, Nat>:
  L.norm16([k])

def one() -> List<&2, Nat>:
  small(1n)

def add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.add(a, b))

def neg(a: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.neg_raw(c(), a))

def mul(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  reduce(L.conv(a, b))

def pow_step(b: Nat, +x: List<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case 0n: s
    case 1n+k: mul(s, x)

def pow_go(+x: List<&2, Nat>, bits: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}: acc
    case b <> t: pow_go(x, t, pow_step(b, x, mul(acc, acc)))

# x is looked at first, so that on an unknown x nothing is unfolded
def pow(x: List<&2, Nat>, bits: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match x:
    case Nil{}: pow_go(Nil{}, bits, acc)
    case +y <> +t: pow_go(y <> t, bits, acc)

# the bits of n - 2 = 2^256 - 1 - (c + 1): those of c + 1, flipped
def inv_bits() -> List<&2, Nat>:
  L.cbits(L.bits([48832n, 12233n, 41331n, 16429n, 24516n, 20663n, 8985n, 17745n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]))

# a^(n - 2): the inverse of a nonzero a, 0 for 0
def inv(+a: List<&2, Nat>) -> List<&2, Nat>:
  pow(a, inv_bits(), one())

def is_zero(a: List<&2, Nat>) -> Bool:
  L.is_zero(a)

def eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  L.eq(a, b)

# a < n, for 16 limbs below 2^16
def lt_n(a: List<&2, Nat>) -> Bool:
  L.ltm(c(), a)

# a > n / 2 for a reduced scalar: 2 a >= n (n is odd, so 2 a != n), i.e.
# 2 a + c >= 2^256
def is_high(a: List<&2, Nat>) -> Bool:
  Bool.not(Nat.is_eq(L.top(L.carry(32n, L.add(L.scal(2n, a), c()), 0n)), 0n))

def select(+b: Nat, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  L.select(b, x, y)
