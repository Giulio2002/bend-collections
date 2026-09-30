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

def reduce_u(xs: List<&2, Nat>) -> List<&2, Nat>:
  L.reduce(c(), 4n, xs)

def reduce(xs: List<&2, Nat>) -> List<&2, Nat>:
  reduce_u(xs)

def zero() -> List<&2, Nat>:
  L.norm16([])

def small(+k: Nat) -> List<&2, Nat>:
  L.norm16([k])

def one() -> List<&2, Nat>:
  small(1n)

def add_u(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  reduce_u(L.add(a, b))

def add_b(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case Nil{}: add_u(a, Nil{})
    case y <> u: add_u(a, y <> u)

def add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: add_b(Nil{}, b)
    case x <> t: add_b(x <> t, b)

def neg_u(a: List<&2, Nat>) -> List<&2, Nat>:
  reduce_u(L.neg_raw(c(), a))

# (one argument: nothing to look at first)
def neg(a: List<&2, Nat>) -> List<&2, Nat>:
  neg_u(a)

def mul_u(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  reduce_u(L.conv(a, b))

def mul_b(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case Nil{}: mul_u(a, Nil{})
    case y <> u: mul_u(a, y <> u)

def mul(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: mul_b(Nil{}, b)
    case x <> t: mul_b(x <> t, b)

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

# the bits of n - 2, most significant first (the proofs show they are those
# of 2^256 - 1 - (c + 1), c + 1 = 2^256 - n + 1)
def inv_bits() -> List<&2, Nat>:
  [1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n,
   1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n,
   1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n,
   1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 0n,
   1n, 0n, 1n, 1n, 1n, 0n, 1n, 0n, 1n, 0n, 1n, 0n, 1n, 1n, 1n, 0n, 1n, 1n, 0n, 1n, 1n, 1n, 0n, 0n, 1n, 1n, 1n, 0n, 0n, 1n, 1n, 0n,
   1n, 0n, 1n, 0n, 1n, 1n, 1n, 1n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 0n, 1n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 1n, 1n, 0n, 1n, 1n,
   1n, 0n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n, 1n, 1n, 1n, 1n, 0n, 1n, 0n, 0n, 0n, 1n, 1n, 0n, 0n,
   1n, 1n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 1n, 0n, 1n, 1n, 0n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, 1n, 1n, 1n, 1n, 1n, 1n]

# a^(n - 2): the inverse of a nonzero a, 0 for 0
def inv(+a: List<&2, Nat>) -> List<&2, Nat>:
  pow(a, inv_bits(), one())

def is_zero(a: List<&2, Nat>) -> Bool:
  L.is_zero(a)

def eq_b(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match b:
    case Nil{}: L.eq(a, Nil{})
    case y <> u: L.eq(a, y <> u)

def eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}: eq_b(Nil{}, b)
    case x <> t: eq_b(x <> t, b)

# a < n, for 16 limbs below 2^16
def lt_n(a: List<&2, Nat>) -> Bool:
  L.ltm(c(), a)

# 2^256 - n - 1
def cm1() -> List<&2, Nat>:
  [48830n, 12233n, 41331n, 16429n, 24516n, 20663n, 8985n, 17745n, 1n]

# a > n / 2 (n is odd), i.e. 2 a >= n + 1 = 2^256 - cm1: the carry out of
# 2 a + cm1
def is_high(a: List<&2, Nat>) -> Bool:
  Bool.not(L.ltm(cm1(), L.scal(2n, a)))

def select(+b: Nat, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  L.select(b, x, y)
