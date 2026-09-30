import Base
import ./limbs.bend as L
import ./fe.bend as R
import ./se.bend as SE

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

# The product runs on records (se.bend, reduction as L.reduce(c, 4n, xs)),
# whose fields the compiled code keeps in registers; a reduced list is the
# list of its record. The first argument is looked at first.
def mul_u(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(SE.mul(R.of_list(a), R.of_list(b)))

def mul(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: mul_u(Nil{}, b)
    case x <> t: mul_u(x <> t, b)

# a^e for the exponent e given by its bits, on records (a looked at first)
def powl_u(a: List<&2, Nat>, bits: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(SE.pow(R.of_list(a), bits, SE.one()))

def powl(a: List<&2, Nat>, +bits: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: powl_u(Nil{}, bits)
    case x <> t: powl_u(x <> t, bits)

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
def inv(a: List<&2, Nat>) -> List<&2, Nat>:
  powl(a, inv_bits())

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
