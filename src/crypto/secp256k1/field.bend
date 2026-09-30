import Base
import ./limbs.bend as L
import ./fe.bend as R

# GF(p), p = 2^256 - 2^32 - 977 (SEC 2 section 2.4.1), on 16 limbs of
# radix 2^16 (src/crypto/secp256k1/limbs.bend). Every operation takes and
# returns reduced elements: exactly 16 limbs below 2^16, value below p.
# The contract is spec/crypto/secp256k1/field.bend; the proofs are in
# proofs/crypto/secp256k1/.
#
# Inversion and square root are exponentiations by the public exponents
# p - 2 (Fermat) and (p + 1) / 4 (p = 3 mod 4), square-and-multiply over
# the exponent's bits: the branch is on the public exponent, never on the
# base. The arithmetic runs on records (fe.bend).

# 2^256 - p = 2^32 + 977
def c() -> List<&2, Nat>:
  [977n, 0n, 1n]

def small(+k: Nat) -> List<&2, Nat>:
  L.norm16([k])

def zero() -> List<&2, Nat>:
  small(0n)

def one() -> List<&2, Nat>:
  small(1n)

# The operations run on records (src/crypto/secp256k1/fe.bend), whose
# fields the compiled code keeps in registers; a reduced list is the list of
# its record. Each looks at its first argument first, so that on unknown
# arguments the proof checker keeps it folded (and never computes with a
# constant second argument).

def add_u(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(R.add(R.of_list(a), R.of_list(b)))

def add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: add_u(Nil{}, b)
    case x <> t: add_u(x <> t, b)

def sub_u(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(R.sub(R.of_list(a), R.of_list(b)))

def sub(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: sub_u(Nil{}, b)
    case x <> t: sub_u(x <> t, b)

def neg_u(a: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(R.neg(R.of_list(a)))

def neg(a: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: neg_u(Nil{})
    case x <> t: neg_u(x <> t)

def mul_u(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(R.mul(R.of_list(a), R.of_list(b)))

def mul(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: mul_u(Nil{}, b)
    case x <> t: mul_u(x <> t, b)

def sq(+a: List<&2, Nat>) -> List<&2, Nat>:
  mul(a, a)

# a^e for the exponent e given by its bits (a looked at first)
def powl_u(a: List<&2, Nat>, bits: List<&2, Nat>) -> List<&2, Nat>:
  R.to_list(R.pow(R.of_list(a), bits, R.one()))

def powl(a: List<&2, Nat>, +bits: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}: powl_u(Nil{}, bits)
    case x <> t: powl_u(x <> t, bits)

# the bits of p - 2 = 2^256 - 1 - (c + 1): those of c + 1, flipped
def inv_bits() -> List<&2, Nat>:
  L.cbits(L.bits(L.norm16([978n, 0n, 1n])))

def init2(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse(&2, Nat, L.drop(2n, List.reverse(&2, Nat, xs)))

# the bits of (p + 1) / 4: p + 1 = 2^256 - 1 - (c - 2), without its last two bits
def sqrt_bits() -> List<&2, Nat>:
  init2(L.cbits(L.bits(L.norm16([975n, 0n, 1n]))))

# a^(p - 2): the inverse of a nonzero a, 0 for 0
def inv(a: List<&2, Nat>) -> List<&2, Nat>:
  powl(a, inv_bits())

# a^((p + 1) / 4): a square root of a when a is a square (p = 3 mod 4)
def sqrt(a: List<&2, Nat>) -> List<&2, Nat>:
  powl(a, sqrt_bits())

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

# a mod 2 (the parity of the canonical representative)
def parity(a: List<&2, Nat>) -> Nat:
  Nat.mod(L.hd0(a), 2n)

# a < p, for 16 limbs below 2^16
def lt_p(a: List<&2, Nat>) -> Bool:
  L.ltm(c(), a)

# b ? x : y, branch-free, for b in {0, 1}
def select(+b: Nat, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  L.select(b, x, y)
