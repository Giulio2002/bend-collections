import Base
import ../lib/common.bend as C
import ../../src/math/natural.bend as M
import ../../src/math/number.bend as NB

# Specification of src/math/number.bend: integer extras on Nat
# (python_style_math_stdlib_design.pdf sections 3.2, 8.7 and 10).
#
#   function    clauses                 statements mirror
#   bit_count   BitCount.value          Python int.bit_count; Mathlib
#                                       Nat.bits / List.count true
#   egcd        Egcd.gcd, Egcd.bezout   Knuth 4.5.2 Algorithm X; Mathlib
#                                       Nat.xgcd and Nat.gcd_eq_gcd_ab
#                                       (a * gcdA + b * gcdB = gcd)
#   is_prime    IsPrime.value           Mathlib Nat.Prime (2 <= n and no
#                                       divisor in [2, n)); the trial
#                                       division bound is Mathlib's
#                                       Nat.minFac_sq_le_self

# the 1 bits among the k lowest bits of n
def ones(k: Nat, +n: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(C.bit(n), ones(p, C.half(n)))

# every n is below 2^n, so ones(n, n) counts all of n's 1 bits
def BitCount.value(+n: Nat) -> Type:
  {NB.bit_count(n) == ones(n, n) : Nat}

# the gcd of the extended algorithm is the proved reference's
def eg_gcd(r: NB.EGcd) -> Nat:
  match r:
    case NB.EG{g, x, y, neg}:
      g

def Egcd.gcd(+a: Nat, +b: Nat) -> Type:
  {eg_gcd(NB.egcd(a, b)) == M.gcd(a, b) : Nat}

# the signed Bezout identity a*x - b*y == g (neg false) or b*y - a*x == g
# (neg true), stated without subtraction: the positive side equals g plus
# the negative side
def eg_pos(+a: Nat, +b: Nat, r: NB.EGcd) -> Nat:
  match r:
    case NB.EG{g, +x, +y, neg}:
      match neg:
        case True{}:
          Nat.mul(b, y)
        case False{}:
          Nat.mul(a, x)

def eg_neg(+a: Nat, +b: Nat, r: NB.EGcd) -> Nat:
  match r:
    case NB.EG{+g, +x, +y, neg}:
      match neg:
        case True{}:
          Nat.add(g, Nat.mul(a, x))
        case False{}:
          Nat.add(g, Nat.mul(b, y))

def Egcd.bezout(+a: Nat, +b: Nat) -> Type:
  {eg_pos(a, b, NB.egcd(a, b)) == eg_neg(a, b, NB.egcd(a, b)) : Nat}

# no d in [d, d + k) divides n
def nodiv(k: Nat, +n: Nat, +d: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.not(Nat.is_eq(Nat.mod(n, d), 0n)), nodiv(p, n, 1n+d))

# n is prime: 2 <= n and no d in [2, n) divides n
def prime(+n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      False{}
    case 2n+ +p:
      nodiv(p, 2n+p, 2n)

def IsPrime.value(+n: Nat) -> Type:
  {NB.is_prime(n) == prime(n) : Bool}
