import Base

# Integer extras on the natural numbers, after the design reference's
# section 3.2 (int.bit_count), 8.7 (the extended Euclidean algorithm) and 10
# (egcd, is_prime), next to natural.bend's section 4.2 functions.
#
#   bit_count(n)       the number of 1 bits of n (Python's int.bit_count)
#   egcd(a, b)         gcd(a, b) with its Bezout coefficients (see EGcd)
#   is_prime(n)        n is prime, by trial division up to sqrt(n)
#
# Nat is exact; Bend's native backend stops the program on a Nat above
# 2^48 - 1 (natural.bend), so is_prime is meant for n below that. The proofs
# are over the mathematical naturals.

# gcd(a, b) and signed Bezout coefficients split into magnitudes and a sign:
#   neg == False:  a * x == gcd + b * y      (a*x - b*y == gcd)
#   neg == True:   b * y == gcd + a * x      (b*y - a*x == gcd)
# Python's egcd would return one negative coefficient; the unsigned library
# returns both magnitudes and says which side carries the minus sign.
type EGcd is Data:
  EG{gcd: Nat, x: Nat, y: Nat, neg: Bool}

# ---- bit count ----

# n halves every step, so n steps are enough
def bit_count_go(fuel: Nat, +n: Nat, +acc: Nat) -> Nat:
  match fuel n:
    case 0n _:
      acc
    case 1n+f 0n:
      acc
    case 1n+f 1n+ +np:
      bit_count_go(f, Nat.div(1n+np, 2n), Nat.add(acc, Nat.mod(1n+np, 2n)))

def bit_count(+n: Nat) -> Nat:
  bit_count_go(n, n, 0n)

# ---- extended Euclid ----

# From the child (b, a mod b) to the parent (a, b): with q = a div b the
# coefficients become (y', x' + q*y') and the sign flips (Knuth 4.5.2,
# algorithm X, in magnitudes).
def eg_up(+q: Nat, r: EGcd) -> EGcd:
  match r:
    case EG{+g, +x, +y, neg}:
      EG{g, y, Nat.add(x, Nat.mul(q, y)), Bool.not(neg)}

# b <= fuel throughout, as in natural.bend's gcd_go
def egcd_go(fuel: Nat, +a: Nat, +b: Nat) -> EGcd:
  match fuel b:
    case 0n _:
      EG{a, 1n, 0n, False{}}
    case 1n+f 0n:
      EG{a, 1n, 0n, False{}}
    case 1n+ +f 1n+ +bp:
      eg_up(Nat.div(a, 1n+bp), egcd_go(f, 1n+bp, Nat.mod(a, 1n+bp)))

def egcd(+a: Nat, +b: Nat) -> EGcd:
  egcd_go(b, a, b)

# ---- primality ----

# trial division: no d in [2, n) divides n iff none in [2, isqrt(n)] does.
# `done` is n < d*d, `divides` is d | n, both for the current d.
def prime_go(fuel: Nat, +n: Nat, +d: Nat, done: Bool, divides: Bool) -> Bool:
  match fuel done divides:
    case 0n _ _:
      True{}
    case 1n+f True{} _:
      True{}
    case 1n+f False{} True{}:
      False{}
    case 1n+ +f False{} False{}:
      prime_go(f, n, 1n+d, Nat.is_lt(n, Nat.mul(1n+d, 1n+d)), Nat.is_eq(Nat.mod(n, 1n+d), 0n))

def is_prime(+n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      False{}
    case 2n+ +p:
      prime_go(2n+p, 2n+p, 2n, Nat.is_lt(2n+p, 4n), Nat.is_eq(Nat.mod(2n+p, 2n), 0n))
