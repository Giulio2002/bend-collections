import Base
import ./pow2.bend as P2

# Exact integer functions of a Python-style math library on the natural
# numbers (Python's non-negative int), after the design reference's
# section 4.2 (math module integer functions), 3.1 (divmod, three-argument
# pow) and 10 (ilog, iroot, clamp, mod_inverse).
#
#   gcd(a, b), gcd_all(xs)       greatest common divisor; gcd_all([]) == 0
#   lcm(a, b), lcm_all(xs)       least common multiple;   lcm_all([]) == 1
#   isqrt(n)                     floor(sqrt(n)), exact for every n
#   iroot(n, k)                  floor of the k-th root (k >= 1)
#   ilog(n, b)                   floor(log_b(n)), exact (n >= 1, b >= 2)
#   factorial(n), perm(n, k)     n!, n! / (n - k)! (0 when k > n)
#   comb(n, k)                   n choose k (0 when k > n)
#   prod(xs), sum(xs)            product and sum of a list; prod([]) == 1
#   pow_mod(b, e, m)             b^e mod m by binary exponentiation
#   mod_inverse(a, m)            x with a*x == 1 (mod m), x < m
#   divmod(a, b)                 (a // b, a % b)
#   bit_length(n)                bits of n without leading zeros
#   clamp(x, lo, hi)             x limited to [lo, hi]
#
# Errors follow the reference's error model (section 2.3) as values, not
# exceptions: ZeroDivision where Python raises ZeroDivisionError or the
# "cannot be 0" ValueError of pow, Domain for the other ValueErrors, and
# NotInvertible for pow(a, -1, m) without an inverse.
#
# Nat is exact; Bend's native backend stops the program on a Nat above
# 2^48 - 1, so results (and the intermediate products of comb, lcm and
# pow_mod) must stay below that at run time. The proofs are over the
# mathematical naturals.

type MathError is Data:
  ZeroDivision{}
  Domain{}
  NotInvertible{}

# the last nonzero remainder of the extended Euclid loop and its
# coefficient: a * coef == gcd (mod m)
type Bezout is Data:
  BZ{gcd: Nat, coef: Nat}

# a // b and a % b
type QuotRem is Data:
  QR{quot: Nat, rem: Nat}

# ---- greatest common divisor, least common multiple ----

# Euclid's algorithm; b <= fuel throughout (every step lowers b).
def gcd_go(fuel: Nat, +a: Nat, +b: Nat) -> Nat:
  match fuel b:
    case 0n _:
      a
    case 1n+f 0n:
      a
    case 1n+f 1n+ +bp:
      gcd_go(f, 1n+bp, Nat.mod(a, 1n+bp))

def gcd(+a: Nat, +b: Nat) -> Nat:
  gcd_go(b, a, b)

def lcm(+a: Nat, +b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ +ap 1n+ +bp:
      Nat.mul(Nat.div(1n+ap, gcd(1n+ap, 1n+bp)), 1n+bp)

def gcd_all_go(xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      gcd_all_go(rest, gcd(acc, x))

def gcd_all(xs: List<&2, Nat>) -> Nat:
  gcd_all_go(xs, 0n)

def lcm_all_go(xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      lcm_all_go(rest, lcm(acc, x))

def lcm_all(xs: List<&2, Nat>) -> Nat:
  lcm_all_go(xs, 1n)

# ---- sums and products ----

def sum_go(xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      sum_go(rest, Nat.add(acc, x))

def sum(xs: List<&2, Nat>) -> Nat:
  sum_go(xs, 0n)

def prod_go(xs: List<&2, Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      prod_go(rest, Nat.mul(acc, x))

def prod(xs: List<&2, Nat>) -> Nat:
  prod_go(xs, 1n)

# ---- factorial, permutations, combinations ----

def factorial_go(n: Nat, +acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+ +p:
      factorial_go(p, Nat.mul(1n+p, acc))

def factorial(+n: Nat) -> Nat:
  factorial_go(n, 1n)

# n * (n - 1) * ... * (n - k + 1)
def perm_go(k: Nat, +m: Nat, +acc: Nat) -> Nat:
  match k:
    case 0n:
      acc
    case 1n+j:
      perm_go(j, Nat.sub(m, 1n), Nat.mul(acc, m))

def perm(+n: Nat, +k: Nat) -> Nat:
  perm_go(k, n, 1n)

# r_{i+1} = r_i * (n - i) / (i + 1): every r_i is C(n, i), so the division
# is exact (reference section 8.6).
def comb_go(j: Nat, +n: Nat, +i: Nat, +r: Nat) -> Nat:
  match j:
    case 0n:
      r
    case 1n+ +jp:
      comb_go(jp, n, 1n+i, Nat.div(Nat.mul(r, Nat.sub(n, i)), 1n+i))

def comb_small(+n: Nat, +k: Nat, +big: Bool) -> Nat:
  match big:
    case True{}:
      0n
    case False{}:
      comb_go(Nat.min(k, Nat.sub(n, k)), n, 0n, 1n)

def comb(+n: Nat, +k: Nat) -> Nat:
  comb_small(n, k, Nat.is_lt(n, k))

# ---- bits ----

def bit_length_go(fuel: Nat, +n: Nat, +k: Nat) -> Nat:
  match fuel n:
    case 0n _:
      k
    case 1n+f 0n:
      k
    case 1n+f 1n+ +np:
      bit_length_go(f, Nat.div(1n+np, 2n), 1n+k)

def bit_length(+n: Nat) -> Nat:
  bit_length_go(n, n, 0n)

# ---- roots and logarithms ----

# Binary search for the last r in [lo, hi) where the test holds, given it
# holds at lo and fails at hi (reference section 8.5 notes the float-sqrt
# shortcut is wrong above 2^52; this search is exact). `more` is lo + 1 < hi
# and `ok` is the test at the midpoint; the fuel bounds the halvings.
def mid(+lo: Nat, +hi: Nat) -> Nat:
  Nat.div(Nat.add(lo, hi), 2n)

# r^k <= n without forming a product above n: `ok` is acc * r <= n, asked
# as acc <= n / r, and acc * r is only formed once it is known to fit.
def pow_le_go(k: Nat, +r: Nat, +acc: Nat, +n: Nat, +ok: Bool) -> Bool:
  match k ok:
    case 0n _:
      True{}
    case 1n+j False{}:
      False{}
    case 1n+j True{}:
      pow_le_go(j, r, Nat.mul(acc, r), n, Nat.is_le(Nat.mul(acc, r), Nat.div(n, r)))

def root_le(+n: Nat, +k: Nat, +r: Nat) -> Bool:
  match k r:
    case 0n _:
      Nat.is_le(1n, n)
    case 1n+kp 0n:
      True{}
    case 1n+ +kp 1n+ +rp:
      pow_le_go(1n+kp, 1n+rp, 1n, n, Nat.is_le(1n, Nat.div(n, 1n+rp)))

# the test is r^k <= n
def search_go(fuel: Nat, +n: Nat, +k: Nat, +lo: Nat, +hi: Nat, +more: Bool, +ok: Bool) -> Nat:
  match fuel more ok:
    case 0n _ _:
      lo
    case 1n+f False{} _:
      lo
    case 1n+f True{} True{}:
      search_go(f, n, k, mid(lo, hi), hi, Nat.is_lt(1n+mid(lo, hi), hi), root_le(n, k, mid(mid(lo, hi), hi)))
    case 1n+f True{} False{}:
      search_go(f, n, k, lo, mid(lo, hi), Nat.is_lt(1n+lo, mid(lo, hi)), root_le(n, k, mid(lo, mid(lo, hi))))

def search(+n: Nat, +k: Nat, +lo: Nat, +hi: Nat) -> Nat:
  search_go(Nat.sub(hi, lo), n, k, lo, hi, Nat.is_lt(1n+lo, hi), root_le(n, k, mid(lo, hi)))

# the largest r with r * r <= n, by Heron's (Newton's) iteration as in Lean 4
# Mathlib's Nat.sqrt: g := (g + n / g) / 2 while that decreases g. Started
# from 2^(b/2 + 1) >= sqrt(n) (n < 2^b, b = bit_length(n)) it converges in
# O(log b) steps; the fuel g bounds the (strictly decreasing) steps.
def sqrt_next(+n: Nat, +g: Nat) -> Nat:
  Nat.div(Nat.add(g, Nat.div(n, g)), 2n)

def sqrt_iter(fuel: Nat, +n: Nat, +g: Nat, +m: Nat, +down: Bool) -> Nat:
  match fuel down:
    case 0n _:
      g
    case 1n+f False{}:
      g
    case 1n+f True{}:
      sqrt_iter(f, n, m, sqrt_next(n, m), Nat.is_lt(sqrt_next(n, m), m))

def isqrt_from(+n: Nat, +g: Nat) -> Nat:
  sqrt_iter(g, n, g, sqrt_next(n, g), Nat.is_lt(sqrt_next(n, g), g))

def isqrt(+n: Nat) -> Nat:
  isqrt_from(n, P2.pow2t(1n+Nat.div(bit_length(n), 2n)))

# the largest r with r^k <= n (k >= 1)
def iroot_k(+n: Nat, +k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n:
      n
    case 2n+ +kp:
      search(n, 2n+kp, 0n, P2.pow2t(1n+Nat.div(bit_length(n), 2n+kp)))

def iroot(+n: Nat, +k: Nat) -> Result<&2, &2, MathError, Nat>:
  match k:
    case 0n:
      Fail{Domain{}}
    case 1n+ +kp:
      Done{iroot_k(n, 1n+kp)}

# the largest k with b^k <= n: p is b^k, `up` is p * b <= n, asked as
# p <= n / b so no product above n is formed
def ilog_go(fuel: Nat, +n: Nat, +b: Nat, +k: Nat, +p: Nat, +up: Bool) -> Nat:
  match fuel up:
    case 0n _:
      k
    case 1n+f False{}:
      k
    case 1n+f True{}:
      ilog_go(f, n, b, 1n+k, Nat.mul(p, b), Nat.is_le(Nat.mul(p, b), Nat.div(n, b)))

def ilog_ok(+n: Nat, +b: Nat, +bad: Bool) -> Result<&2, &2, MathError, Nat>:
  match bad:
    case True{}:
      Fail{Domain{}}
    case False{}:
      Done{ilog_go(n, n, b, 0n, 1n, Nat.is_le(1n, Nat.div(n, b)))}

def ilog(+n: Nat, +b: Nat) -> Result<&2, &2, MathError, Nat>:
  ilog_ok(n, b, Bool.or(Nat.is_eq(n, 0n), Nat.is_lt(b, 2n)))

# ---- modular arithmetic ----

# right-to-left binary exponentiation, reducing mod m after every product:
# acc * base^e == b^e0 (mod m) throughout
def pow_mod_odd(+m: Nat, +bit: Nat, +base: Nat, +acc: Nat) -> Nat:
  match bit:
    case 0n:
      acc
    case 1n+z:
      Nat.mod(Nat.mul(acc, base), m)

def pow_mod_go(fuel: Nat, +m: Nat, +e: Nat, +base: Nat, +acc: Nat) -> Nat:
  match fuel e:
    case 0n _:
      acc
    case 1n+f 0n:
      acc
    case 1n+f 1n+ +ep:
      pow_mod_go(f, m, Nat.div(1n+ep, 2n), Nat.mod(Nat.mul(base, base), m), pow_mod_odd(m, Nat.mod(1n+ep, 2n), base, acc))

def pow_mod(+b: Nat, +e: Nat, +m: Nat) -> Result<&2, &2, MathError, Nat>:
  match m:
    case 0n:
      Fail{ZeroDivision{}}
    case 1n+ +mp:
      Done{pow_mod_go(e, 1n+mp, e, Nat.mod(b, 1n+mp), Nat.mod(1n, 1n+mp))}

# Extended Euclid on (m, a mod m) keeping only the coefficient of a, mod m:
# a * s0 == r0 and a * s1 == r1 (mod m). The remainders are gcd's.
def inv_step(+m: Nat, +q: Nat, +s0: Nat, +s1: Nat) -> Nat:
  Nat.mod(Nat.add(s0, Nat.sub(m, Nat.mod(Nat.mul(q, s1), m))), m)

def inv_go(fuel: Nat, +m: Nat, +r0: Nat, +s0: Nat, +r1: Nat, +s1: Nat) -> Bezout:
  match fuel r1:
    case 0n _:
      BZ{r0, s0}
    case 1n+f 0n:
      BZ{r0, s0}
    case 1n+f 1n+ +rp:
      inv_go(f, m, 1n+rp, s1, Nat.mod(r0, 1n+rp), inv_step(m, Nat.div(r0, 1n+rp), s0, s1))

def inv_fin(+m: Nat, bz: Bezout) -> Result<&2, &2, MathError, Nat>:
  match bz:
    case BZ{1n, s}:
      Done{Nat.mod(s, m)}
    case BZ{0n, s}:
      Fail{NotInvertible{}}
    case BZ{2n+g, s}:
      Fail{NotInvertible{}}

# pow(a, -1, m): the x < m with a * x == 1 (mod m)
def mod_inverse(+a: Nat, +m: Nat) -> Result<&2, &2, MathError, Nat>:
  match m:
    case 0n:
      Fail{ZeroDivision{}}
    case 1n+ +mp:
      inv_fin(1n+mp, inv_go(1n+mp, 1n+mp, 1n+mp, 0n, Nat.mod(a, 1n+mp), 1n))

# ---- division and clamping ----

def divmod(+a: Nat, +b: Nat) -> Result<&2, &2, MathError, QuotRem>:
  match b:
    case 0n:
      Fail{ZeroDivision{}}
    case 1n+ +bp:
      Done{QR{Nat.div(a, 1n+bp), Nat.mod(a, 1n+bp)}}

def clamp_ok(+x: Nat, +lo: Nat, +hi: Nat, +bad: Bool) -> Result<&2, &2, MathError, Nat>:
  match bad:
    case True{}:
      Fail{Domain{}}
    case False{}:
      Done{Nat.min(Nat.max(x, lo), hi)}

def clamp(+x: Nat, +lo: Nat, +hi: Nat) -> Result<&2, &2, MathError, Nat>:
  clamp_ok(x, lo, hi, Nat.is_lt(hi, lo))
