import Base
import ./num.bend as N

# The math of natural.bend written once for any numeric type (num.bend).
# Every function takes its type and interface as templates (~T, ~num), so an
# instance (instances.bend: U32, U64, F32, F64) is compiled with the
# operations inlined.
#
#   ordered-ring functions (any Arith, floats included):
#     min, max, clamp, abs, sign, sum, prod, pow (exponent a Nat)
#   integer functions (an unsigned Integer):
#     gcd, lcm, gcd_all, lcm_all, bit_length, isqrt, iroot, ilog,
#     factorial, perm, comb, pow_mod, mod_inverse, divmod
#
# Semantics are Python's, with checked results for fixed widths (design
# reference section 2.6): a result that does not fit is Fail{Overflow}, never
# a wrapped value. comb reduces by a gcd at every step, so it overflows only
# when the result does; pow_mod and mod_inverse multiply mod m by doubling, so
# no intermediate exceeds 2m. Loops are bounded by the bit width (fuel). The
# Nat versions in natural.bend are the proved reference; these are tested
# against Python (tools/check_generic.py). sum is a left fold (Python's float
# sum is compensated; use it for exact float sums once fsum exists).

type QuotRem<-T: Data> is Data:
  QR{quot: T, rem: T}

def fst(-T: Data, p: T & T) -> T:
  (a, b) = p
  a

def snd(-T: Data, p: T & T) -> T:
  (a, b) = p
  b

def ok(-T: Data, m: Maybe<&2, T>) -> Result<&2, &2, N.NumError, T>:
  match m:
    case None{}:
      Fail{N.Overflow{}}
    case Some{x}:
      Done{x}

def or_zero(-T: Data, +z: T, m: Maybe<&2, T>) -> T:
  match m:
    case None{}:
      z
    case Some{x}:
      x

# ---- ordered-ring functions ----

# Python's min(a, b) keeps a unless b < a; max keeps a unless a < b.
def min(~T: Data, ~num: N.Arith<T>, +a: T, +b: T) -> T:
  Bool.pick(T, N.lt(T, num, b, a), b, a)

def max(~T: Data, ~num: N.Arith<T>, +a: T, +b: T) -> T:
  Bool.pick(T, N.lt(T, num, a, b), b, a)

def clamp_ok(~T: Data, ~num: N.Arith<T>, +x: T, +lo: T, +hi: T, bad: Bool) -> Result<&2, &2, N.NumError, T>:
  match bad:
    case True{}:
      Fail{N.Domain{}}
    case False{}:
      Done{min(~T, ~num, max(~T, ~num, x, lo), hi)}

def clamp(~T: Data, ~num: N.Arith<T>, +x: T, +lo: T, +hi: T) -> Result<&2, &2, N.NumError, T>:
  clamp_ok(~T, ~num, x, lo, hi, N.lt(T, num, hi, lo))

def abs(~T: Data, ~num: N.Arith<T>, x: T) -> T:
  N.abs(T, num, x)

def sign_neg(-T: Data, +x: T, m: Maybe<&2, T>) -> T:
  match m:
    case None{}:
      x
    case Some{y}:
      y

def sign_below(~T: Data, ~num: N.Arith<T>, +x: T, below: Bool) -> T:
  match below:
    case True{}:
      sign_neg(T, x, N.neg(T, num, N.one(T, num)))
    case False{}:
      x

def sign_above(~T: Data, ~num: N.Arith<T>, +x: T, above: Bool) -> T:
  match above:
    case True{}:
      N.one(T, num)
    case False{}:
      sign_below(~T, ~num, x, N.lt(T, num, x, N.zero(T, num)))

# 1 above zero, -1 below, x itself otherwise (0, -0.0, NaN)
def sign(~T: Data, ~num: N.Arith<T>, +x: T) -> T:
  sign_above(~T, ~num, x, N.lt(T, num, N.zero(T, num), x))

def sum_go(~T: Data, ~num: N.Arith<T>, xs: List<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} None{}:
      None{}
    case Con{x, rest} Some{a}:
      sum_go(~T, ~num, rest, N.add(T, num, a, x))

def sum(~T: Data, ~num: N.Arith<T>, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  ok(T, sum_go(~T, ~num, xs, Some{N.zero(T, num)}))

def prod_go(~T: Data, ~num: N.Arith<T>, xs: List<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} None{}:
      None{}
    case Con{x, rest} Some{a}:
      prod_go(~T, ~num, rest, N.mul(T, num, a, x))

def prod(~T: Data, ~num: N.Arith<T>, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  ok(T, prod_go(~T, ~num, xs, Some{N.one(T, num)}))

def mul2(~T: Data, ~num: N.Arith<T>, a: Maybe<&2, T>, b: Maybe<&2, T>) -> Maybe<&2, T>:
  match a b:
    case Some{x} Some{y}:
      N.mul(T, num, x, y)
    case _ _:
      None{}

def pow_bit(~T: Data, ~num: N.Arith<T>, +bit: Nat, +base: Maybe<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match bit:
    case 0n:
      acc
    case 1n+z:
      mul2(~T, ~num, acc, base)

def pow_square(~T: Data, ~num: N.Arith<T>, more: Bool, +base: Maybe<&2, T>) -> Maybe<&2, T>:
  match more:
    case False{}:
      base
    case True{}:
      mul2(~T, ~num, base, base)

# square-and-multiply; the base is squared only while higher exponent bits
# remain, so an overflowing square means the result overflows too
def pow_go(~T: Data, ~num: N.Arith<T>, fuel: Nat, +k: Nat, +base: Maybe<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match fuel k:
    case 0n _:
      acc
    case 1n+f 0n:
      acc
    case 1n+f 1n+ +kp:
      pow_go(~T, ~num, f, Nat.div(1n+kp, 2n), pow_square(~T, ~num, Nat.is_lt(1n, 1n+kp), base), pow_bit(~T, ~num, Nat.mod(1n+kp, 2n), base, acc))

def pow(~T: Data, ~num: N.Arith<T>, +x: T, +k: Nat) -> Result<&2, &2, N.NumError, T>:
  ok(T, pow_go(~T, ~num, 1n+k, k, Some{x}, Some{N.one(T, num)}))

# ---- integer functions (unsigned) ----

def is_pos(~T: Data, ~num: N.Integer<T>, x: T) -> Bool:
  N.lt(T, N.ar(T, num), N.zero(T, N.ar(T, num)), x)

def ilt(~T: Data, ~num: N.Integer<T>, x: T, y: T) -> Bool:
  N.lt(T, N.ar(T, num), x, y)

def ile(~T: Data, ~num: N.Integer<T>, x: T, y: T) -> Bool:
  Bool.not(N.lt(T, N.ar(T, num), y, x))

def izero(~T: Data, ~num: N.Integer<T>) -> T:
  N.zero(T, N.ar(T, num))

def ione(~T: Data, ~num: N.Integer<T>) -> T:
  N.one(T, N.ar(T, num))

def nat(~T: Data, ~num: N.Integer<T>, n: Nat) -> T:
  or_zero(T, izero(~T, ~num), N.from_nat(T, num, n))

def quot(~T: Data, ~num: N.Integer<T>, x: T, y: T) -> T:
  fst(T, N.divmod(T, num, x, y))

def rem(~T: Data, ~num: N.Integer<T>, x: T, y: T) -> T:
  snd(T, N.divmod(T, num, x, y))

# a - b for b <= a (never None then)
def isub(~T: Data, ~num: N.Integer<T>, +a: T, b: T) -> T:
  or_zero(T, a, N.sub(T, N.ar(T, num), a, b))

def iadd(~T: Data, ~num: N.Integer<T>, a: T, b: T) -> Maybe<&2, T>:
  N.add(T, N.ar(T, num), a, b)

def imul(~T: Data, ~num: N.Integer<T>, a: T, b: T) -> Maybe<&2, T>:
  N.mul(T, N.ar(T, num), a, b)

def fuel(~T: Data, ~num: N.Integer<T>) -> Nat:
  Nat.add(Nat.double(N.width(T, num)), 4n)

# Euclid's algorithm; the width bounds the steps (Fibonacci: < 1.5 w + 2)
def gcd_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +a: T, +b: T, pos: Bool) -> T:
  match fuel pos:
    case 0n _:
      a
    case 1n+f False{}:
      a
    case 1n+f True{}:
      gcd_go(~T, ~num, f, b, rem(~T, ~num, a, b), is_pos(~T, ~num, rem(~T, ~num, a, b)))

def gcd(~T: Data, ~num: N.Integer<T>, +a: T, +b: T) -> T:
  gcd_go(~T, ~num, fuel(~T, ~num), a, b, is_pos(~T, ~num, b))

def lcm_ok(~T: Data, ~num: N.Integer<T>, +a: T, +b: T, zero: Bool) -> Result<&2, &2, N.NumError, T>:
  match zero:
    case True{}:
      Done{izero(~T, ~num)}
    case False{}:
      ok(T, imul(~T, ~num, quot(~T, ~num, a, gcd(~T, ~num, a, b)), b))

def lcm(~T: Data, ~num: N.Integer<T>, +a: T, +b: T) -> Result<&2, &2, N.NumError, T>:
  lcm_ok(~T, ~num, a, b, Bool.or(Bool.not(is_pos(~T, ~num, a)), Bool.not(is_pos(~T, ~num, b))))

def gcd_all_go(~T: Data, ~num: N.Integer<T>, xs: List<&2, T>, +acc: T) -> T:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      gcd_all_go(~T, ~num, rest, gcd(~T, ~num, acc, x))

def gcd_all(~T: Data, ~num: N.Integer<T>, xs: List<&2, T>) -> T:
  gcd_all_go(~T, ~num, xs, izero(~T, ~num))

def lcm_all_go(~T: Data, ~num: N.Integer<T>, xs: List<&2, T>, acc: Result<&2, &2, N.NumError, T>) -> Result<&2, &2, N.NumError, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} Fail{e}:
      Fail{e}
    case Con{+x, rest} Done{+a}:
      lcm_all_go(~T, ~num, rest, lcm(~T, ~num, a, x))

def lcm_all(~T: Data, ~num: N.Integer<T>, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  lcm_all_go(~T, ~num, xs, Done{ione(~T, ~num)})

def bit_length_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +n: T, +k: Nat, pos: Bool) -> Nat:
  match fuel pos:
    case 0n _:
      k
    case 1n+f False{}:
      k
    case 1n+f True{}:
      bit_length_go(~T, ~num, f, N.shr1(T, num, n), 1n+k, is_pos(~T, ~num, N.shr1(T, num, n)))

def bit_length(~T: Data, ~num: N.Integer<T>, +n: T) -> Nat:
  bit_length_go(~T, ~num, fuel(~T, ~num), n, 0n, is_pos(~T, ~num, n))

def pow2(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# Heron's iteration from 2^(b/2 + 1) >= sqrt(n), as natural.bend (Mathlib's
# Nat.sqrt): g stays >= floor(sqrt n) and g + n/g <= 2 g, so nothing overflows
def sqrt_next(~T: Data, ~num: N.Integer<T>, +n: T, +g: T) -> T:
  N.shr1(T, num, or_zero(T, g, iadd(~T, ~num, g, quot(~T, ~num, n, g))))

def sqrt_iter(~T: Data, ~num: N.Integer<T>, fuel: Nat, +n: T, +g: T, +m: T, down: Bool) -> T:
  match fuel down:
    case 0n _:
      g
    case 1n+f False{}:
      g
    case 1n+f True{}:
      sqrt_iter(~T, ~num, f, n, m, sqrt_next(~T, ~num, n, m), ilt(~T, ~num, sqrt_next(~T, ~num, n, m), m))

def isqrt_from(~T: Data, ~num: N.Integer<T>, +n: T, +g: T) -> T:
  sqrt_iter(~T, ~num, fuel(~T, ~num), n, g, sqrt_next(~T, ~num, n, g), ilt(~T, ~num, sqrt_next(~T, ~num, n, g), g))

def isqrt_pos(~T: Data, ~num: N.Integer<T>, +n: T, pos: Bool) -> T:
  match pos:
    case False{}:
      n
    case True{}:
      isqrt_from(~T, ~num, n, nat(~T, ~num, pow2(1n+Nat.div(bit_length(~T, ~num, n), 2n))))

def isqrt(~T: Data, ~num: N.Integer<T>, +n: T) -> T:
  isqrt_pos(~T, ~num, n, is_pos(~T, ~num, n))

def mul_ok(~T: Data, ~num: N.Integer<T>, acc: Maybe<&2, T>, +x: T) -> Maybe<&2, T>:
  match acc:
    case None{}:
      None{}
    case Some{a}:
      imul(~T, ~num, a, x)

def inc(~T: Data, ~num: N.Integer<T>, +x: T) -> T:
  or_zero(T, x, iadd(~T, ~num, x, ione(~T, ~num)))

def dec(~T: Data, ~num: N.Integer<T>, +x: T) -> T:
  isub(~T, ~num, x, ione(~T, ~num))

# ---- roots and logarithms ----

# r^k <= n, with an overflowing power counted as > n
def root_le_fin(~T: Data, ~num: N.Integer<T>, +n: T, p: Maybe<&2, T>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{x}:
      ile(~T, ~num, x, n)

def root_le(~T: Data, ~num: N.Integer<T>, +n: T, +k: Nat, +r: T) -> Bool:
  root_le_fin(~T, ~num, n, pow_go(~T, ~N.ar(T, num), 1n+k, k, Some{r}, Some{ione(~T, ~num)}))

# lo + (hi - lo) / 2, never above hi
def imid(~T: Data, ~num: N.Integer<T>, +lo: T, +hi: T) -> T:
  or_zero(T, lo, iadd(~T, ~num, lo, N.shr1(T, num, isub(~T, ~num, hi, lo))))

# the last r in [lo, hi) with r^k <= n, given it holds at lo and fails at
# hi; m is the midpoint and ok the test there
def search_go(~T: Data, ~num: N.Integer<T>, fu: Nat, +n: T, +k: Nat, +lo: T, +hi: T, +m: T, +more: Bool, +hit: Bool) -> T:
  match fu more hit:
    case 0n _ _:
      lo
    case 1n+f False{} _:
      lo
    case 1n+f True{} True{}:
      search_go(~T, ~num, f, n, k, m, hi, imid(~T, ~num, m, hi), ilt(~T, ~num, inc(~T, ~num, m), hi), root_le(~T, ~num, n, k, imid(~T, ~num, m, hi)))
    case 1n+f True{} False{}:
      search_go(~T, ~num, f, n, k, lo, m, imid(~T, ~num, lo, m), ilt(~T, ~num, inc(~T, ~num, lo), m), root_le(~T, ~num, n, k, imid(~T, ~num, lo, m)))

def search(~T: Data, ~num: N.Integer<T>, +n: T, +k: Nat, +hi: T) -> T:
  search_go(~T, ~num, fuel(~T, ~num), n, k, izero(~T, ~num), hi, imid(~T, ~num, izero(~T, ~num), hi), ilt(~T, ~num, ione(~T, ~num), hi), root_le(~T, ~num, n, k, imid(~T, ~num, izero(~T, ~num), hi)))

def iroot_k(~T: Data, ~num: N.Integer<T>, +n: T, +k: Nat) -> T:
  match k:
    case 0n:
      izero(~T, ~num)
    case 1n:
      n
    case 2n+ +kp:
      search(~T, ~num, n, 2n+kp, nat(~T, ~num, pow2(1n+Nat.div(bit_length(~T, ~num, n), 2n+kp))))

def iroot(~T: Data, ~num: N.Integer<T>, +n: T, +k: Nat) -> Result<&2, &2, N.NumError, T>:
  match k:
    case 0n:
      Fail{N.Domain{}}
    case 1n+ +kp:
      Done{iroot_k(~T, ~num, n, 1n+kp)}

# the largest k with b^k <= n; p <= n / b is asked before p * b is formed
def ilog_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +n: T, +b: T, +k: Nat, +p: T, up: Bool) -> Nat:
  match fuel up:
    case 0n _:
      k
    case 1n+f False{}:
      k
    case 1n+f True{}:
      ilog_go(~T, ~num, f, n, b, 1n+k, or_zero(T, p, imul(~T, ~num, p, b)), ile(~T, ~num, or_zero(T, p, imul(~T, ~num, p, b)), quot(~T, ~num, n, b)))

def ilog_ok(~T: Data, ~num: N.Integer<T>, +n: T, +b: T, bad: Bool) -> Result<&2, &2, N.NumError, Nat>:
  match bad:
    case True{}:
      Fail{N.Domain{}}
    case False{}:
      Done{ilog_go(~T, ~num, fuel(~T, ~num), n, b, 0n, ione(~T, ~num), ile(~T, ~num, ione(~T, ~num), quot(~T, ~num, n, b)))}

def ilog(~T: Data, ~num: N.Integer<T>, +n: T, +b: T) -> Result<&2, &2, N.NumError, Nat>:
  ilog_ok(~T, ~num, n, b, Bool.or(Bool.not(is_pos(~T, ~num, n)), ilt(~T, ~num, b, nat(~T, ~num, 2n))))

# ---- factorial, permutations, combinations ----

# i! for i up to n: every factor above 1 at least doubles the product, so a
# product still unfinished after width + 2 steps has overflowed
def fact_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +i: T, +n: T, acc: Maybe<&2, T>, more: Bool) -> Maybe<&2, T>:
  match fuel more:
    case 0n _:
      None{}
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      fact_go(~T, ~num, f, inc(~T, ~num, i), n, mul_ok(~T, ~num, acc, i), Bool.and(ilt(~T, ~num, i, n), N.lt(T, N.ar(T, num), i, inc(~T, ~num, i))))

def factorial(~T: Data, ~num: N.Integer<T>, +n: T) -> Result<&2, &2, N.NumError, T>:
  ok(T, fact_go(~T, ~num, 1n+fuel(~T, ~num), ione(~T, ~num), n, Some{ione(~T, ~num)}, ile(~T, ~num, ione(~T, ~num), n)))

# n (n - 1) ... (n - k + 1); the factors are >= 2 but for a last 1
def perm_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +k: T, +m: T, acc: Maybe<&2, T>, more: Bool) -> Maybe<&2, T>:
  match fuel more:
    case 0n _:
      None{}
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      perm_go(~T, ~num, f, dec(~T, ~num, k), dec(~T, ~num, m), mul_ok(~T, ~num, acc, m), is_pos(~T, ~num, dec(~T, ~num, k)))

def perm_big(~T: Data, ~num: N.Integer<T>, +n: T, +k: T, big: Bool) -> Result<&2, &2, N.NumError, T>:
  match big:
    case True{}:
      Done{izero(~T, ~num)}
    case False{}:
      ok(T, perm_go(~T, ~num, 1n+fuel(~T, ~num), k, n, Some{ione(~T, ~num)}, is_pos(~T, ~num, k)))

def perm(~T: Data, ~num: N.Integer<T>, +n: T, +k: T) -> Result<&2, &2, N.NumError, T>:
  perm_big(~T, ~num, n, k, ilt(~T, ~num, n, k))

# r_{i+1} = C(n, i+1) = (r_i / g) * ((n - i) / ((i + 1) / g)), g = gcd(r_i,
# i + 1): exact, and it overflows only if C(n, i+1) does (C(n, i) grows for
# i <= n / 2); C(n, i) >= 2^i there, so width + 2 steps settle it
def comb_next(~T: Data, ~num: N.Integer<T>, +n: T, +i: T, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match acc:
    case None{}:
      None{}
    case Some{+r}:
      imul(~T, ~num, quot(~T, ~num, r, gcd(~T, ~num, r, inc(~T, ~num, i))), quot(~T, ~num, isub(~T, ~num, n, i), quot(~T, ~num, inc(~T, ~num, i), gcd(~T, ~num, r, inc(~T, ~num, i)))))

def comb_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +n: T, +i: T, +j: T, acc: Maybe<&2, T>, more: Bool) -> Maybe<&2, T>:
  match fuel more:
    case 0n _:
      None{}
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      comb_go(~T, ~num, f, n, inc(~T, ~num, i), j, comb_next(~T, ~num, n, i, acc), ilt(~T, ~num, inc(~T, ~num, i), j))

def comb_big(~T: Data, ~num: N.Integer<T>, +n: T, +k: T, big: Bool) -> Result<&2, &2, N.NumError, T>:
  match big:
    case True{}:
      Done{izero(~T, ~num)}
    case False{}:
      ok(T, comb_go(~T, ~num, 1n+fuel(~T, ~num), n, izero(~T, ~num), min(~T, ~N.ar(T, num), k, isub(~T, ~num, n, k)), Some{ione(~T, ~num)}, ilt(~T, ~num, izero(~T, ~num), min(~T, ~N.ar(T, num), k, isub(~T, ~num, n, k)))))

def comb(~T: Data, ~num: N.Integer<T>, +n: T, +k: T) -> Result<&2, &2, N.NumError, T>:
  comb_big(~T, ~num, n, k, ilt(~T, ~num, n, k))

# ---- modular arithmetic ----

def pow_mod_odd(~T: Data, ~num: N.Integer<T>, +m: T, odd: Bool, +base: T, +acc: T) -> T:
  match odd:
    case False{}:
      acc
    case True{}:
      N.mulmod(T, num, acc, base, m)

# right-to-left binary exponentiation, every product reduced mod m
def pow_mod_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +m: T, +e: T, +base: T, +acc: T, more: Bool) -> T:
  match fuel more:
    case 0n _:
      acc
    case 1n+f False{}:
      acc
    case 1n+f True{}:
      pow_mod_go(~T, ~num, f, m, N.shr1(T, num, e), N.mulmod(T, num, base, base, m), pow_mod_odd(~T, ~num, m, N.odd(T, num, e), base, acc), is_pos(~T, ~num, N.shr1(T, num, e)))

def pow_mod_ok(~T: Data, ~num: N.Integer<T>, +b: T, +e: T, +m: T, pos: Bool) -> Result<&2, &2, N.NumError, T>:
  match pos:
    case False{}:
      Fail{N.ZeroDivision{}}
    case True{}:
      Done{pow_mod_go(~T, ~num, 1n+N.width(T, num), m, e, rem(~T, ~num, b, m), rem(~T, ~num, ione(~T, ~num), m), is_pos(~T, ~num, e))}

def pow_mod(~T: Data, ~num: N.Integer<T>, +b: T, +e: T, +m: T) -> Result<&2, &2, N.NumError, T>:
  pow_mod_ok(~T, ~num, b, e, m, is_pos(~T, ~num, m))

# s0 - x mod m for s0, x < m, without leaving [0, m)
def submod(~T: Data, ~num: N.Integer<T>, +m: T, +s0: T, +x: T, below: Bool) -> T:
  match below:
    case False{}:
      isub(~T, ~num, s0, x)
    case True{}:
      or_zero(T, s0, iadd(~T, ~num, s0, isub(~T, ~num, m, x)))

def inv_step(~T: Data, ~num: N.Integer<T>, +m: T, +q: T, +s0: T, +s1: T) -> T:
  submod(~T, ~num, m, s0, N.mulmod(T, num, rem(~T, ~num, q, m), s1, m), ilt(~T, ~num, s0, N.mulmod(T, num, rem(~T, ~num, q, m), s1, m)))

# extended Euclid on (m, a mod m), keeping the coefficient of a mod m
def inv_go(~T: Data, ~num: N.Integer<T>, fuel: Nat, +m: T, +r0: T, +s0: T, +r1: T, +s1: T, more: Bool) -> T & T:
  match fuel more:
    case 0n _:
      (r0, s0)
    case 1n+f False{}:
      (r0, s0)
    case 1n+f True{}:
      inv_go(~T, ~num, f, m, r1, s1, rem(~T, ~num, r0, r1), inv_step(~T, ~num, m, quot(~T, ~num, r0, r1), s0, s1), is_pos(~T, ~num, rem(~T, ~num, r0, r1)))

def inv_one(~T: Data, ~num: N.Integer<T>, +m: T, +s: T, one: Bool) -> Result<&2, &2, N.NumError, T>:
  match one:
    case True{}:
      Done{rem(~T, ~num, s, m)}
    case False{}:
      Fail{N.NotInvertible{}}

def inv_fin(~T: Data, ~num: N.Integer<T>, +m: T, r: T & T) -> Result<&2, &2, N.NumError, T>:
  (+g, +s) = r
  inv_one(~T, ~num, m, s, Bool.and(Bool.not(ilt(~T, ~num, g, ione(~T, ~num))), Bool.not(ilt(~T, ~num, ione(~T, ~num), g))))

def inv_ok(~T: Data, ~num: N.Integer<T>, +a: T, +m: T, pos: Bool) -> Result<&2, &2, N.NumError, T>:
  match pos:
    case False{}:
      Fail{N.ZeroDivision{}}
    case True{}:
      inv_fin(~T, ~num, m, inv_go(~T, ~num, fuel(~T, ~num), m, m, izero(~T, ~num), rem(~T, ~num, a, m), ione(~T, ~num), is_pos(~T, ~num, rem(~T, ~num, a, m))))

# pow(a, -1, m): the x < m with a * x == 1 (mod m)
def mod_inverse(~T: Data, ~num: N.Integer<T>, +a: T, +m: T) -> Result<&2, &2, N.NumError, T>:
  inv_ok(~T, ~num, a, m, is_pos(~T, ~num, m))

# ---- division ----

def divmod_ok(~T: Data, ~num: N.Integer<T>, +a: T, +b: T, pos: Bool) -> Result<&2, &2, N.NumError, QuotRem<T>>:
  match pos:
    case False{}:
      Fail{N.ZeroDivision{}}
    case True{}:
      Done{QR{quot(~T, ~num, a, b), rem(~T, ~num, a, b)}}

def divmod(~T: Data, ~num: N.Integer<T>, +a: T, +b: T) -> Result<&2, &2, N.NumError, QuotRem<T>>:
  divmod_ok(~T, ~num, a, b, is_pos(~T, ~num, b))
