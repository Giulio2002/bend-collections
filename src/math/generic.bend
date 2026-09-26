import Base
import ./num.bend as N

# The math of natural.bend written once for any numeric type. Every function
# takes the type and its interface as templates (~T, ~op, ~test; num.bend), so
# each instance (instances.bend: U32, U64, F32; f64.bend: F64) compiles to its
# own copy with the operations inlined:
#
#   G.gcd(~U32, ~I.u32_op, ~I.u32_is, a, b)
#
#   ordered-ring functions (every instance, floats included):
#     min, max, clamp, abs, sign, sum, prod, pow (exponent a Nat)
#   integer functions (the unsigned instances):
#     gcd, lcm, gcd_all, lcm_all, bit_length, isqrt, iroot, ilog,
#     factorial, perm, comb, pow_mod, mod_inverse, divmod
#
# Semantics are Python's, with checked results for fixed widths (design
# reference section 2.6): a result that does not fit is Fail{Overflow}, never
# a wrapped value. comb reduces by a gcd at every step, so it overflows only
# when the result does; pow_mod and mod_inverse use the instance's MulMod, so
# no intermediate leaves [0, m). Loops are bounded by fuel for 64-bit widths.
# The Nat versions in natural.bend are the proved reference; these are tested
# against Python (tools/check_generic.py). sum is a left fold (Python's float
# sum is compensated; use it for exact float sums once fsum exists).

type QuotRem<-T: Data> is Data:
  TQR{quot: T, rem: T}

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

# enough steps for every loop at 64 bits (Euclid < 1.5 w + 2, bit loops w)
def fuel() -> Nat:
  140n

# x when it fits, else None
def fits(-T: Data, over: Bool, +x: T) -> Maybe<&2, T>:
  match over:
    case True{}:
      None{}
    case False{}:
      Some{x}

def cadd(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Maybe<&2, T>:
  fits(T, test(N.AddOver{a, b}), op(N.Add{a, b}))

def cmul(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Maybe<&2, T>:
  fits(T, test(N.MulOver{a, b}), op(N.Mul{a, b}))

def lt(~T: Data, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Bool:
  test(N.Lt{a, b})

def le(~T: Data, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Bool:
  Bool.not(test(N.Lt{b, a}))

def pos(~T: Data, ~test: N.Test<T> -> Bool, +a: T) -> Bool:
  Bool.not(test(N.IsZero{a}))

# ---- ordered-ring functions ----

def pick(-T: Data, c: Bool, +a: T, +b: T) -> T:
  match c:
    case True{}:
      a
    case False{}:
      b

# Python's min(a, b) keeps a unless b < a; max keeps a unless a < b.
def min(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> T:
  pick(T, test(N.Lt{b, a}), b, a)

def max(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> T:
  pick(T, test(N.Lt{a, b}), b, a)

def clamp_ok(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T, bad: Bool) -> Result<&2, &2, N.NumError, T>:
  match bad:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Done{min(~T, ~op, ~test, max(~T, ~op, ~test, x, lo), hi)}

# min(max(x, lo), hi); hi < lo is a Domain error
def clamp(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +lo: T, +hi: T) -> Result<&2, &2, N.NumError, T>:
  clamp_ok(~T, ~op, ~test, x, lo, hi, test(N.Lt{hi, lo}))

def abs(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> T:
  op(N.Abs{x})

def sign_below(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, below: Bool) -> T:
  match below:
    case True{}:
      op(N.Neg{op(N.One{})})
    case False{}:
      x

def sign_above(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, above: Bool) -> T:
  match above:
    case True{}:
      op(N.One{})
    case False{}:
      sign_below(~T, ~op, ~test, x, test(N.Lt{x, op(N.ZeroOp{})}))

# 1 above zero, -1 below, x itself otherwise (0, -0.0, NaN)
def sign(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T) -> T:
  sign_above(~T, ~op, ~test, x, test(N.Lt{op(N.ZeroOp{}), x}))

def sum_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} None{}:
      None{}
    case Con{+x, rest} Some{+a}:
      sum_go(~T, ~op, ~test, rest, cadd(~T, ~op, ~test, a, x))

def sum(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  ok(T, sum_go(~T, ~op, ~test, xs, Some{op(N.ZeroOp{})}))

def prod_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>, acc: Maybe<&2, T>) -> Maybe<&2, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} None{}:
      None{}
    case Con{+x, rest} Some{+a}:
      prod_go(~T, ~op, ~test, rest, cmul(~T, ~op, ~test, a, x))

def prod(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  ok(T, prod_go(~T, ~op, ~test, xs, Some{op(N.One{})}))

# (value, still fits) after multiplying by x when bit is set
def mul_st(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, bit: Bool, +x: T, +xok: Bool, st: T & Bool) -> T & Bool:
  match bit st:
    case False{} _:
      st
    case True{} Tuple{+a, +aok}:
      (op(N.Mul{a, x}), Bool.and(Bool.and(aok, xok), Bool.not(test(N.MulOver{a, x}))))

# the base squared, only while higher exponent bits remain
def sq_val(~T: Data, ~op: N.Op<T> -> T, more: Bool, +b: T) -> T:
  match more:
    case False{}:
      b
    case True{}:
      op(N.Mul{b, b})

def sq_ok(~T: Data, ~test: N.Test<T> -> Bool, more: Bool, +b: T, +bok: Bool) -> Bool:
  match more:
    case False{}:
      bok
    case True{}:
      Bool.and(bok, Bool.not(test(N.MulOver{b, b})))

def st_fin(-T: Data, st: T & Bool) -> Maybe<&2, T>:
  match st:
    case Tuple{+a, +aok}:
      fits(T, Bool.not(aok), a)

# square-and-multiply, low bits first; an overflowing square means the
# result overflows too (a later bit multiplies it in). Callers pass fuel
# 1 + k: every step halves k, so the loop always ends on k == 0.
def pow_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +k: Nat, +b: T, +bok: Bool, st: T & Bool) -> Maybe<&2, T>:
  match fuel k:
    case 0n _:
      st_fin(T, st)
    case 1n+f 0n:
      st_fin(T, st)
    case 1n+f 1n+j:
      pow_go(~T, ~op, ~test, f, Nat.div(1n+j, 2n), sq_val(~T, ~op, Nat.is_lt(1n, 1n+j), b), sq_ok(~T, ~test, Nat.is_lt(1n, 1n+j), b, bok), mul_st(~T, ~op, ~test, Nat.is_eq(Nat.mod(1n+j, 2n), 1n), b, bok, st))

def pow(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, +k: Nat) -> Result<&2, &2, N.NumError, T>:
  ok(T, pow_go(~T, ~op, ~test, 1n+k, k, x, True{}, (op(N.One{}), True{})))

# ---- integer functions (unsigned) ----

def one(~T: Data, ~op: N.Op<T> -> T) -> T:
  op(N.One{})

def inc(~T: Data, ~op: N.Op<T> -> T, +x: T) -> T:
  op(N.Add{x, op(N.One{})})

def dec(~T: Data, ~op: N.Op<T> -> T, +x: T) -> T:
  op(N.Sub{x, op(N.One{})})

# (x, x == 0)
def zst(~T: Data, ~test: N.Test<T> -> Bool, +x: T) -> T & Bool:
  (x, test(N.IsZero{x}))

# Euclid's algorithm on (a, (b, b == 0))
def gcd_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +a: T, st: T & Bool) -> T:
  match fuel st:
    case 0n _:
      a
    case 1n+f Tuple{b, True{}}:
      a
    case 1n+f Tuple{+b, False{}}:
      gcd_go(~T, ~op, ~test, f, b, zst(~T, ~test, op(N.Rem{a, b})))

def gcd(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> T:
  gcd_go(~T, ~op, ~test, fuel(), a, zst(~T, ~test, b))

def lcm_ok(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T, zero: Bool) -> Result<&2, &2, N.NumError, T>:
  match zero:
    case True{}:
      Done{op(N.ZeroOp{})}
    case False{}:
      ok(T, cmul(~T, ~op, ~test, op(N.Quot{a, gcd(~T, ~op, ~test, a, b)}), b))

def lcm(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Result<&2, &2, N.NumError, T>:
  lcm_ok(~T, ~op, ~test, a, b, Bool.or(test(N.IsZero{a}), test(N.IsZero{b})))

def gcd_all_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>, +acc: T) -> T:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      gcd_all_go(~T, ~op, ~test, rest, gcd(~T, ~op, ~test, acc, x))

def gcd_all(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> T:
  gcd_all_go(~T, ~op, ~test, xs, op(N.ZeroOp{}))

def lcm_all_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>, acc: Result<&2, &2, N.NumError, T>) -> Result<&2, &2, N.NumError, T>:
  match xs acc:
    case Nil{} _:
      acc
    case Con{x, rest} Fail{e}:
      Fail{e}
    case Con{+x, rest} Done{+a}:
      lcm_all_go(~T, ~op, ~test, rest, lcm(~T, ~op, ~test, a, x))

def lcm_all(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, xs: List<&2, T>) -> Result<&2, &2, N.NumError, T>:
  lcm_all_go(~T, ~op, ~test, xs, Done{op(N.One{})})

# the number of halvings to reach zero
def bit_length_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +k: Nat, st: T & Bool) -> Nat:
  match fuel st:
    case 0n _:
      k
    case 1n+f Tuple{n, True{}}:
      k
    case 1n+f Tuple{+n, False{}}:
      bit_length_go(~T, ~op, ~test, f, 1n+k, zst(~T, ~test, op(N.Half{n})))

def bit_length(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T) -> Nat:
  bit_length_go(~T, ~op, ~test, fuel(), 0n, zst(~T, ~test, n))

# the instance's integer square root (a hardware estimate and an exact
# integer correction for U32 and U64)
def isqrt(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T) -> T:
  op(N.Sqrt{n})

# ---- roots and logarithms ----

# r^k <= n, with an overflowing power counted as > n
def root_le_fin(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, p: Maybe<&2, T>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{+x}:
      le(~T, ~test, x, n)

def root_le(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: Nat, +r: T) -> Bool:
  root_le_fin(~T, ~op, ~test, n, pow_go(~T, ~op, ~test, 1n+k, k, r, True{}, (op(N.One{}), True{})))

# lo + (hi - lo) / 2, never above hi
def imid(~T: Data, ~op: N.Op<T> -> T, +lo: T, +hi: T) -> T:
  op(N.Add{lo, op(N.Half{op(N.Sub{hi, lo})})})

# the last r in [lo, hi) with r^k <= n, given it holds at lo and fails at
# hi: bisection while hi - lo > 1
def search_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fu: Nat, +n: T, +k: Nat, +lo: T, +hi: T, +m: T, +more: Bool, +hit: Bool) -> T:
  match fu more hit:
    case 0n _ _:
      lo
    case 1n+f False{} _:
      lo
    case 1n+f True{} True{}:
      search_go(~T, ~op, ~test, f, n, k, m, hi, imid(~T, ~op, m, hi), test(N.Lt{inc(~T, ~op, m), hi}), root_le(~T, ~op, ~test, n, k, imid(~T, ~op, m, hi)))
    case 1n+f True{} False{}:
      search_go(~T, ~op, ~test, f, n, k, lo, m, imid(~T, ~op, lo, m), test(N.Lt{inc(~T, ~op, lo), m}), root_le(~T, ~op, ~test, n, k, imid(~T, ~op, lo, m)))

def search(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: Nat, +hi: T) -> T:
  search_go(~T, ~op, ~test, fuel(), n, k, op(N.ZeroOp{}), hi, imid(~T, ~op, op(N.ZeroOp{}), hi), test(N.Lt{op(N.One{}), hi}), root_le(~T, ~op, ~test, n, k, imid(~T, ~op, op(N.ZeroOp{}), hi)))

# 2^(bits(n) / k + 1) > the k-th root of n
def iroot_k(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: Nat) -> T:
  match k:
    case 0n:
      op(N.ZeroOp{})
    case 1n:
      n
    case 2n+ +kp:
      search(~T, ~op, ~test, n, 2n+kp, op(N.Pow2{1n+Nat.div(bit_length(~T, ~op, ~test, n), 2n+kp)}))

def iroot(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: Nat) -> Result<&2, &2, N.NumError, T>:
  match k:
    case 0n:
      Fail{N.BadDomain{}}
    case 1n+ +kp:
      Done{iroot_k(~T, ~op, ~test, n, 1n+kp)}

# the largest k with b^k <= n; p <= n / b is asked before p * b is formed
def ilog_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +q: T, +b: T, +k: Nat, +p: T, up: Bool) -> Nat:
  match fuel up:
    case 0n _:
      k
    case 1n+f False{}:
      k
    case 1n+f True{}:
      ilog_go(~T, ~op, ~test, f, q, b, 1n+k, op(N.Mul{p, b}), le(~T, ~test, op(N.Mul{p, b}), q))

def ilog_ok(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +b: T, bad: Bool) -> Result<&2, &2, N.NumError, Nat>:
  match bad:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Done{ilog_go(~T, ~op, ~test, fuel(), op(N.Quot{n, b}), b, 0n, op(N.One{}), le(~T, ~test, op(N.One{}), op(N.Quot{n, b})))}

def ilog(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +b: T) -> Result<&2, &2, N.NumError, Nat>:
  ilog_ok(~T, ~op, ~test, n, b, Bool.or(test(N.IsZero{n}), test(N.Lt{b, op(N.Add{op(N.One{}), op(N.One{})})})))

# ---- factorial, permutations, combinations ----

# (acc * x, still fits)
def mul_by(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +x: T, st: T & Bool) -> T & Bool:
  match st:
    case Tuple{+a, +aok}:
      (op(N.Mul{a, x}), Bool.and(aok, Bool.not(test(N.MulOver{a, x}))))

# 2 * 3 * ... * n: i runs up to n, stopping at the first overflow
def fact_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +i: T, +n: T, st: T & Bool, more: Bool) -> Maybe<&2, T>:
  match fuel st more:
    case 0n _ _:
      None{}
    case 1n+f Tuple{a, False{}} _:
      None{}
    case 1n+f Tuple{+a, True{}} False{}:
      Some{a}
    case 1n+f Tuple{+a, True{}} True{}:
      fact_go(~T, ~op, ~test, f, inc(~T, ~op, i), n, mul_by(~T, ~op, ~test, inc(~T, ~op, i), (a, True{})), test(N.Lt{inc(~T, ~op, i), n}))

def factorial(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T) -> Result<&2, &2, N.NumError, T>:
  ok(T, fact_go(~T, ~op, ~test, fuel(), op(N.One{}), n, (op(N.One{}), True{}), test(N.Lt{op(N.One{}), n})))

# n (n - 1) ... (n - k + 1): m runs down while k counts the factors left
def perm_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +k: T, +m: T, st: T & Bool, more: Bool) -> Maybe<&2, T>:
  match fuel st more:
    case 0n _ _:
      None{}
    case 1n+f Tuple{a, False{}} _:
      None{}
    case 1n+f Tuple{+a, True{}} False{}:
      Some{a}
    case 1n+f Tuple{+a, True{}} True{}:
      perm_go(~T, ~op, ~test, f, dec(~T, ~op, k), dec(~T, ~op, m), mul_by(~T, ~op, ~test, m, (a, True{})), Bool.not(test(N.IsZero{dec(~T, ~op, k)})))

def perm_big(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: T, big: Bool) -> Result<&2, &2, N.NumError, T>:
  match big:
    case True{}:
      Done{op(N.ZeroOp{})}
    case False{}:
      ok(T, perm_go(~T, ~op, ~test, fuel(), k, n, (op(N.One{}), True{}), Bool.not(test(N.IsZero{k}))))

def perm(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: T) -> Result<&2, &2, N.NumError, T>:
  perm_big(~T, ~op, ~test, n, k, test(N.Lt{n, k}))

# C(n, i+1) = (r / g) * ((n - i) / ((i + 1) / g)) with r = C(n, i) and
# g = gcd(r, i + 1): exact, and it overflows only if C(n, i+1) does (C(n, i)
# grows for i < n / 2)
def comb_mul(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +r: T, +t: T, +j: T, +g: T) -> T & Bool:
  mul_by(~T, ~op, ~test, op(N.Quot{t, op(N.Quot{j, g})}), (op(N.Quot{r, g}), True{}))

def comb_next(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +r: T, +t: T, +j: T) -> T & Bool:
  comb_mul(~T, ~op, ~test, r, t, j, gcd(~T, ~op, ~test, r, j))

# i runs up to k (k <= n / 2), r = C(n, i)
def comb_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +n: T, +i: T, +k: T, st: T & Bool, more: Bool) -> Maybe<&2, T>:
  match fuel st more:
    case 0n _ _:
      None{}
    case 1n+f Tuple{r, False{}} _:
      None{}
    case 1n+f Tuple{+r, True{}} False{}:
      Some{r}
    case 1n+f Tuple{+r, True{}} True{}:
      comb_go(~T, ~op, ~test, f, n, inc(~T, ~op, i), k, comb_next(~T, ~op, ~test, r, op(N.Sub{n, i}), inc(~T, ~op, i)), test(N.Lt{inc(~T, ~op, i), k}))

def comb_k(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: T) -> Result<&2, &2, N.NumError, T>:
  ok(T, comb_go(~T, ~op, ~test, fuel(), n, op(N.ZeroOp{}), k, (op(N.One{}), True{}), test(N.Lt{op(N.ZeroOp{}), k})))

def comb_big(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: T, big: Bool) -> Result<&2, &2, N.NumError, T>:
  match big:
    case True{}:
      Done{op(N.ZeroOp{})}
    case False{}:
      comb_k(~T, ~op, ~test, n, min(~T, ~op, ~test, k, op(N.Sub{n, k})))

def comb(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +n: T, +k: T) -> Result<&2, &2, N.NumError, T>:
  comb_big(~T, ~op, ~test, n, k, test(N.Lt{n, k}))

# ---- modular arithmetic ----

def mm_bit(~T: Data, ~op: N.Op<T> -> T, odd: Bool, +m: T, +b: T, +acc: T) -> T:
  match odd:
    case False{}:
      acc
    case True{}:
      op(N.MulMod{acc, b, m})

# right-to-left binary exponentiation on (e, e == 0), every product reduced
# mod m
def pow_mod_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +m: T, +b: T, +acc: T, st: T & Bool) -> T:
  match fuel st:
    case 0n _:
      acc
    case 1n+f Tuple{e, True{}}:
      acc
    case 1n+f Tuple{+e, False{}}:
      pow_mod_go(~T, ~op, ~test, f, m, op(N.MulMod{b, b, m}), mm_bit(~T, ~op, test(N.Odd{e}), m, b, acc), zst(~T, ~test, op(N.Half{e})))

def pow_mod_ok(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +b: T, +e: T, +m: T, zero: Bool) -> Result<&2, &2, N.NumError, T>:
  match zero:
    case True{}:
      Fail{N.DivByZero{}}
    case False{}:
      Done{pow_mod_go(~T, ~op, ~test, fuel(), m, op(N.Rem{b, m}), op(N.Rem{op(N.One{}), m}), zst(~T, ~test, e))}

# Python's pow(b, e, m) for m > 0
def pow_mod(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +b: T, +e: T, +m: T) -> Result<&2, &2, N.NumError, T>:
  pow_mod_ok(~T, ~op, ~test, b, e, m, test(N.IsZero{m}))

# s0 - x mod m for s0, x < m, without leaving [0, m)
def submod(~T: Data, ~op: N.Op<T> -> T, +m: T, +s0: T, +x: T, below: Bool) -> T:
  match below:
    case False{}:
      op(N.Sub{s0, x})
    case True{}:
      op(N.Add{s0, op(N.Sub{m, x})})

def inv_sub(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +m: T, +s0: T, +x: T) -> T:
  submod(~T, ~op, m, s0, x, test(N.Lt{s0, x}))

def inv_step(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +m: T, +q: T, +s0: T, +s1: T) -> T:
  inv_sub(~T, ~op, ~test, m, s0, op(N.MulMod{op(N.Rem{q, m}), s1, m}))

# extended Euclid on (m, a mod m), keeping the coefficient of a mod m;
# st = (r1, r1 == 0)
def inv_go(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, fuel: Nat, +m: T, +r0: T, +s0: T, +s1: T, st: T & Bool) -> T & T:
  match fuel st:
    case 0n _:
      (r0, s0)
    case 1n+f Tuple{r1, True{}}:
      (r0, s0)
    case 1n+f Tuple{+r1, False{}}:
      inv_go(~T, ~op, ~test, f, m, r1, s1, inv_step(~T, ~op, ~test, m, op(N.Quot{r0, r1}), s0, s1), zst(~T, ~test, op(N.Rem{r0, r1})))

def inv_one(~T: Data, ~op: N.Op<T> -> T, +m: T, +s: T, one: Bool) -> Result<&2, &2, N.NumError, T>:
  match one:
    case True{}:
      Done{op(N.Rem{s, m})}
    case False{}:
      Fail{N.NoInverse{}}

def inv_fin(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +m: T, r: T & T) -> Result<&2, &2, N.NumError, T>:
  (+g, +s) = r
  inv_one(~T, ~op, m, s, Bool.and(Bool.not(test(N.Lt{g, op(N.One{})})), Bool.not(test(N.Lt{op(N.One{}), g}))))

def inv_ok(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +m: T, zero: Bool) -> Result<&2, &2, N.NumError, T>:
  match zero:
    case True{}:
      Fail{N.DivByZero{}}
    case False{}:
      inv_fin(~T, ~op, ~test, m, inv_go(~T, ~op, ~test, fuel(), m, m, op(N.ZeroOp{}), op(N.One{}), zst(~T, ~test, op(N.Rem{a, m}))))

# pow(a, -1, m): the x < m with a * x == 1 (mod m)
def mod_inverse(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +m: T) -> Result<&2, &2, N.NumError, T>:
  inv_ok(~T, ~op, ~test, a, m, test(N.IsZero{m}))

# ---- division ----

def divmod_ok(~T: Data, ~op: N.Op<T> -> T, +a: T, +b: T, zero: Bool) -> Result<&2, &2, N.NumError, QuotRem<T>>:
  match zero:
    case True{}:
      Fail{N.DivByZero{}}
    case False{}:
      Done{TQR{op(N.Quot{a, b}), op(N.Rem{a, b})}}

def divmod(~T: Data, ~op: N.Op<T> -> T, ~test: N.Test<T> -> Bool, +a: T, +b: T) -> Result<&2, &2, N.NumError, QuotRem<T>>:
  divmod_ok(~T, ~op, a, b, test(N.IsZero{b}))
