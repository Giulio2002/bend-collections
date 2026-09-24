import Base
import ./num.bend as N
import ./wide.bend as X


type F64 is Data:
  Bits{lo: U32, hi: U32}

def word_lo(x: F64) -> U32:
  match x:
    case Bits{l, h}:
      l

# IEEE-754 binary64 in software, on two U32 words (Bend 2 has only F32).
# Every arithmetic operation computes its exact result as a wide natural
# significand times a power of two (wide.bend) and rounds it once, to nearest
# with ties to even, into the binary64 grid: subnormals, overflow to
# infinity, signed zeros and NaN follow IEEE 754 (x + (-x) is +0, 0/0 and
# inf - inf are NaN; a NaN result is the canonical quiet NaN).
#
#   of_bits(hi, lo), word_hi(x), word_lo(x)          the bit pattern
#   is_nan, is_inf, is_finite, is_zero, signbit
#   neg, abs, copysign
#   add, sub, mul, div, sqrt               correctly rounded
#   lt, le, eq                             IEEE comparisons (NaN unordered)
#   of_nat(n)                              exact for n < 2^48
#   arith()                                the num.bend instance
#
# Exponents are kept as naturals offset by B = 3000, so a finite value is
# m * 2^(e - B) with m a wide natural.

def word_hi(x: F64) -> U32:
  match x:
    case Bits{l, h}:
      h

def two31() -> Nat:
  2147483648n

def two32() -> Nat:
  Nat.add(4294967295n, 1n)

def hin(x: F64) -> Nat:
  U32.to_nat(word_hi(x))

def neg(+x: F64) -> F64:
  Bits{word_lo(x), U32.from_nat(Nat.mod(Nat.add(hin(x), two31()), two32()))}

type Class is Data:
  CNaN{}
  CInf{neg: Bool}
  CZero{neg: Bool}
  CFin{neg: Bool, m: List<&2, Nat>, e: Nat}

# 2^52 in 24-bit limbs
def two52() -> List<&2, Nat>:
  Con{0n, Con{0n, Con{16n, Nil{}}}}

# min and max by one comparison (Base's Nat.min / Nat.max count down)
def nmin(+a: Nat, +b: Nat) -> Nat:
  X.nat_pick(Nat.is_le(a, b), a, b)

def nmax(+a: Nat, +b: Nat) -> Nat:
  X.nat_pick(Nat.is_le(a, b), b, a)

def bias() -> Nat:
  3000n

def of_bits(+hi: U32, +lo: U32) -> F64:
  Bits{lo, hi}

def lon(x: F64) -> Nat:
  U32.to_nat(word_lo(x))

def bitb(b: Bool) -> Nat:
  X.bitn(b)

# ---- fields ----

def signbit(+x: F64) -> Bool:
  Nat.is_le(two31(), hin(x))

def exp_field(+x: F64) -> Nat:
  Nat.mod(Nat.div(hin(x), 1048576n), 2048n)

def frac_zero(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(hin(x), 1048576n), 0n), Nat.is_eq(lon(x), 0n))

# the 52 fraction bits as a wide natural (24-bit limbs)
def frac(+x: F64) -> List<&2, Nat>:
  X.norm(Con{Nat.mod(lon(x), 16777216n), Con{Nat.add(Nat.div(lon(x), 16777216n), Nat.mul(Nat.mod(Nat.mod(hin(x), 1048576n), 65536n), 256n)), Con{Nat.div(Nat.mod(hin(x), 1048576n), 65536n), Nil{}}}})

def is_nan(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 2047n), Bool.not(frac_zero(x)))

def is_inf(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 2047n), frac_zero(x))

def is_finite(+x: F64) -> Bool:
  Nat.is_lt(exp_field(x), 2047n)

def is_zero(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 0n), frac_zero(x))

# ---- constants and sign ----

def nan() -> F64:
  Bits{0, 2146959360}

def inf(neg: Bool) -> F64:
  Bits{0, U32.from_nat(Nat.add(Nat.mul(bitb(neg), two31()), 2146435072n))}

def zero(neg: Bool) -> F64:
  Bits{0, U32.from_nat(Nat.mul(bitb(neg), two31()))}

def one() -> F64:
  Bits{0, 1072693248}

def abs(+x: F64) -> F64:
  Bits{word_lo(x), U32.from_nat(Nat.mod(hin(x), two31()))}

def copysign(+x: F64, +y: F64) -> F64:
  Bits{word_lo(x), U32.from_nat(Nat.add(Nat.mod(hin(x), two31()), Nat.mul(bitb(signbit(y)), two31())))}

def classify_sub(+s: Bool, f: List<&2, Nat>) -> Class:
  match f:
    case Nil{}:
      CZero{s}
    case Con{h, t}:
      CFin{s, Con{h, t}, Nat.sub(bias(), 1074n)}

def classify_top(+s: Bool, f: List<&2, Nat>) -> Class:
  match f:
    case Nil{}:
      CInf{s}
    case Con{h, t}:
      CNaN{}

def classify_e(+s: Bool, e: Nat, f: List<&2, Nat>) -> Class:
  match e:
    case 0n:
      classify_sub(s, f)
    case 2047n:
      classify_top(s, f)
    case 1n+ +k:
      CFin{s, X.add(f, two52()), Nat.sub(Nat.add(bias(), 1n+k), 1075n)}

# ---- decoding ----

def classify(+x: F64) -> Class:
  classify_e(signbit(x), exp_field(x), frac(x))

# ---- rounding ----

# the fraction f < 2^52 and biased exponent field E into the word pair
def encode(+s: Bool, +ex: Nat, +f: List<&2, Nat>) -> F64:
  Bits{U32.from_nat(Nat.add(X.nth(f, 0n), Nat.mul(Nat.mod(X.nth(f, 1n), 256n), 16777216n))), U32.from_nat(Nat.add(Nat.add(Nat.mul(bitb(s), two31()), Nat.mul(ex, 1048576n)), Nat.add(Nat.div(X.nth(f, 1n), 256n), Nat.mul(X.nth(f, 2n), 65536n))))}

def odd(+m: List<&2, Nat>) -> Bool:
  Nat.is_eq(Nat.mod(X.nth(m, 0n), 2n), 1n)

def rne_up(+q: List<&2, Nat>, up: Bool) -> List<&2, Nat>:
  match up:
    case True{}:
      X.add(q, X.of_nat(1n))
    case False{}:
      q

# m / 2^d rounded to nearest, ties to even (d >= 1): t = m / 2^(d-1) keeps
# the half bit, st whether anything below it was set
def rne_fin(p: List<&2, Nat> & Bool) -> List<&2, Nat>:
  (+t, +st) = p
  rne_up(X.shr1(t), Bool.and(odd(t), Bool.or(st, odd(X.shr1(t)))))

def rne_shift(+m: List<&2, Nat>, d: Nat) -> List<&2, Nat>:
  match d:
    case 0n:
      m
    case 1n+j:
      rne_fin(X.shr_sticky(m, j))

def top_of_quantum(+m: List<&2, Nat>, +e: Nat) -> Nat:
  nmax(Nat.sub(Nat.sub(Nat.add(e, X.bit_length(m)), 1n), 52n), Nat.sub(bias(), 1074n))

def round_to(+m: List<&2, Nat>, +e: Nat, +q: Nat, down: Bool) -> List<&2, Nat>:
  match down:
    case True{}:
      rne_shift(m, Nat.sub(q, e))
    case False{}:
      X.shl(m, Nat.sub(e, q))

def pack_over(+s: Bool, +f: List<&2, Nat>, +ex: Nat, over: Bool) -> F64:
  match over:
    case True{}:
      inf(s)
    case False{}:
      encode(s, ex, f)

def pack_e(+s: Bool, +f: List<&2, Nat>, +ex: Nat) -> F64:
  pack_over(s, f, ex, Nat.is_le(2047n, ex))

# ---- addition ----

def eqb(+a: Bool, +b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def pack_n(+s: Bool, +m: List<&2, Nat>, +q: Nat, small: Bool) -> F64:
  match small:
    case True{}:
      encode(s, 0n, m)
    case False{}:
      pack_e(s, X.sub(m, two52()), Nat.add(Nat.sub(q, Nat.sub(bias(), 1074n)), 1n))

# m * 2^(q - B) with m < 2^53 on the grid: subnormal below 2^52
def pack(+s: Bool, +m: List<&2, Nat>, +q: Nat) -> F64:
  pack_n(s, m, q, X.lt(m, two52()))

def round_carry_at(+s: Bool, +m: List<&2, Nat>, +q: Nat, carry: Bool) -> F64:
  match carry:
    case True{}:
      pack(s, X.shr1(m), 1n+q)
    case False{}:
      pack(s, m, q)

# a round up to 2^53 renormalizes (exactly) into the next binade
def round_carry(+s: Bool, +m: List<&2, Nat>, +q: Nat) -> F64:
  round_carry_at(s, m, q, Nat.is_lt(53n, X.bit_length(m)))

def round_q(+s: Bool, +m: List<&2, Nat>, +e: Nat, +q: Nat, ) -> F64:
  round_carry(s, round_to(m, e, q, Nat.is_le(e, q)), q)

# m * 2^(e - B), m > 0, rounded: the quantum q is 2^-1074 or the 53rd bit
# below the leading one, whichever is larger
def round_pack(+s: Bool, +m: List<&2, Nat>, +e: Nat) -> F64:
  round_q(s, m, e, top_of_quantum(m, e))

def add_diff(+s1: Bool, +a: List<&2, Nat>, +s2: Bool, +b: List<&2, Nat>, +e: Nat, c: Cmp) -> F64:
  match c:
    case EQ{}:
      zero(False{})
    case GT{}:
      round_pack(s1, X.sub(a, b), e)
    case LT{}:
      round_pack(s2, X.sub(b, a), e)

def add_signs(+s1: Bool, +a: List<&2, Nat>, +s2: Bool, +b: List<&2, Nat>, +e: Nat, same: Bool) -> F64:
  match same:
    case True{}:
      round_pack(s1, X.add(a, b), e)
    case False{}:
      add_diff(s1, a, s2, b, e, X.cmp(a, b))

def add_exact(+s1: Bool, +a: List<&2, Nat>, +s2: Bool, +b: List<&2, Nat>, +e: Nat) -> F64:
  add_signs(s1, a, s2, b, e, eqb(s1, s2))

def add_aligned(+s1: Bool, +m1: List<&2, Nat>, +e1: Nat, +s2: Bool, +m2: List<&2, Nat>, +e2: Nat) -> F64:
  add_exact(s1, X.shl(m1, Nat.sub(e1, nmin(e1, e2))), s2, X.shl(m2, Nat.sub(e2, nmin(e1, e2))), nmin(e1, e2))

def add_capped(+s1: Bool, +m1: List<&2, Nat>, +e1: Nat, +s2: Bool, +m2: List<&2, Nat>, +e2: Nat, far1: Bool, far2: Bool) -> F64:
  match far1 far2:
    case True{} _:
      add_aligned(s1, m1, e1, s2, X.of_nat(1n), Nat.sub(e1, 120n))
    case False{} True{}:
      add_aligned(s1, X.of_nat(1n), Nat.sub(e2, 120n), s2, m2, e2)
    case False{} False{}:
      add_aligned(s1, m1, e1, s2, m2, e2)

# the smaller operand, when more than 120 bits below the larger one, only
# decides rounding as a sticky bit: it is replaced by 2^(e_big - 120)
def add_near(+s1: Bool, +m1: List<&2, Nat>, +e1: Nat, +s2: Bool, +m2: List<&2, Nat>, +e2: Nat) -> F64:
  add_capped(s1, m1, e1, s2, m2, e2, Nat.is_lt(Nat.add(e2, 120n), e1), Nat.is_lt(Nat.add(e1, 120n), e2))

def add_infs(+x: F64, same: Bool) -> F64:
  match same:
    case True{}:
      x
    case False{}:
      nan()

def add_cls(+x: F64, +y: F64, cx: Class, cy: Class) -> F64:
  match cx cy:
    case CNaN{} _:
      nan()
    case _ CNaN{}:
      nan()
    case CInf{+a} CInf{+b}:
      add_infs(x, eqb(a, b))
    case CInf{a} _:
      x
    case _ CInf{b}:
      y
    case CZero{+a} CZero{+b}:
      zero(Bool.and(a, b))
    case CZero{a} _:
      y
    case _ CZero{b}:
      x
    case CFin{+s1, +m1, +e1} CFin{+s2, +m2, +e2}:
      add_near(s1, m1, e1, s2, m2, e2)

def add(+x: F64, +y: F64) -> F64:
  add_cls(x, y, classify(x), classify(y))

def sub(+x: F64, +y: F64) -> F64:
  add(x, neg(y))

# ---- multiplication and division ----

def mul_cls(+s: Bool, cx: Class, cy: Class) -> F64:
  match cx cy:
    case CNaN{} _:
      nan()
    case _ CNaN{}:
      nan()
    case CInf{a} CZero{b}:
      nan()
    case CZero{a} CInf{b}:
      nan()
    case CInf{a} _:
      inf(s)
    case _ CInf{b}:
      inf(s)
    case CZero{a} _:
      zero(s)
    case _ CZero{b}:
      zero(s)
    case CFin{s1, +m1, +e1} CFin{s2, +m2, +e2}:
      round_pack(s, X.mul(m1, m2), Nat.sub(Nat.add(e1, e2), bias()))

def mul(+x: F64, +y: F64) -> F64:
  mul_cls(Bool.xor(signbit(x), signbit(y)), classify(x), classify(y))

# a finite significand scaled to exactly 53 bits (the exponent follows)
def norm53(+m: List<&2, Nat>, +e: Nat) -> List<&2, Nat> & Nat:
  (X.shl(m, Nat.sub(53n, X.bit_length(m))), Nat.sub(e, Nat.sub(53n, X.bit_length(m))))

# n1 / n2 with both 53-bit: 57 quotient bits (the first a 1, after doubling
# n1 when n1 < n2), and the remainder as a sticky bit
def div_fin(+s: Bool, +e: Nat, p: List<&2, Nat> & List<&2, Nat>) -> F64:
  (+q, +r) = p
  round_pack(s, X.add(X.shl(q, 1n), X.of_nat(bitb(Bool.not(X.is_zero(r))))), e)

def div_lower(+s: Bool, +n1: List<&2, Nat>, +f1: Nat, +n2: List<&2, Nat>, +f2: Nat, lower: Bool) -> F64:
  match lower:
    case False{}:
      div_fin(s, Nat.sub(Nat.add(f1, bias()), Nat.add(f2, 57n)), X.div_frac(n1, n2, 56n))
    case True{}:
      div_fin(s, Nat.sub(Nat.add(f1, bias()), Nat.add(f2, 58n)), X.div_frac(X.shl(n1, 1n), n2, 56n))

def div_norm2(+s: Bool, +n1: List<&2, Nat>, +f1: Nat, b: List<&2, Nat> & Nat) -> F64:
  (+n2, +f2) = b
  div_lower(s, n1, f1, n2, f2, X.lt(n1, n2))

def div_norm(+s: Bool, a: List<&2, Nat> & Nat, b: List<&2, Nat> & Nat) -> F64:
  (+n1, +f1) = a
  div_norm2(s, n1, f1, b)

def div_cls(+s: Bool, cx: Class, cy: Class) -> F64:
  match cx cy:
    case CNaN{} _:
      nan()
    case _ CNaN{}:
      nan()
    case CInf{a} CInf{b}:
      nan()
    case CZero{a} CZero{b}:
      nan()
    case CInf{a} _:
      inf(s)
    case _ CInf{b}:
      zero(s)
    case CZero{a} _:
      zero(s)
    case _ CZero{b}:
      inf(s)
    case CFin{s1, +m1, +e1} CFin{s2, +m2, +e2}:
      div_norm(s, norm53(m1, e1), norm53(m2, e2))

def div(+x: F64, +y: F64) -> F64:
  div_cls(Bool.xor(signbit(x), signbit(y)), classify(x), classify(y))

# ---- square root ----

# n * 2^(f - B) with n of 53 bits = N * 2^(f - B - k), k = 60 + (f mod 2) so
# the exponent is even and N has 113 or 114 bits: its 57-bit root, doubled,
# plus (remainder != 0) carries the sticky bit
def sqrt_fin(+ex: Nat, p: List<&2, Nat> & List<&2, Nat>) -> F64:
  (+r, +rem) = p
  round_pack(False{}, X.add(X.shl(r, 1n), X.of_nat(bitb(Bool.not(X.is_zero(rem))))), ex)

def sqrt_k(+n: List<&2, Nat>, +f: Nat, +k: Nat) -> F64:
  sqrt_fin(Nat.sub(Nat.div(Nat.sub(Nat.add(bias(), f), k), 2n), 1n), X.sqrt_rem(n, k, 57n))

def sqrt_norm(p: List<&2, Nat> & Nat) -> F64:
  (+n, +f) = p
  sqrt_k(n, f, Nat.add(60n, Nat.mod(f, 2n)))

def sqrt_cls(+x: F64, c: Class) -> F64:
  match c:
    case CNaN{}:
      nan()
    case CZero{s}:
      x
    case CInf{False{}}:
      x
    case CInf{True{}}:
      nan()
    case CFin{True{}, m, e}:
      nan()
    case CFin{False{}, +m, +e}:
      sqrt_norm(norm53(m, e))

def sqrt(+x: F64) -> F64:
  sqrt_cls(x, classify(x))

# ---- comparison and conversion ----

# |x| as (high word without the sign, low word)
def mag_lt(+x: F64, +y: F64) -> Bool:
  Bool.or(Nat.is_lt(Nat.mod(hin(x), two31()), Nat.mod(hin(y), two31())), Bool.and(Nat.is_eq(Nat.mod(hin(x), two31()), Nat.mod(hin(y), two31())), Nat.is_lt(lon(x), lon(y))))

def lt_signs(+x: F64, +y: F64, sx: Bool, sy: Bool) -> Bool:
  match sx sy:
    case False{} False{}:
      mag_lt(x, y)
    case True{} True{}:
      mag_lt(y, x)
    case True{} False{}:
      True{}
    case False{} True{}:
      False{}

def lt(+x: F64, +y: F64) -> Bool:
  Bool.and(Bool.not(Bool.or(Bool.or(is_nan(x), is_nan(y)), Bool.and(is_zero(x), is_zero(y)))), lt_signs(x, y, signbit(x), signbit(y)))

def eq(+x: F64, +y: F64) -> Bool:
  Bool.and(Bool.not(Bool.or(is_nan(x), is_nan(y))), Bool.or(Bool.and(is_zero(x), is_zero(y)), Bool.and(Nat.is_eq(hin(x), hin(y)), Nat.is_eq(lon(x), lon(y)))))

def le(+x: F64, +y: F64) -> Bool:
  Bool.or(lt(x, y), eq(x, y))

def of_nat_z(+n: Nat, z: Bool) -> F64:
  match z:
    case True{}:
      zero(False{})
    case False{}:
      round_pack(False{}, X.of_nat(n), bias())

# n < 2^48, exactly
def of_nat(+n: Nat) -> F64:
  of_nat_z(n, Nat.is_eq(n, 0n))

# ---- the num.bend instance ----

def arith() -> N.Arith<F64>:
  N.Arith{zero(False{}), one(), (a => b => Some{add(a, b)}), (a => b => Some{sub(a, b)}), (a => b => Some{mul(a, b)}), (a => Some{neg(a)}), (a => b => lt(a, b)), (a => abs(a))}
