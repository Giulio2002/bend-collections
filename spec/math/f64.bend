import Base
import ../lib/common.bend as C
import ../../src/math/f64.bend as F
import ../../src/math/natural.bend as M

# Specification of src/math/f64.bend: IEEE 754-2019 binary64 with round to
# nearest, ties to even, written as Flocq writes it (Boldo & Melquiond,
# Flocq's Binary / Round_NE / Bracket developments; the same shape as the
# HOL Light and Isabelle IEEE_Floating_Point specifications): a finite
# double denotes the exact dyadic (-1)^s * m * 2^e, every operation computes
# its exact result on dyadics (or rationals, with a sticky bit) and rounds
# it once (round below). Special values follow IEEE 754 section 6 and the
# design reference python_style_math_stdlib_design.pdf (3.3, 4.4; appendix
# A): NaN in gives the canonical quiet NaN out, x + (-x) is +0 under round
# to nearest, inf - inf, 0 * inf, 0 / 0, inf / inf and sqrt of a negative
# number are NaN, x / 0 is a signed infinity, sqrt(-0) is -0, comparisons
# are false on NaN and +0 == -0.
#
# STATED, TESTED, NOT PROVED: tools/check_f64.py tests the implementation
# (Berkeley SoftFloat 3e's algorithms) against the machine's IEEE doubles on
# random bit patterns (zeros, subnormals, infinities, NaNs, rounding ties),
# and tools/check_f64_spec.py tests this reference itself against them
# through a line-by-line mirror; neither is a proof that the implementation
# equals the reference.
#
#   function            clauses
#   add, sub            Add.value, Sub.value
#   mul, div, sqrt      Mul.value, Div.value, Sqrt.value
#   lt, le, eq          Lt.value, Le.value, Eq.value
#   neg, abs, copysign  Neg.value, Abs.value, Copysign.value
#   is_nan, is_inf,     IsNan.value, IsInf.value, IsFinite.value,
#   is_finite, is_zero, IsZero.value, Signbit.value
#   signbit
#   of_nat              OfNat.value

# ---- the encoding ----

# The checker evaluates a closed Nat term such as 2^52 in unary, so no such
# constant appears here: widths are stated with C.shift (x * 2^k), C.low
# (n mod 2^k), C.high (n div 2^k) and C.fits (n < 2^k) on symbolic
# arguments, and the special bit patterns are U32 words. Each form is the
# plain arithmetic one (tools/check_f64_spec.py mirrors it line by line).

def hi_nat(x: F.F64) -> Nat:
  U32.to_nat(F.word_hi(x))

def lo_nat(x: F.F64) -> Nat:
  U32.to_nat(F.word_lo(x))

# bit 63, bits 52..62 and bits 0..51 of the pattern
def sign(+x: F.F64) -> Bool:
  Bool.not(C.fits(31n, hi_nat(x)))

def efield(+x: F.F64) -> Nat:
  C.low(11n, C.high(20n, hi_nat(x)))

def frac(+x: F.F64) -> Nat:
  Nat.add(lo_nat(x), C.shift(32n, C.low(20n, hi_nat(x))))

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the double with sign s, exponent field ef < 2^11 and fraction f < 2^52:
# (s * 2^11 + ef) * 2^52 + f
def encode(+s: Bool, +ef: Nat, +f: Nat) -> F.F64:
  F.Bits{U32.from_nat(C.low(32n, f)), U32.from_nat(Nat.add(C.high(32n, f), C.shift(20n, Nat.add(ef, C.shift(11n, b2n(s))))))}

def pick(-T: Data, c: Bool, +a: T, +b: T) -> T:
  match c:
    case True{}:
      a
    case False{}:
      b

# encode(False, 2047, 2^51), encode(s, 2047, 0) and encode(s, 0, 0)
def qnan() -> F.F64:
  F.Bits{0, 2146959360}

def inf(+s: Bool) -> F.F64:
  pick(F.F64, s, F.Bits{0, 4293918720}, F.Bits{0, 2146435072})

def zero(+s: Bool) -> F.F64:
  pick(F.F64, s, F.Bits{0, 2147483648}, F.Bits{0, 0})

def is_nan(+x: F.F64) -> Bool:
  Bool.and(Nat.is_eq(efield(x), 2047n), Bool.not(Nat.is_eq(frac(x), 0n)))

def is_inf(+x: F.F64) -> Bool:
  Bool.and(Nat.is_eq(efield(x), 2047n), Nat.is_eq(frac(x), 0n))

def is_zero(+x: F.F64) -> Bool:
  Bool.and(Nat.is_eq(efield(x), 0n), Nat.is_eq(frac(x), 0n))

# ---- the exact value of a finite double: m * 2^(xe - Z) ----
# Z keeps every exponent a natural number: the smallest (subnormal) is
# -1074 = 1926 - Z, and products and quotients stay above -Z.

def zb() -> Nat:
  3000n

# the fraction with the hidden bit 2^52 of a normal number
def mant(+x: F.F64) -> Nat:
  Nat.add(frac(x), C.shift(52n, b2n(Bool.not(Nat.is_eq(efield(x), 0n)))))

def xexp(+x: F.F64) -> Nat:
  pick(Nat, Nat.is_eq(efield(x), 0n), Nat.sub(zb(), 1074n), Nat.sub(Nat.add(efield(x), zb()), 1075n))

# ---- rounding (Flocq's round_NE on the binary64 format) ----

# m / 2^k rounded to nearest, ties to even: the quotient q, the remainder
# r and half the divisor h
def rne_up(+q: Nat, +r: Nat, +h: Nat) -> Nat:
  Nat.add(q, b2n(Bool.or(Nat.is_lt(h, r), Bool.and(Nat.is_eq(r, h), Nat.is_eq(Nat.mod(q, 2n), 1n)))))

def rne(+m: Nat, +k: Nat) -> Nat:
  match k:
    case 0n:
      m
    case 1n+ +j:
      rne_up(C.high(1n+j, m), C.low(1n+j, m), C.shift(j, 1n))

# a normal number (ef < 2047) or an overflow to infinity
def pack_e(+s: Bool, +ef: Nat, +f: Nat) -> F.F64:
  pick(F.F64, Nat.is_le(2047n, ef), inf(s), encode(s, ef, f))

# 2^52 <= q < 2^53 is normal with fraction q - 2^52, q < 2^52 subnormal
def pack_n(+s: Bool, +q: Nat, +u: Nat) -> F.F64:
  pick(F.F64, C.fits(52n, q), encode(s, 0n, q), pack_e(s, Nat.sub(Nat.add(u, 1075n), zb()), C.low(52n, q)))

# the double nearest to (-1)^s * q * 2^(u - Z) for a q of at most 53 bits at
# the ulp u (subnormal when q < 2^52), carrying a rounded-up q = 2^53 into
# 2^52 at the ulp 1 + u
def pack(+s: Bool, +q: Nat, +u: Nat) -> F.F64:
  pick(F.F64, C.fits(53n, q), pack_n(s, q, u), pack_e(s, Nat.sub(Nat.add(1n+u, 1075n), zb()), 0n))

# round (-1)^s * m * 2^(x - Z): the ulp is 2^(msb - 52), but never below
# the subnormal ulp 2^-1074
def round_u(+s: Bool, +m: Nat, +x: Nat, +u: Nat) -> F.F64:
  pack(s, pick(Nat, Nat.is_le(x, u), rne(m, Nat.sub(u, x)), C.shift(Nat.sub(x, u), m)), u)

def round(+s: Bool, +m: Nat, +x: Nat) -> F.F64:
  pick(F.F64, Nat.is_eq(m, 0n), zero(s), round_u(s, m, x, Nat.max(Nat.sub(Nat.add(x, M.bit_length(m)), 53n), Nat.sub(zb(), 1074n))))

# ---- the operations ----

# (-1)^sa A + (-1)^sb B at a common scale x: equal magnitudes of opposite
# signs cancel to +0 (round to nearest)
def sub_mag(+sa: Bool, +a: Nat, +sb: Bool, +b: Nat, +x: Nat, c: Cmp) -> F.F64:
  match c:
    case GT{}:
      round(sa, Nat.sub(a, b), x)
    case LT{}:
      round(sb, Nat.sub(b, a), x)
    case EQ{}:
      zero(False{})

def add_mag(+sa: Bool, +a: Nat, +sb: Bool, +b: Nat, +x: Nat) -> F.F64:
  pick(F.F64, Bool.not(Bool.xor(sa, sb)), round(sa, Nat.add(a, b), x), sub_mag(sa, a, sb, b, x, Nat.cmp(a, b)))

def add_fin(+x: F.F64, +y: F.F64) -> F.F64:
  add_mag(sign(x), C.shift(Nat.sub(xexp(x), Nat.min(xexp(x), xexp(y))), mant(x)), sign(y), C.shift(Nat.sub(xexp(y), Nat.min(xexp(x), xexp(y))), mant(y)), Nat.min(xexp(x), xexp(y)))

def add_inf(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, is_inf(x), pick(F.F64, Bool.and(is_inf(y), Bool.not(Bool.not(Bool.xor(sign(x), sign(y))))), qnan(), x), pick(F.F64, is_inf(y), y, add_fin(x, y)))

def add(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, Bool.or(is_nan(x), is_nan(y)), qnan(), add_inf(x, y))

# the double with the sign bit flipped (NaN included)
def neg(+x: F.F64) -> F.F64:
  encode(Bool.not(sign(x)), efield(x), frac(x))

def mul_inf(+x: F.F64, +y: F.F64, +s: Bool) -> F.F64:
  pick(F.F64, Bool.or(is_inf(x), is_inf(y)), pick(F.F64, Bool.or(is_zero(x), is_zero(y)), qnan(), inf(s)), round(s, Nat.mul(mant(x), mant(y)), Nat.sub(Nat.add(xexp(x), xexp(y)), zb())))

def mul(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, Bool.or(is_nan(x), is_nan(y)), qnan(), mul_inf(x, y, Bool.xor(sign(x), sign(y))))

# enough quotient bits for any pair of significands, plus a sticky bit
def kq() -> Nat:
  200n

def div_fin(+x: F.F64, +y: F.F64, +s: Bool) -> F.F64:
  round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(kq(), mant(x)), mant(y))), Nat.min(Nat.mod(C.shift(kq(), mant(x)), mant(y)), 1n)), Nat.sub(Nat.add(xexp(x), zb()), Nat.add(Nat.add(xexp(y), kq()), 1n)))

def div_cls(+x: F.F64, +y: F.F64, +s: Bool) -> F.F64:
  pick(F.F64, is_inf(x), pick(F.F64, is_inf(y), qnan(), inf(s)), pick(F.F64, is_inf(y), zero(s), pick(F.F64, is_zero(y), pick(F.F64, is_zero(x), qnan(), inf(s)), div_fin(x, y, s))))

def div(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, Bool.or(is_nan(x), is_nan(y)), qnan(), div_cls(x, y, Bool.xor(sign(x), sign(y))))

# sqrt(m * 2^(x - Z)) with x - Z made even: the integer square root of the
# significand scaled by 2^(2 K), and a sticky bit when it was not exact
def kr() -> Nat:
  100n

def sqrt_even(+m: Nat, +x: Nat) -> F.F64:
  round(False{}, Nat.add(Nat.mul(2n, M.isqrt(C.shift(Nat.mul(2n, kr()), m))), b2n(Bool.not(Nat.is_eq(Nat.pow(M.isqrt(C.shift(Nat.mul(2n, kr()), m)), 2n), C.shift(Nat.mul(2n, kr()), m))))), Nat.sub(Nat.add(Nat.div(x, 2n), Nat.div(zb(), 2n)), Nat.add(kr(), 1n)))

def sqrt_fin(+x: F.F64) -> F.F64:
  pick(F.F64, Nat.is_eq(Nat.mod(xexp(x), 2n), 0n), sqrt_even(mant(x), xexp(x)), sqrt_even(Nat.mul(2n, mant(x)), Nat.sub(xexp(x), 1n)))

def sqrt_cls(+x: F.F64) -> F.F64:
  pick(F.F64, is_zero(x), x, pick(F.F64, sign(x), qnan(), pick(F.F64, is_inf(x), x, sqrt_fin(x))))

def sqrt(+x: F.F64) -> F.F64:
  pick(F.F64, is_nan(x), qnan(), sqrt_cls(x))

# ---- comparisons: the order of the extended reals, false on NaN ----

# the order of two non-NaN doubles: infinities at the ends, zeros equal
def mag_cmp(+x: F.F64, +y: F.F64) -> Cmp:
  pick(Cmp, is_inf(x), pick(Cmp, is_inf(y), EQ{}, GT{}), pick(Cmp, is_inf(y), LT{}, Nat.cmp(C.shift(Nat.sub(xexp(x), Nat.min(xexp(x), xexp(y))), mant(x)), C.shift(Nat.sub(xexp(y), Nat.min(xexp(x), xexp(y))), mant(y)))))

def flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def ord(+x: F.F64, +y: F.F64) -> Cmp:
  pick(Cmp, Bool.and(is_zero(x), is_zero(y)), EQ{}, pick(Cmp, Bool.not(Bool.xor(sign(x), sign(y))), pick(Cmp, sign(x), flip(mag_cmp(x, y)), mag_cmp(x, y)), pick(Cmp, sign(x), LT{}, GT{})))

def ordered(+x: F.F64, +y: F.F64) -> Bool:
  Bool.not(Bool.or(is_nan(x), is_nan(y)))

# ---- the contract ----

def Add.value(+x: F.F64, +y: F.F64) -> Type:
  {F.add(x, y) == add(x, y) : F.F64}

# x - y is x + (-y)
def Sub.value(+x: F.F64, +y: F.F64) -> Type:
  {F.sub(x, y) == add(x, neg(y)) : F.F64}

def Mul.value(+x: F.F64, +y: F.F64) -> Type:
  {F.mul(x, y) == mul(x, y) : F.F64}

def Div.value(+x: F.F64, +y: F.F64) -> Type:
  {F.div(x, y) == div(x, y) : F.F64}

def Sqrt.value(+x: F.F64) -> Type:
  {F.sqrt(x) == sqrt(x) : F.F64}

def Lt.value(+x: F.F64, +y: F.F64) -> Type:
  {F.lt(x, y) == Bool.and(ordered(x, y), Cmp.is_lt(ord(x, y))) : Bool}

def Le.value(+x: F.F64, +y: F.F64) -> Type:
  {F.le(x, y) == Bool.and(ordered(x, y), Cmp.is_le(ord(x, y))) : Bool}

def Eq.value(+x: F.F64, +y: F.F64) -> Type:
  {F.eq(x, y) == Bool.and(ordered(x, y), Cmp.is_eq(ord(x, y))) : Bool}

def Neg.value(+x: F.F64) -> Type:
  {F.neg(x) == neg(x) : F.F64}

def Abs.value(+x: F.F64) -> Type:
  {F.abs(x) == encode(False{}, efield(x), frac(x)) : F.F64}

def Copysign.value(+x: F.F64, +y: F.F64) -> Type:
  {F.copysign(x, y) == encode(sign(y), efield(x), frac(x)) : F.F64}

def IsNan.value(+x: F.F64) -> Type:
  {F.is_nan(x) == is_nan(x) : Bool}

def IsInf.value(+x: F.F64) -> Type:
  {F.is_inf(x) == is_inf(x) : Bool}

def IsFinite.value(+x: F.F64) -> Type:
  {F.is_finite(x) == Bool.not(Nat.is_eq(efield(x), 2047n)) : Bool}

def IsZero.value(+x: F.F64) -> Type:
  {F.is_zero(x) == is_zero(x) : Bool}

def Signbit.value(+x: F.F64) -> Type:
  {F.signbit(x) == sign(x) : Bool}

# exact below 2^53, rounded above (the runtime bounds Nat by 2^48)
def OfNat.value(+n: Nat) -> Type:
  {F.of_nat(n) == round(False{}, n, zb()) : F.F64}
