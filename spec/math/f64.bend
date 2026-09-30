import Base
import ../lib/common.bend as C
import ../../src/math/f64.bend as F
import ../../src/math/natural.bend as M
import ../../src/math/u64.bend as WU
import ../../src/math/num.bend as N
import ./w64.bend as SW

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
# PROVED: every clause below is proved for every input in
# proofs/math/typed/f64*.bend (no holes, no axioms). TESTED as well:
# tools/check_f64.py and tools/check_f64x.py test the implementation
# against the machine's IEEE doubles and CPython's math module on random bit
# patterns (zeros, subnormals, infinities, NaNs, rounding ties, appendix A's
# special values), and tools/check_f64_spec.py tests the arithmetic part of
# this reference itself against them through a line-by-line mirror.
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
#
# Rounding, conversions and the rest of the design reference's float
# foundation (python_style_math_stdlib_design.pdf 3.1, 3.3, 4.3, 4.4, 10 and
# appendix A; IEEE 754-2019 5.3.1, 5.3.3, 5.8, 9.6; C99 annex F):
#
#   trunc, floor, ceil, round   Trunc.value, Floor.value, Ceil.value,
#                               Round.value (roundToIntegral, ties to even)
#   to_u64, to_u32              ToU64.value, ToU32.value
#   floor_u64, ceil_u64,        FloorU64.value, CeilU64.value,
#   round_u64                   RoundU64.value
#   of_u64, of_u32              OfU64.value, OfU32.value
#   frexp, ldexp, ulp           Frexp.value, Ldexp.value, Ulp.value
#   nextafter                   Nextafter.value
#   fmin, fmax                  Fmin.value, Fmax.value (minimumNumber,
#                               maximumNumber)
#   is_normal, is_subnormal     IsNormal.value, IsSubnormal.value
#   to_bits, of_bits64          Bits.value, Bits.roundtrip, Bits.inverse
#   is_integer                  IsInteger.value
#   modf                        Modf.value
#   fmod, remainder             Fmod.value, Remainder.value (exact)
#   isclose                     IsClose.value
#   as_integer_ratio            AsIntegerRatio.value

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

# pick for pairs (a Sigma is Type-sorted)
def pickt(-T: Type, c: Bool, a: T, b: T) -> T:
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

# ---- rounding to an integral value (IEEE 754 roundToIntegral) ----

# the integer magnitude of (-1)^s * m * 2^-k, k >= 1, in each direction: the
# integer part high(k, m), plus one when the discarded low(k, m) is nonzero
# and the direction is away from zero (floor of a negative, ceil of a
# positive), or to nearest with ties to even (rne)
def integral(m: F.RMode, +s: Bool, +n: Nat, +k: Nat) -> Nat:
  match m:
    case F.Trunc{}:
      C.high(k, n)
    case F.Floor{}:
      Nat.add(C.high(k, n), b2n(Bool.and(s, Bool.not(Nat.is_eq(C.low(k, n), 0n)))))
    case F.Ceil{}:
      Nat.add(C.high(k, n), b2n(Bool.and(Bool.not(s), Bool.not(Nat.is_eq(C.low(k, n), 0n)))))
    case F.Even{}:
      rne(n, k)

# NaN gives NaN, an infinity or a value of at least 2^52 is already integral,
# anything else is its integer (with the sign of x, so -0.5 goes to -0 under
# trunc, ceil and round)
def to_integral(m: F.RMode, +x: F.F64) -> F.F64:
  pick(F.F64, is_nan(x), qnan(), pick(F.F64, Bool.or(is_inf(x), Nat.is_le(zb(), xexp(x))), x, round(sign(x), integral(m, sign(x), mant(x), Nat.sub(zb(), xexp(x))), zb())))

def Trunc.value(+x: F.F64) -> Type:
  {F.trunc(x) == to_integral(F.Trunc{}, x) : F.F64}

def Floor.value(+x: F.F64) -> Type:
  {F.floor(x) == to_integral(F.Floor{}, x) : F.F64}

def Ceil.value(+x: F.F64) -> Type:
  {F.ceil(x) == to_integral(F.Ceil{}, x) : F.F64}

def Round.value(+x: F.F64) -> Type:
  {F.round(x) == to_integral(F.Even{}, x) : F.F64}

# ---- conversions ----

# the integer part of |x| (x finite)
def int_part(+x: F.F64) -> Nat:
  pick(Nat, Nat.is_le(zb(), xexp(x)), C.shift(Nat.sub(xexp(x), zb()), mant(x)), C.high(Nat.sub(zb(), xexp(x)), mant(x)))

# x truncated toward zero as a w-bit unsigned integer: NaN is a domain error;
# an infinity, a truncation below zero or one of 2^w or more an overflow
# (3.1: int(x) truncates; 2.6: fixed widths raise instead of wrapping)
def to_nat(+x: F.F64, +w: Nat) -> Result<&2, &2, N.NumError, Nat>:
  pick(Result<&2, &2, N.NumError, Nat>, is_nan(x), Fail{N.BadDomain{}}, pick(Result<&2, &2, N.NumError, Nat>, Bool.or(is_inf(x), Bool.or(Bool.and(sign(x), Bool.not(Nat.is_eq(int_part(x), 0n))), Bool.not(C.fits(w, int_part(x))))), Fail{N.Overflow{}}, Done{int_part(x)}))

def rv64(r: Result<&2, &2, N.NumError, WU.U64>) -> Result<&2, &2, N.NumError, Nat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{w}:
      Done{SW.value(w)}

def rv32(r: Result<&2, &2, N.NumError, U32>) -> Result<&2, &2, N.NumError, Nat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{U32.to_nat(u)}

def ToU64.value(+x: F.F64) -> Type:
  {rv64(F.to_u64(x)) == to_nat(x, 64n) : Result<&2, &2, N.NumError, Nat>}

def ToU32.value(+x: F.F64) -> Type:
  {rv32(F.to_u32(x)) == to_nat(x, 32n) : Result<&2, &2, N.NumError, Nat>}

def FloorU64.value(+x: F.F64) -> Type:
  {rv64(F.floor_u64(x)) == to_nat(to_integral(F.Floor{}, x), 64n) : Result<&2, &2, N.NumError, Nat>}

def CeilU64.value(+x: F.F64) -> Type:
  {rv64(F.ceil_u64(x)) == to_nat(to_integral(F.Ceil{}, x), 64n) : Result<&2, &2, N.NumError, Nat>}

def RoundU64.value(+x: F.F64) -> Type:
  {rv64(F.round_u64(x)) == to_nat(to_integral(F.Even{}, x), 64n) : Result<&2, &2, N.NumError, Nat>}

# the double nearest to an unsigned integer (exact below 2^53)
def OfU64.value(+w: WU.U64) -> Type:
  {F.of_u64(w) == round(False{}, SW.value(w), zb()) : F.F64}

def OfU32.value(+u: U32) -> Type:
  {F.of_u32(u) == round(False{}, U32.to_nat(u), zb()) : F.F64}

# ---- exponents ----

# t - Z as a signed exponent
def exp_of(+t: Nat) -> F.Exp:
  pick(F.Exp, Nat.is_le(zb(), t), F.Exp{False{}, Nat.sub(t, zb())}, F.Exp{True{}, Nat.sub(zb(), t)})

# (m, e) with x = m 2^e and 1/2 <= |m| < 1: m is mant(x) scaled by
# 2^-bit_length(mant(x)) (exact), e the rest of the scale; NaN gives (NaN, 0),
# zeros and infinities (x, 0) (4.4)
def frexp(+x: F.F64) -> F.F64 & F.Exp:
  pickt(F.F64 & F.Exp, is_nan(x), (qnan(), F.Exp{False{}, 0n}), pickt(F.F64 & F.Exp, Bool.or(is_inf(x), is_zero(x)), (x, F.Exp{False{}, 0n}), (round(sign(x), mant(x), Nat.sub(zb(), M.bit_length(mant(x)))), exp_of(Nat.add(xexp(x), M.bit_length(mant(x)))))))

def Frexp.value(+x: F.F64) -> Type:
  {F.frexp(x) == frexp(x) : F.F64 & F.Exp}

# x 2^e rounded once: overflow to infinity, gradual underflow (4.4); a
# scale below 2^-Z is a product under 2^-2947, which rounds to a zero like
# the scale 0 it is cut to
def ldexp(+x: F.F64, +neg: Bool, +k: Nat) -> F.F64:
  pick(F.F64, is_nan(x), qnan(), pick(F.F64, Bool.or(is_inf(x), is_zero(x)), x, round(sign(x), mant(x), pick(Nat, neg, Nat.sub(xexp(x), k), Nat.add(xexp(x), k)))))

def Ldexp.value(+x: F.F64, +neg: Bool, +k: Nat) -> Type:
  {F.ldexp(x, F.Exp{neg, k}) == ldexp(x, neg, k) : F.F64}

# the weight of the last bit of x: 2^(xexp(x) - Z) (the smallest subnormal
# for zeros), inf for infinities, NaN for NaN (4.4)
def Ulp.value(+x: F.F64) -> Type:
  {F.ulp(x) == pick(F.F64, is_nan(x), qnan(), pick(F.F64, is_inf(x), inf(False{}), round(False{}, 1n, xexp(x)))) : F.F64}

# ---- neighbours and NaN-ignoring extrema ----

# the magnitude bits: exponent field and fraction as one integer below 2^63
def pat(+x: F.F64) -> Nat:
  Nat.add(frac(x), C.shift(52n, efield(x)))

def of_pat(+s: Bool, +p: Nat) -> F.F64:
  encode(s, C.high(52n, p), C.low(52n, p))

# the ordered-set neighbour (IEEE nextAfter, C99 annex F): NaN in, NaN out;
# y when x == y; from a zero the smallest subnormal with y's sign; otherwise
# one step of the magnitude bits, up when moving away from zero (the step past
# the largest finite double is infinity, the step below the smallest
# subnormal a zero of x's sign)
def nextafter(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, Bool.not(ordered(x, y)), qnan(), pick(F.F64, Cmp.is_eq(ord(x, y)), y, pick(F.F64, is_zero(x), encode(sign(y), 0n, 1n), of_pat(sign(x), pick(Nat, Bool.xor(Cmp.is_lt(ord(x, y)), sign(x)), Nat.add(pat(x), 1n), Nat.sub(pat(x), 1n))))))

def Nextafter.value(+x: F.F64, +y: F.F64) -> Type:
  {F.nextafter(x, y) == nextafter(x, y) : F.F64}

# IEEE 754-2019 minimumNumber / maximumNumber (10: fmin/fmax fix the
# order dependence of min/max with NaN): a NaN operand is ignored, -0 < +0
def fmin(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, is_nan(x), pick(F.F64, is_nan(y), qnan(), y), pick(F.F64, is_nan(y), x, pick(F.F64, Bool.and(is_zero(x), is_zero(y)), zero(Bool.or(sign(x), sign(y))), pick(F.F64, Cmp.is_lt(ord(x, y)), x, y))))

def fmax(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, is_nan(x), pick(F.F64, is_nan(y), qnan(), y), pick(F.F64, is_nan(y), x, pick(F.F64, Bool.and(is_zero(x), is_zero(y)), zero(Bool.and(sign(x), sign(y))), pick(F.F64, Cmp.is_lt(ord(y, x)), x, y))))

def Fmin.value(+x: F.F64, +y: F.F64) -> Type:
  {F.fmin(x, y) == fmin(x, y) : F.F64}

def Fmax.value(+x: F.F64, +y: F.F64) -> Type:
  {F.fmax(x, y) == fmax(x, y) : F.F64}

# ---- classification, bit casts, integrality ----

def IsNormal.value(+x: F.F64) -> Type:
  {F.is_normal(x) == Bool.and(Bool.not(Nat.is_eq(efield(x), 0n)), Nat.is_lt(efield(x), 2047n)) : Bool}

def IsSubnormal.value(+x: F.F64) -> Type:
  {F.is_subnormal(x) == Bool.and(Nat.is_eq(efield(x), 0n), Bool.not(Nat.is_eq(frac(x), 0n))) : Bool}

# the 64-bit pattern: sign, exponent field, fraction
def Bits.value(+x: F.F64) -> Type:
  {SW.value(F.to_bits(x)) == Nat.add(pat(x), C.shift(63n, b2n(sign(x)))) : Nat}

def Bits.roundtrip(+x: F.F64) -> Type:
  {F.of_bits64(F.to_bits(x)) == x : F.F64}

def Bits.inverse(+w: WU.U64) -> Type:
  {F.to_bits(F.of_bits64(w)) == w : WU.U64}

# finite with no fractional bits
def IsInteger.value(+x: F.F64) -> Type:
  {F.is_integer(x) == Bool.and(Nat.is_lt(efield(x), 2047n), Bool.or(Nat.is_le(zb(), xexp(x)), Nat.is_eq(C.low(Nat.sub(zb(), xexp(x)), mant(x)), 0n))) : Bool}

# ---- the fractional part and the exact remainders ----

# (fractional part, integral part), both with the sign of x, both exact:
# modf(-2.0) = (-0.0, -2.0), modf(inf) = (0.0, inf) (4.3)
def modf(+x: F.F64) -> F.F64 & F.F64:
  pickt(F.F64 & F.F64, is_nan(x), (qnan(), qnan()), pickt(F.F64 & F.F64, Bool.or(is_inf(x), Nat.is_le(zb(), xexp(x))), (zero(sign(x)), x), (round(sign(x), C.low(Nat.sub(zb(), xexp(x)), mant(x)), xexp(x)), to_integral(F.Trunc{}, x))))

def Modf.value(+x: F.F64) -> Type:
  {F.modf(x) == modf(x) : F.F64 & F.F64}

# the significands of x and y at their common scale
def rsc(+x: F.F64, +y: F.F64) -> Nat:
  Nat.min(xexp(x), xexp(y))

def ra(+x: F.F64, +y: F.F64) -> Nat:
  C.shift(Nat.sub(xexp(x), rsc(x, y)), mant(x))

def rb(+x: F.F64, +y: F.F64) -> Nat:
  C.shift(Nat.sub(xexp(y), rsc(x, y)), mant(y))

def rbad(+x: F.F64, +y: F.F64) -> Bool:
  Bool.or(Bool.or(Bool.not(ordered(x, y)), is_inf(x)), is_zero(y))

# x - n y with n = trunc(x / y): the exact remainder of the scaled
# significands, with the sign of x; NaN for NaN, an infinite x or a zero y;
# x for an infinite y (4.3: fmod(x, inf) == x)
def fmod(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, rbad(x, y), qnan(), pick(F.F64, is_inf(y), x, round(sign(x), Nat.mod(ra(x, y), rb(x, y)), rsc(x, y))))

def Fmod.value(+x: F.F64, +y: F.F64) -> Type:
  {F.fmod(x, y) == fmod(x, y) : F.F64}

# IEEE remainder, x - n y with n = x / y rounded to nearest, ties to even:
# from r = A mod B and q = A div B, n is q + 1 when r is past half of B (or
# exactly half with q odd), which leaves B - r with the opposite sign; a zero
# result has the sign of x (4.3)
def rflip(+r: Nat, +b: Nat, +q: Nat) -> Bool:
  Bool.or(Nat.is_lt(b, Nat.add(r, r)), Bool.and(Nat.is_eq(Nat.add(r, r), b), Nat.is_eq(Nat.mod(q, 2n), 1n)))

def rnear(+s: Bool, +r: Nat, +b: Nat, +q: Nat, +u: Nat) -> F.F64:
  pick(F.F64, rflip(r, b, q), round(Bool.not(s), Nat.sub(b, r), u), round(s, r, u))

def remainder(+x: F.F64, +y: F.F64) -> F.F64:
  pick(F.F64, rbad(x, y), qnan(), pick(F.F64, is_inf(y), x, rnear(sign(x), Nat.mod(ra(x, y), rb(x, y)), rb(x, y), Nat.div(ra(x, y), rb(x, y)), rsc(x, y))))

def Remainder.value(+x: F.F64, +y: F.F64) -> Type:
  {F.remainder(x, y) == remainder(x, y) : F.F64}

# ---- closeness and exact ratios ----

def lt_s(+x: F.F64, +y: F.F64) -> Bool:
  Bool.and(ordered(x, y), Cmp.is_lt(ord(x, y)))

def le_s(+x: F.F64, +y: F.F64) -> Bool:
  Bool.and(ordered(x, y), Cmp.is_le(ord(x, y)))

def eq_s(+x: F.F64, +y: F.F64) -> Bool:
  Bool.and(ordered(x, y), Cmp.is_eq(ord(x, y)))

def fabs(+x: F.F64) -> F.F64:
  encode(False{}, efield(x), frac(x))

# CPython's math.isclose, computed in binary64: a negative tolerance is a
# domain error; a == b is close, an infinity is close only to itself, and
# otherwise |b - a| <= max(|rel * b|, |rel * a|, abs_tol) (4.4)
def ic_near(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +d: F.F64) -> Bool:
  Bool.or(Bool.or(le_s(d, fabs(mul(rel, b))), le_s(d, fabs(mul(rel, a)))), le_s(d, at))

def isclose(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> Result<&2, &2, N.NumError, Bool>:
  pick(Result<&2, &2, N.NumError, Bool>, Bool.or(lt_s(rel, zero(False{})), lt_s(at, zero(False{}))), Fail{N.BadDomain{}}, Done{pick(Bool, eq_s(a, b), True{}, pick(Bool, Bool.or(is_inf(a), is_inf(b)), False{}, ic_near(a, b, rel, at, fabs(add(b, neg(a))))))})

def IsClose.value(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> Type:
  {F.isclose(a, b, rel, at) == isclose(a, b, rel, at) : Result<&2, &2, N.NumError, Bool>}

# trailing zero bits of n (at most fuel)
def tz(fuel: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      pick(Nat, Nat.is_eq(Nat.mod(n, 2n), 1n), 0n, 1n+tz(f, Nat.div(n, 2n)))

# (sign, numerator, exponent of the denominator)
type Rat is Data:
  Rat{neg: Bool, num: Nat, den: Nat}

def rtriple(r: Result<&2, &2, N.NumError, F.Ratio>) -> Result<&2, &2, N.NumError, Rat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{F.Ratio{neg, num, den}}:
      Done{Rat{neg, SW.value(num), den}}

# x = +-num / 2^den in lowest terms: the significand with as many of its
# trailing zeros moved into the denominator as the scale allows; a zero is
# 0/1 (Python's ints have no -0); NaN is a domain error, an infinity or an
# integer of 2^64 or more an overflow (3.3)
def as_ratio(+x: F.F64) -> Result<&2, &2, N.NumError, Rat>:
  pick(Result<&2, &2, N.NumError, Rat>, is_nan(x), Fail{N.BadDomain{}}, pick(Result<&2, &2, N.NumError, Rat>, is_inf(x), Fail{N.Overflow{}}, pick(Result<&2, &2, N.NumError, Rat>, is_zero(x), Done{Rat{False{}, 0n, 0n}}, pick(Result<&2, &2, N.NumError, Rat>, Nat.is_le(zb(), xexp(x)), pick(Result<&2, &2, N.NumError, Rat>, C.fits(64n, int_part(x)), Done{Rat{sign(x), int_part(x), 0n}}, Fail{N.Overflow{}}), Done{Rat{sign(x), C.high(Nat.min(tz(64n, mant(x)), Nat.sub(zb(), xexp(x))), mant(x)), Nat.sub(Nat.sub(zb(), xexp(x)), Nat.min(tz(64n, mant(x)), Nat.sub(zb(), xexp(x))))}}))))

def AsIntegerRatio.value(+x: F.F64) -> Type:
  {rtriple(F.as_integer_ratio(x)) == as_ratio(x) : Result<&2, &2, N.NumError, Rat>}
