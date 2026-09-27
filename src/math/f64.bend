import Base
import ./num.bend as N
import ./u64.bend as W
import ./w64.bend as X
import ./natural.bend as M

# IEEE-754 binary64 in software, on two U32 words (Bend 2 has only F32).
# The algorithms are Berkeley SoftFloat 3e's (f64_add/f64_sub through
# addMags/subMags, f64_mul, roundPackToF64 and normRoundPackToF64, round to
# nearest with ties to even), on 64-bit significands held as two U32 limbs
# (w64.bend). Division is exact long division by 32-bit quotient digits and
# the square root one step of Zimmermann's Karatsuba square root with its
# exact remainder, each followed by a sticky bit, so every result is correctly rounded: subnormals, overflow
# to infinity, signed zeros and NaN follow IEEE 754 (x + (-x) is +0, 0/0 and
# inf - inf are NaN; a NaN result is the canonical quiet NaN).
#
#   of_bits(hi, lo), word_hi(x), word_lo(x)          the bit pattern
#   is_nan, is_inf, is_finite, is_zero, signbit
#   neg, abs, copysign
#   add, sub, mul, div, sqrt               correctly rounded
#   lt, le, eq                             IEEE comparisons (NaN unordered)
#   of_nat(n)                              correctly rounded (exact below 2^53)
#   f64_op, f64_is                         the num.bend instance
#
# Exponents that may go below zero before rounding are kept as naturals
# offset by OFF = 4096. Tested against the machine's doubles
# (tools/check_f64.py); not proved.

type F64 is Data:
  Bits{lo: U32, hi: U32}

def word_lo(x: F64) -> U32:
  match x:
    case Bits{l, h}:
      l

def word_hi(x: F64) -> U32:
  match x:
    case Bits{l, h}:
      h

def of_bits(+hi: U32, +lo: U32) -> F64:
  Bits{lo, hi}

def off() -> Nat:
  4096n

def sgn(s: Bool) -> U32:
  match s:
    case True{}:
      2147483648
    case False{}:
      0

# ---- fields ----

def signbit(+x: F64) -> Bool:
  U32.is_le(2147483648, word_hi(x))

def exp_field(+x: F64) -> Nat:
  U32.to_nat(U32.and(U32.div(word_hi(x), 1048576), 2047))

def frac(+x: F64) -> W.U64:
  W.U64{word_lo(x), U32.and(word_hi(x), 1048575)}

def mag(+x: F64) -> W.U64:
  W.U64{word_lo(x), U32.and(word_hi(x), 2147483647)}

def nz(+a: W.U64) -> Bool:
  Bool.not(X.is_zero(a))

def is_nan(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 2047n), nz(frac(x)))

def is_inf(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 2047n), X.is_zero(frac(x)))

def is_finite(+x: F64) -> Bool:
  Nat.is_lt(exp_field(x), 2047n)

def is_zero(+x: F64) -> Bool:
  X.is_zero(mag(x))

# ---- constants and sign ----

def nan() -> F64:
  Bits{0, 2146959360}

def inf(s: Bool) -> F64:
  Bits{0, U32.add(2146435072, sgn(s))}

def zero(s: Bool) -> F64:
  Bits{0, sgn(s)}

def one() -> F64:
  Bits{0, 1072693248}

def neg(+x: F64) -> F64:
  Bits{word_lo(x), U32.xor(word_hi(x), 2147483648)}

def abs(+x: F64) -> F64:
  Bits{word_lo(x), U32.and(word_hi(x), 2147483647)}

def copysign(+x: F64, +y: F64) -> F64:
  Bits{word_lo(x), U32.add(U32.and(word_hi(x), 2147483647), U32.and(word_hi(y), 2147483648))}

def nan_or(+x: F64, bad: Bool) -> F64:
  match bad:
    case True{}:
      nan()
    case False{}:
      x

# ---- packing and rounding (SoftFloat's packToF64, roundPackToF64) ----

def pack64(+w: W.U64) -> F64:
  Bits{X.lo(w), X.hi(w)}

# sign, exponent field e and significand m; the hidden bit of m (bit 52)
# carries into the exponent field, as packToF64's addition does
def pack(s: Bool, +e: Nat, +m: W.U64) -> F64:
  pack64(X.add(W.U64{0, U32.add(sgn(s), U32.mul(U32.from_nat(e), 1048576))}, m))

def zero_e(+e: Nat, z: Bool) -> Nat:
  match z:
    case True{}:
      0n
    case False{}:
      e

def rp_fin3(+s: Bool, +e: Nat, +r: W.U64) -> F64:
  pack(s, zero_e(e, X.is_zero(r)), r)

def rp_fin2(+s: Bool, +e: Nat, +r: W.U64, tie: Bool) -> F64:
  rp_fin3(s, e, X.clear0(r, tie))

# sig has its top bit at 62 and e is the plain exponent (0 <= e <= 0x7FD):
# add half an ulp of the kept 53 bits, shift, and clear bit 0 on a tie
def rp_fin(+s: Bool, +e: Nat, +sig: W.U64) -> F64:
  rp_fin2(s, e, X.shr(X.add(sig, W.U64{512, 0}), 10n), U32.is_eq(U32.and(X.lo(sig), 1023), 512))

def rp_over(+s: Bool, +e: Nat, +sig: W.U64, over: Bool) -> F64:
  match over:
    case True{}:
      inf(s)
    case False{}:
      rp_fin(s, Nat.sub(e, off()), sig)

def rp_neg(+s: Bool, +e: Nat, +sig: W.U64, below: Bool) -> F64:
  match below:
    case True{}:
      rp_fin(s, 0n, X.shr_jam(sig, Nat.sub(off(), e)))
    case False{}:
      rp_over(s, e, sig, Bool.or(Nat.is_lt(Nat.add(off(), 2045n), e), Bool.and(Nat.is_eq(e, Nat.add(off(), 2045n)), X.le(W.U64{0, 2147483648}, X.add(sig, W.U64{512, 0})))))

# e is the biased exponent minus one, offset by OFF; sig has its top bit at 62
def round_pack(+s: Bool, +e: Nat, +sig: W.U64) -> F64:
  rp_neg(s, e, sig, Nat.is_lt(e, off()))

# sig below 2^62 is shifted up once
def rp62_pick(+s: Bool, +e: Nat, +sig: W.U64, low: Bool) -> F64:
  match low:
    case True{}:
      round_pack(s, Nat.sub(e, 1n), X.add(sig, sig))
    case False{}:
      round_pack(s, e, sig)

def rp62(+s: Bool, +e: Nat, +sig: W.U64) -> F64:
  rp62_pick(s, e, sig, X.lt(sig, W.U64{0, 1073741824}))

def nrp_exp(+e: Nat, +sd: Nat, z: Bool) -> Nat:
  match z:
    case True{}:
      0n
    case False{}:
      Nat.sub(Nat.sub(e, sd), off())

def nrp_pick(+s: Bool, +e: Nat, +sig: W.U64, +sd: Nat, direct: Bool) -> F64:
  match direct:
    case True{}:
      pack(s, nrp_exp(e, sd, X.is_zero(sig)), X.shl(sig, Nat.sub(sd, 10n)))
    case False{}:
      round_pack(s, Nat.sub(e, sd), X.shl(sig, sd))

def nrp_sd(+s: Bool, +e: Nat, +sig: W.U64, +sd: Nat) -> F64:
  nrp_pick(s, e, sig, sd, Bool.and(Nat.is_le(10n, sd), Bool.and(Nat.is_le(Nat.add(off(), sd), e), Nat.is_lt(Nat.sub(e, sd), Nat.add(off(), 2045n)))))

# SoftFloat's normRoundPackToF64 (e offset)
def norm_round_pack(+s: Bool, +e: Nat, +sig: W.U64) -> F64:
  nrp_sd(s, e, sig, Nat.sub(X.clz(sig), 1n))

# the offset exponent and 53-bit significand (hidden bit at 52) of a nonzero
# finite value, subnormals normalized (SoftFloat's normSubnormalF64Sig)
def norm_e(+e: Nat, +f: W.U64) -> Nat:
  match e:
    case 0n:
      Nat.sub(Nat.add(off(), 12n), X.clz(f))
    case _:
      Nat.add(off(), e)

def norm_f(+e: Nat, +f: W.U64) -> W.U64:
  match e:
    case 0n:
      X.shl(f, Nat.sub(X.clz(f), 11n))
    case _:
      X.add(f, W.U64{0, 1048576})

# ---- addition (SoftFloat's addMagsF64 and subMagsF64) ----

def am_small(+e: Nat, +f9: W.U64) -> W.U64:
  match e:
    case 0n:
      X.add(f9, f9)
    case _:
      X.add(f9, W.U64{0, 536870912})

# |x| + |y| with sign s, the larger exponent eL
def am_big(+big: F64, +s: Bool, +el: Nat, +fl: W.U64, +es: Nat, +fs: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(big, nz(fl))
    case False{}:
      rp62(s, Nat.add(off(), el), X.add(X.add(W.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(am_small(es, X.shl(fs, 9n)), Nat.sub(el, es))))

def am_eq_n(+x: F64, +s: Bool, +e: Nat, +fa: W.U64, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(x, Bool.or(nz(fa), nz(fb)))
    case False{}:
      round_pack(s, Nat.add(off(), e), X.shl(X.add(W.U64{0, 2097152}, X.add(fa, fb)), 9n))

def am_eq(+x: F64, +s: Bool, +e: Nat, +fa: W.U64, +fb: W.U64) -> F64:
  match e:
    case 0n:
      pack(s, 0n, X.add(fa, fb))
    case _:
      am_eq_n(x, s, e, fa, fb, Nat.is_eq(e, 2047n))

def am_case(+x: F64, +y: F64, +s: Bool, +ea: Nat, +eb: Nat, c: Cmp) -> F64:
  match c:
    case EQ{}:
      am_eq(x, s, ea, frac(x), frac(y))
    case LT{}:
      am_big(y, s, eb, frac(y), ea, frac(x), Nat.is_eq(eb, 2047n))
    case GT{}:
      am_big(x, s, ea, frac(x), eb, frac(y), Nat.is_eq(ea, 2047n))

def add_mags(+x: F64, +y: F64, +s: Bool) -> F64:
  am_case(x, y, s, exp_field(x), exp_field(y), Nat.cmp(exp_field(x), exp_field(y)))

def sm_small(+e: Nat, +f10: W.U64) -> W.U64:
  match e:
    case 0n:
      X.add(f10, f10)
    case _:
      X.add(f10, W.U64{0, 1073741824})

# |big| - |small| with sign s, the larger exponent eL
def sm_big(+big: F64, +s: Bool, +el: Nat, +fl: W.U64, +es: Nat, +fs: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(big, nz(fl))
    case False{}:
      norm_round_pack(s, Nat.add(off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), W.U64{0, 1073741824}), X.shr_jam(sm_small(es, X.shl(fs, 10n)), Nat.sub(el, es))))

def sm_exact3(+s: Bool, +e1: Nat, +d: W.U64, +sd: Nat, under: Bool) -> F64:
  match under:
    case True{}:
      pack(s, 0n, X.shl(d, e1))
    case False{}:
      pack(s, Nat.sub(e1, sd), X.shl(d, sd))

# an exact difference of equal exponents, normalized without rounding
def sm_exact(+s: Bool, +e1: Nat, +d: W.U64) -> F64:
  sm_exact3(s, e1, d, Nat.sub(X.clz(d), 11n), Nat.is_lt(e1, Nat.sub(X.clz(d), 11n)))

def sm_eq2(+s: Bool, +e: Nat, +fa: W.U64, +fb: W.U64, c: Cmp) -> F64:
  match c:
    case EQ{}:
      zero(False{})
    case LT{}:
      sm_exact(Bool.not(s), Nat.sub(e, 1n), X.sub(fb, fa))
    case GT{}:
      sm_exact(s, Nat.sub(e, 1n), X.sub(fa, fb))

def cmp64(+a: W.U64, +b: W.U64) -> Cmp:
  X.cmp(a, b)

def sm_eq(+s: Bool, +e: Nat, +fa: W.U64, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan()
    case False{}:
      sm_eq2(s, e, fa, fb, cmp64(fa, fb))

def sm_case(+x: F64, +y: F64, +s: Bool, +ea: Nat, +eb: Nat, c: Cmp) -> F64:
  match c:
    case EQ{}:
      sm_eq(s, ea, frac(x), frac(y), Nat.is_eq(ea, 2047n))
    case LT{}:
      sm_big(y, Bool.not(s), eb, frac(y), ea, frac(x), Nat.is_eq(eb, 2047n))
    case GT{}:
      sm_big(x, s, ea, frac(x), eb, frac(y), Nat.is_eq(ea, 2047n))

def sub_mags(+x: F64, +y: F64, +s: Bool) -> F64:
  sm_case(x, y, s, exp_field(x), exp_field(y), Nat.cmp(exp_field(x), exp_field(y)))

def add_pick(+x: F64, +y: F64, same: Bool) -> F64:
  match same:
    case True{}:
      add_mags(x, y, signbit(x))
    case False{}:
      sub_mags(x, y, signbit(x))

def add(+x: F64, +y: F64) -> F64:
  add_pick(x, y, Bool.not(Bool.xor(signbit(x), signbit(y))))

def sub(+x: F64, +y: F64) -> F64:
  add(x, neg(y))

# ---- multiplication (SoftFloat's f64_mul) ----

def mul_n2(+s: Bool, +e: Nat, p: W.U64 & W.U64) -> F64:
  (+pl, +ph) = p
  rp62(s, e, X.or_bit(ph, nz(pl)))

def mul_n(+s: Bool, +ea: Nat, +ma: W.U64, +eb: Nat, +mb: W.U64) -> F64:
  mul_n2(s, Nat.sub(Nat.add(ea, eb), Nat.add(off(), 1023n)), X.mul128(X.shl(ma, 10n), X.shl(mb, 11n)))

def fin_zero(+e: Nat, +f: W.U64) -> Bool:
  Bool.and(Nat.is_eq(e, 0n), X.is_zero(f))

def mul_z(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, z: Bool) -> F64:
  match z:
    case True{}:
      zero(s)
    case False{}:
      mul_n(s, norm_e(ea, fa), norm_f(ea, fa), norm_e(eb, fb), norm_f(eb, fb))

def inf_or_nan(+s: Bool, bad: Bool) -> F64:
  match bad:
    case True{}:
      nan()
    case False{}:
      inf(s)

def mul_b(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      inf_or_nan(s, Bool.or(nz(fb), fin_zero(ea, fa)))
    case False{}:
      mul_z(s, ea, fa, eb, fb, Bool.or(fin_zero(ea, fa), fin_zero(eb, fb)))

def mul_cls(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      inf_or_nan(s, Bool.or(Bool.or(nz(fa), Bool.and(Nat.is_eq(eb, 2047n), nz(fb))), fin_zero(eb, fb)))
    case False{}:
      mul_b(s, ea, fa, eb, fb, Nat.is_eq(eb, 2047n))

def mul(+x: F64, +y: F64) -> F64:
  mul_cls(Bool.xor(signbit(x), signbit(y)), exp_field(x), frac(x), exp_field(y), frac(y), Nat.is_eq(exp_field(x), 2047n))

# ---- division ----

# the next quotient digit of r * 2^32 / b (r < b, b >= 2^52) and the remainder
def digit_fin(+r: W.U64, +b: W.U64, +d: U32) -> U32 & W.U64:
  (d, X.sub(W.U64{0, X.lo(r)}, X.fst_q(X.mul_32_64(d, b))))

def digit(+r: W.U64, +b: W.U64, +t: Nat) -> U32 & W.U64:
  digit_fin(r, b, X.q96(W.U64{0, X.lo(r)}, X.hi(r), b, t))

def dq_fin(+s: Bool, +e: Nat, +d1: U32, p: U32 & W.U64) -> F64:
  (+d2, +r2) = p
  round_pack(s, e, X.or_bit(X.add(W.U64{0, 1073741824}, X.shr(W.U64{d2, d1}, 2n)), Bool.or(nz(r2), Bool.not(U32.is_zero(U32.and(d2, 3))))))

def dq_mid(+s: Bool, +e: Nat, +b: W.U64, +t: Nat, p: U32 & W.U64) -> F64:
  (+d1, +r1) = p
  dq_fin(s, e, d1, digit(r1, b, t))

# a in [b, 2b): 2^62 + floor((a - b) * 2^62 / b), sticky, by two 32-bit digits
def div_qt(+s: Bool, +e: Nat, +a: W.U64, +b: W.U64, +t: Nat) -> F64:
  dq_mid(s, e, b, t, digit(X.sub(a, b), b, t))

def div_q(+s: Bool, +e: Nat, +a: W.U64, +b: W.U64) -> F64:
  div_qt(s, e, a, b, X.bitlen(X.hi(b)))

def div_ab(+s: Bool, +ea: Nat, +a: W.U64, +eb: Nat, +b: W.U64, less: Bool) -> F64:
  match less:
    case True{}:
      div_q(s, Nat.sub(Nat.add(ea, Nat.add(off(), 1021n)), eb), X.add(a, a), b)
    case False{}:
      div_q(s, Nat.sub(Nat.add(ea, Nat.add(off(), 1022n)), eb), a, b)

def div_n(+s: Bool, +ea: Nat, +a: W.U64, +eb: Nat, +b: W.U64) -> F64:
  div_ab(s, ea, a, eb, b, X.lt(a, b))

def div_za(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, za: Bool) -> F64:
  match za:
    case True{}:
      zero(s)
    case False{}:
      div_n(s, norm_e(ea, fa), norm_f(ea, fa), norm_e(eb, fb), norm_f(eb, fb))

def div_z(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, zb: Bool) -> F64:
  match zb:
    case True{}:
      inf_or_nan(s, fin_zero(ea, fa))
    case False{}:
      div_za(s, ea, fa, eb, fb, fin_zero(ea, fa))

def div_b(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(zero(s), nz(fb))
    case False{}:
      div_z(s, ea, fa, eb, fb, fin_zero(eb, fb))

def div_cls(+s: Bool, +ea: Nat, +fa: W.U64, +eb: Nat, +fb: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      inf_or_nan(s, Bool.or(nz(fa), Nat.is_eq(eb, 2047n)))
    case False{}:
      div_b(s, ea, fa, eb, fb, Nat.is_eq(eb, 2047n))

def div(+x: F64, +y: F64) -> F64:
  div_cls(Bool.xor(signbit(x), signbit(y)), exp_field(x), frac(x), exp_field(y), frac(y), Nat.is_eq(exp_field(x), 2047n))

# ---- square root ----

def sq_fin(+e: Nat, +t: W.U64, sticky: Bool) -> F64:
  round_pack(False{}, e, X.or_bit(t, sticky))

# the root is S0 - 2: remainder (2 S0 - 3) - (D - (2 S0 - 1)) with c = 2 S0 - 1
def sq_d2(+e: Nat, +s0: W.U64, +d: W.U64, +c: W.U64) -> F64:
  sq_fin(e, X.sub(s0, W.U64{2, 0}), Bool.not(X.eq(X.sub(c, W.U64{2, 0}), X.sub(d, c))))

# S0^2 - N = D > 0: the root is S0 - 1 when D <= 2 S0 - 1 (remainder c - D)
def sq_d1(+e: Nat, +s0: W.U64, +d: W.U64, +c: W.U64, small: Bool) -> F64:
  match small:
    case True{}:
      sq_fin(e, X.sub(s0, W.U64{1, 0}), Bool.not(X.eq(c, d)))
    case False{}:
      sq_d2(e, s0, d, c)

def sq_neg(+e: Nat, +s0: W.U64, +d: W.U64) -> F64:
  sq_d1(e, s0, d, X.sub(X.add(s0, s0), W.U64{1, 0}), X.le(d, X.sub(X.add(s0, s0), W.U64{1, 0})))

# N - S0^2 = a - b for a = u 2^32, b = q^2: the root is S0 when b <= a
def sq_rem(+e: Nat, +s0: W.U64, +a: W.U64, +b: W.U64, ge: Bool) -> F64:
  match ge:
    case True{}:
      sq_fin(e, s0, Bool.not(X.eq(a, b)))
    case False{}:
      sq_neg(e, s0, X.sub(b, a))

def sq_qu(+e: Nat, +s: U32, +q: U32, +u: U32) -> F64:
  sq_rem(e, W.U64{q, s}, W.U64{0, u}, X.mul32(q, q), X.le(X.mul32(q, q), W.U64{0, u}))

# q = 2^32 (r = 2 s) is taken as q = 2^32 - 1 with u = 2 s
def sq_clamp(+e: Nat, +s: U32, +q: W.U64, +u: U32, small: Bool) -> F64:
  match small:
    case True{}:
      sq_qu(e, s, X.lo(q), u)
    case False{}:
      sq_qu(e, s, 4294967295, U32.add(s, s))

def sq_div(+e: Nat, +s: U32, p: W.U64 & U32) -> F64:
  (+q, +u) = p
  sq_clamp(e, s, q, u, U32.is_zero(X.hi(q)))

# one step of Zimmermann's SqrtRem (Karatsuba square root) from s = isqrt(nh):
# r = nh - s^2, (q, u) = divmod(r 2^32, 2 s) give S0 = s 2^32 + q with
# N - S0^2 = u 2^32 - q^2 for N = nh 2^64; S0 - 2 <= isqrt(N) <= S0 and the
# exact remainder decides the root and its sticky bit without squaring S0
def sq_root_s(+e: Nat, +nh: W.U64, +s: U32) -> F64:
  sq_div(e, s, X.div32(W.U64{0, X.lo(X.sub(nh, X.mul32(s, s)))}, U32.add(s, s)))

def sq_root(+e: Nat, +nh: W.U64) -> F64:
  sq_root_s(e, nh, X.lo(X.isqrt(nh)))

# m * 2^(E - OFF - 1075) with the unbiased exponent made even (E odd); the
# root of m * 2^72 has its top bit at 62
def sq_even(+e: Nat, +m: W.U64) -> F64:
  sq_root(Nat.add(Nat.div(Nat.sub(Nat.add(e, off()), 1075n), 2n), 1048n), X.shl(m, 8n))

def sq_n(+e: Nat, +m: W.U64, odd: Bool) -> F64:
  match odd:
    case True{}:
      sq_even(e, m)
    case False{}:
      sq_even(Nat.sub(e, 1n), X.add(m, m))

def sq_pos(+e: Nat, +f: W.U64, negative: Bool) -> F64:
  match negative:
    case True{}:
      nan()
    case False{}:
      sq_n(norm_e(e, f), norm_f(e, f), Nat.is_eq(Nat.mod(norm_e(e, f), 2n), 1n))

def sq_sign(+x: F64, negative: Bool, +e: Nat, +f: W.U64, zr: Bool) -> F64:
  match zr:
    case True{}:
      x
    case False{}:
      sq_pos(e, f, negative)

def sq_cls(+x: F64, s: Bool, +e: Nat, +f: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(x, Bool.or(nz(f), s))
    case False{}:
      sq_sign(x, s, e, f, fin_zero(e, f))

def sqrt(+x: F64) -> F64:
  sq_cls(x, signbit(x), exp_field(x), frac(x), Nat.is_eq(exp_field(x), 2047n))

# ---- comparison and conversion ----

def lt_s(+x: F64, +y: F64, sa: Bool, sb: Bool) -> Bool:
  match sa sb:
    case True{} False{}:
      True{}
    case False{} True{}:
      False{}
    case False{} False{}:
      X.lt(mag(x), mag(y))
    case True{} True{}:
      X.lt(mag(y), mag(x))

def le_s(+x: F64, +y: F64, sa: Bool, sb: Bool) -> Bool:
  match sa sb:
    case True{} False{}:
      True{}
    case False{} True{}:
      False{}
    case False{} False{}:
      X.le(mag(x), mag(y))
    case True{} True{}:
      X.le(mag(y), mag(x))

def unordered(+x: F64, +y: F64) -> Bool:
  Bool.or(is_nan(x), is_nan(y))

def zeros(+x: F64, +y: F64) -> Bool:
  Bool.and(is_zero(x), is_zero(y))

def lt_z(+x: F64, +y: F64, bad: Bool, z: Bool) -> Bool:
  match bad z:
    case True{} _:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      lt_s(x, y, signbit(x), signbit(y))

def lt(+x: F64, +y: F64) -> Bool:
  lt_z(x, y, unordered(x, y), zeros(x, y))

def le_z(+x: F64, +y: F64, bad: Bool, z: Bool) -> Bool:
  match bad z:
    case True{} _:
      False{}
    case False{} True{}:
      True{}
    case False{} False{}:
      le_s(x, y, signbit(x), signbit(y))

def le(+x: F64, +y: F64) -> Bool:
  le_z(x, y, unordered(x, y), zeros(x, y))

def eq_z(+x: F64, +y: F64, bad: Bool, z: Bool) -> Bool:
  match bad z:
    case True{} _:
      False{}
    case False{} True{}:
      True{}
    case False{} False{}:
      Bool.and(U32.is_eq(word_lo(x), word_lo(y)), U32.is_eq(word_hi(x), word_hi(y)))

def eq(+x: F64, +y: F64) -> Bool:
  eq_z(x, y, unordered(x, y), zeros(x, y))

# n mod 2^k and n div 2^k by k halvings (no 2^32 constant: the proof
# checker would expand it in unary)
def low_bits(k: Nat, +n: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(Nat.mod(n, 2n), Nat.double(low_bits(p, Nat.div(n, 2n))))

def high_bits(k: Nat, +n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+p:
      high_bits(p, Nat.div(n, 2n))

# the jam of n >> d (the bits shifted out OR-ed into bit 0)
def jam_nat(+d: Nat, +n: Nat) -> Nat:
  Nat.add(Nat.mul(2n, Nat.div(high_bits(d, n), 2n)), Nat.max(Nat.mod(high_bits(d, n), 2n), Nat.min(low_bits(d, n), 1n)))

def word64(+s: Nat) -> W.U64:
  W.U64{U32.from_nat(low_bits(32n, s)), U32.from_nat(high_bits(32n, s))}

# n with its top bit moved to bit 62 (b = bit_length(n)): shifted up when
# b <= 63 (every runtime Nat), jammed down otherwise
def sig63(+n: Nat, +b: Nat, fits: Bool) -> W.U64:
  match fits:
    case True{}:
      X.shl(word64(n), Nat.sub(63n, b))
    case False{}:
      word64(jam_nat(Nat.sub(b, 63n), n))

def of_nat_z(+n: Nat, z: Bool) -> F64:
  match z:
    case True{}:
      zero(False{})
    case False{}:
      round_pack(False{}, Nat.add(5117n, M.bit_length(n)), sig63(n, M.bit_length(n), Nat.is_le(M.bit_length(n), 63n)))

# the double nearest to n (exact below 2^53)
def of_nat(+n: Nat) -> F64:
  of_nat_z(n, Nat.is_eq(n, 0n))

# 2^k for k <= 1023
def pow2(+k: Nat) -> F64:
  pack(False{}, Nat.add(1022n, k), W.U64{0, 1048576})

# ---- decoding and exact rounding (the tools of everything below) ----

# the significand with its hidden bit (bit 52 of a normal number) and the
# scale of its unit, the exponent plus Z = 3000 (1926 for subnormals), as in
# spec/math/f64.bend's mant and xexp
def dmant_z(+f: W.U64, z: Bool) -> W.U64:
  match z:
    case True{}:
      f
    case False{}:
      X.add(f, W.U64{0, 1048576})

def dmant(+x: F64) -> W.U64:
  dmant_z(frac(x), Nat.is_eq(exp_field(x), 0n))

def dexp_z(+e: Nat, z: Bool) -> Nat:
  match z:
    case True{}:
      1926n
    case False{}:
      Nat.add(e, 1925n)

def dexp(+x: F64) -> Nat:
  dexp_z(exp_field(x), Nat.is_eq(exp_field(x), 0n))

def rw_top(+s: Bool, +x: Nat, +w: W.U64, top: Bool) -> F64:
  match top:
    case True{}:
      norm_round_pack(s, Nat.add(x, 2181n), X.shr_jam(w, 1n))
    case False{}:
      norm_round_pack(s, Nat.add(x, 2180n), w)

def rw_z(+s: Bool, +x: Nat, +w: W.U64, z: Bool) -> F64:
  match z:
    case True{}:
      zero(s)
    case False{}:
      rw_top(s, x, w, X.le(W.U64{0, 2147483648}, w))

# the double nearest to (-1)^s * w * 2^(x - 3000), for x >= 63: every exact
# result below is an integer of at most 64 bits at a scale, rounded once
def round_w(+s: Bool, +x: Nat, +w: W.U64) -> F64:
  rw_z(s, x, w, X.is_zero(w))

# ---- rounding to an integral value (IEEE roundToIntegral) ----

type RMode is Data:
  Trunc{}
  Floor{}
  Ceil{}
  Even{}

def b64(b: Bool) -> W.U64:
  match b:
    case True{}:
      W.U64{1, 0}
    case False{}:
      W.U64{0, 0}

# whether the integer part q (remainder r, half h of the unit) moves up one
def ri_up(m: RMode, +s: Bool, +q: W.U64, +r: W.U64, +h: W.U64) -> Bool:
  match m:
    case Trunc{}:
      False{}
    case Floor{}:
      Bool.and(s, Bool.not(X.is_zero(r)))
    case Ceil{}:
      Bool.and(Bool.not(s), Bool.not(X.is_zero(r)))
    case Even{}:
      Bool.or(X.lt(h, r), Bool.and(X.eq(r, h), X.odd(q)))

def ri_q(m: RMode, +s: Bool, +q: W.U64, +r: W.U64, +h: W.U64) -> F64:
  round_w(s, 3000n, X.add(q, b64(ri_up(m, s, q, r, h))))

# k < 64 fractional bits: q = w >> k, r = w - (q << k), h = 2^(k-1)
def ri_k(m: RMode, +s: Bool, +w: W.U64, +k: Nat, small: Bool) -> F64:
  match small:
    case True{}:
      ri_q(m, s, X.shr(w, k), X.sub(w, X.shl(X.shr(w, k), k)), X.shl(W.U64{1, 0}, Nat.sub(k, 1n)))
    case False{}:
      ri_q(m, s, W.U64{0, 0}, w, W.U64{0, 2147483648})

def ri_fin(m: RMode, +x: F64, int: Bool) -> F64:
  match int:
    case True{}:
      x
    case False{}:
      ri_k(m, signbit(x), dmant(x), Nat.sub(3000n, dexp(x)), Nat.is_lt(Nat.sub(3000n, dexp(x)), 64n))

def ri_cls(m: RMode, +x: F64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(x, nz(frac(x)))
    case False{}:
      ri_fin(m, x, Nat.is_le(3000n, dexp(x)))

def to_integral(m: RMode, +x: F64) -> F64:
  ri_cls(m, x, Nat.is_eq(exp_field(x), 2047n))

def trunc(+x: F64) -> F64:
  to_integral(Trunc{}, x)

def floor(+x: F64) -> F64:
  to_integral(Floor{}, x)

def ceil(+x: F64) -> F64:
  to_integral(Ceil{}, x)

# ties to even (Python's round(x) and C's rint)
def round(+x: F64) -> F64:
  to_integral(Even{}, x)

# ---- conversions to and from unsigned integers ----

def tu_neg(+w: W.U64, bad: Bool) -> Result<&2, &2, N.NumError, W.U64>:
  match bad:
    case True{}:
      Fail{N.Overflow{}}
    case False{}:
      Done{w}

def tu_int(+s: Bool, +w: W.U64) -> Result<&2, &2, N.NumError, W.U64>:
  tu_neg(w, Bool.and(s, Bool.not(X.is_zero(w))))

# |x| >= 2^52: w << k with k + bit_length(w) <= 64
def tu_big(+s: Bool, +w: W.U64, +k: Nat, fits: Bool) -> Result<&2, &2, N.NumError, W.U64>:
  match fits:
    case True{}:
      tu_int(s, X.shl(w, k))
    case False{}:
      Fail{N.Overflow{}}

def tu_fin(+x: F64, big: Bool) -> Result<&2, &2, N.NumError, W.U64>:
  match big:
    case True{}:
      tu_big(signbit(x), dmant(x), Nat.sub(dexp(x), 3000n), Nat.is_le(Nat.add(Nat.sub(dexp(x), 3000n), Nat.sub(64n, X.clz(dmant(x)))), 64n))
    case False{}:
      tu_int(signbit(x), X.shr(dmant(x), Nat.sub(3000n, dexp(x))))

def tu_top(isn: Bool) -> Result<&2, &2, N.NumError, W.U64>:
  match isn:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Fail{N.Overflow{}}

def tu_cls(+x: F64, top: Bool) -> Result<&2, &2, N.NumError, W.U64>:
  match top:
    case True{}:
      tu_top(nz(frac(x)))
    case False{}:
      tu_fin(x, Nat.is_le(3000n, dexp(x)))

# x truncated toward zero as an unsigned 64-bit integer: NaN is a domain
# error, a value outside [0, 2^64) (infinities included) an overflow
def to_u64(+x: F64) -> Result<&2, &2, N.NumError, W.U64>:
  tu_cls(x, Nat.is_eq(exp_field(x), 2047n))

def tu32_w(+w: W.U64, fits: Bool) -> Result<&2, &2, N.NumError, U32>:
  match fits:
    case True{}:
      Done{X.lo(w)}
    case False{}:
      Fail{N.Overflow{}}

def tu32(r: Result<&2, &2, N.NumError, W.U64>) -> Result<&2, &2, N.NumError, U32>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+w}:
      tu32_w(w, U32.is_zero(X.hi(w)))

def to_u32(+x: F64) -> Result<&2, &2, N.NumError, U32>:
  tu32(to_u64(x))

def floor_u64(+x: F64) -> Result<&2, &2, N.NumError, W.U64>:
  to_u64(floor(x))

def ceil_u64(+x: F64) -> Result<&2, &2, N.NumError, W.U64>:
  to_u64(ceil(x))

def round_u64(+x: F64) -> Result<&2, &2, N.NumError, W.U64>:
  to_u64(round(x))

# the double nearest to an unsigned 64-bit integer (exact below 2^53)
def of_u64(+w: W.U64) -> F64:
  round_w(False{}, 3000n, w)

def of_u32(+u: U32) -> F64:
  of_u64(W.U64{u, 0})

# ---- exponents: frexp, ldexp, ulp ----

# a signed exponent: -mag when neg
type Exp is Data:
  Exp{neg: Bool, mag: Nat}

def exp_pick(+t: Nat, pos: Bool) -> Exp:
  match pos:
    case True{}:
      Exp{False{}, Nat.sub(t, 3000n)}
    case False{}:
      Exp{True{}, Nat.sub(3000n, t)}

# t - 3000 as a signed exponent
def exp_of(+t: Nat) -> Exp:
  exp_pick(t, Nat.is_le(3000n, t))

def fx_fin(+x: F64, +w: W.U64, +b: Nat) -> F64 & Exp:
  (round_w(signbit(x), Nat.sub(3000n, b), w), exp_of(Nat.add(dexp(x), b)))

def fx_z(+x: F64, z: Bool) -> F64 & Exp:
  match z:
    case True{}:
      (x, Exp{False{}, 0n})
    case False{}:
      fx_fin(x, dmant(x), Nat.sub(64n, X.clz(dmant(x))))

def fx_cls(+x: F64, top: Bool) -> F64 & Exp:
  match top:
    case True{}:
      (nan_or(x, nz(frac(x))), Exp{False{}, 0n})
    case False{}:
      fx_z(x, is_zero(x))

# (m, e) with x = m * 2^e and 0.5 <= |m| < 1; zeros and infinities give (x, 0)
def frexp(+x: F64) -> F64 & Exp:
  fx_cls(x, Nat.is_eq(exp_field(x), 2047n))

def ld_neg(+x: F64, +k: Nat, tiny: Bool) -> F64:
  match tiny:
    case True{}:
      zero(signbit(x))
    case False{}:
      round_w(signbit(x), Nat.sub(dexp(x), k), dmant(x))

def ld_fin(+x: F64, +neg: Bool, +k: Nat) -> F64:
  match neg:
    case True{}:
      ld_neg(x, k, Nat.is_lt(dexp(x), Nat.add(k, 63n)))
    case False{}:
      round_w(signbit(x), Nat.add(dexp(x), k), dmant(x))

def ld_e(+x: F64, +e: Exp) -> F64:
  match e:
    case Exp{+neg, +k}:
      ld_fin(x, neg, k)

def ld_z(+x: F64, +e: Exp, z: Bool) -> F64:
  match z:
    case True{}:
      x
    case False{}:
      ld_e(x, e)

def ld_cls(+x: F64, +e: Exp, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(x, nz(frac(x)))
    case False{}:
      ld_z(x, e, is_zero(x))

# x * 2^e, rounded once (overflow to infinity, gradual underflow)
def ldexp(+x: F64, +e: Exp) -> F64:
  ld_cls(x, e, Nat.is_eq(exp_field(x), 2047n))

def ulp_cls(+x: F64, top: Bool) -> F64:
  match top:
    case True{}:
      nan_or(inf(False{}), nz(frac(x)))
    case False{}:
      round_w(False{}, dexp(x), W.U64{1, 0})

# the value of the least significant bit of x (Python's math.ulp)
def ulp(+x: F64) -> F64:
  ulp_cls(x, Nat.is_eq(exp_field(x), 2047n))

# ---- neighbours and NaN-ignoring extrema ----

def with_sign(+s: Bool, +w: W.U64) -> F64:
  Bits{X.lo(w), U32.add(X.hi(w), sgn(s))}

def na_step(+x: F64, up: Bool) -> F64:
  match up:
    case True{}:
      with_sign(signbit(x), X.add(mag(x), W.U64{1, 0}))
    case False{}:
      with_sign(signbit(x), X.sub(mag(x), W.U64{1, 0}))

def na_z(+x: F64, +y: F64, z: Bool) -> F64:
  match z:
    case True{}:
      Bits{1, sgn(signbit(y))}
    case False{}:
      na_step(x, Bool.xor(lt(x, y), signbit(x)))

def na_eq(+x: F64, +y: F64, same: Bool) -> F64:
  match same:
    case True{}:
      y
    case False{}:
      na_z(x, y, is_zero(x))

def na_nan(+x: F64, +y: F64, bad: Bool) -> F64:
  match bad:
    case True{}:
      nan()
    case False{}:
      na_eq(x, y, eq(x, y))

# the next double after x toward y (IEEE nextAfter; y when x == y)
def nextafter(+x: F64, +y: F64) -> F64:
  na_nan(x, y, unordered(x, y))

def fpick(+x: F64, +y: F64, first: Bool) -> F64:
  match first:
    case True{}:
      x
    case False{}:
      y

def fmin_z(+x: F64, +y: F64, z: Bool) -> F64:
  match z:
    case True{}:
      zero(Bool.or(signbit(x), signbit(y)))
    case False{}:
      fpick(x, y, lt(x, y))

def fmin_ny(+x: F64, +y: F64, ny: Bool) -> F64:
  match ny:
    case True{}:
      x
    case False{}:
      fmin_z(x, y, zeros(x, y))

def fmin_nx(+x: F64, +y: F64, nx: Bool) -> F64:
  match nx:
    case True{}:
      nan_or(y, is_nan(y))
    case False{}:
      fmin_ny(x, y, is_nan(y))

# IEEE 754-2019 minimumNumber: a NaN operand is ignored, -0 < +0
def fmin(+x: F64, +y: F64) -> F64:
  fmin_nx(x, y, is_nan(x))

def fmax_z(+x: F64, +y: F64, z: Bool) -> F64:
  match z:
    case True{}:
      zero(Bool.and(signbit(x), signbit(y)))
    case False{}:
      fpick(x, y, lt(y, x))

def fmax_ny(+x: F64, +y: F64, ny: Bool) -> F64:
  match ny:
    case True{}:
      x
    case False{}:
      fmax_z(x, y, zeros(x, y))

def fmax_nx(+x: F64, +y: F64, nx: Bool) -> F64:
  match nx:
    case True{}:
      nan_or(y, is_nan(y))
    case False{}:
      fmax_ny(x, y, is_nan(y))

# IEEE 754-2019 maximumNumber
def fmax(+x: F64, +y: F64) -> F64:
  fmax_nx(x, y, is_nan(x))

# ---- classification, bit casts, integrality ----

def is_normal(+x: F64) -> Bool:
  Bool.and(Bool.not(Nat.is_eq(exp_field(x), 0n)), Nat.is_lt(exp_field(x), 2047n))

def is_subnormal(+x: F64) -> Bool:
  Bool.and(Nat.is_eq(exp_field(x), 0n), nz(frac(x)))

def to_bits(+x: F64) -> W.U64:
  W.U64{word_lo(x), word_hi(x)}

def of_bits64(+w: W.U64) -> F64:
  Bits{X.lo(w), X.hi(w)}

def ii_k(+w: W.U64, +k: Nat, small: Bool) -> Bool:
  match small:
    case True{}:
      X.eq(X.shl(X.shr(w, k), k), w)
    case False{}:
      X.is_zero(w)

def ii_fin(+x: F64, int: Bool) -> Bool:
  match int:
    case True{}:
      True{}
    case False{}:
      ii_k(dmant(x), Nat.sub(3000n, dexp(x)), Nat.is_lt(Nat.sub(3000n, dexp(x)), 64n))

# finite with no fractional bits
def is_integer(+x: F64) -> Bool:
  Bool.and(is_finite(x), ii_fin(x, Nat.is_le(3000n, dexp(x))))

# ---- the fractional part and the exact remainders ----

def mf_frac(+s: Bool, +w: W.U64, +u: Nat, +k: Nat, small: Bool) -> F64:
  match small:
    case True{}:
      round_w(s, u, X.sub(w, X.shl(X.shr(w, k), k)))
    case False{}:
      round_w(s, u, w)

def mf_fin(+x: F64, int: Bool) -> F64 & F64:
  match int:
    case True{}:
      (zero(signbit(x)), x)
    case False{}:
      (mf_frac(signbit(x), dmant(x), dexp(x), Nat.sub(3000n, dexp(x)), Nat.is_lt(Nat.sub(3000n, dexp(x)), 64n)), trunc(x))

def mf_cls(+x: F64, top: Bool) -> F64 & F64:
  match top:
    case True{}:
      (nan_or(zero(signbit(x)), nz(frac(x))), nan_or(x, nz(frac(x))))
    case False{}:
      mf_fin(x, Nat.is_le(3000n, dexp(x)))

# (fractional part, integral part), both with the sign of x (Python's modf)
def modf(+x: F64) -> F64 & F64:
  mf_cls(x, Nat.is_eq(exp_field(x), 2047n))

# (q, r) of mx * 2^d by b from (q0, r0) of mx by b: ten bits a step, so each
# partial remainder r * 2^t stays below 2^63
def fm_go(fuel: Nat, +b: W.U64, +d: Nat, st: W.U64 & W.U64) -> W.U64 & W.U64:
  match fuel d:
    case 0n _:
      st
    case 1n+f 0n:
      st
    case 1n+f 1n+e:
      fm_go(f, b, Nat.sub(1n+e, Nat.min(1n+e, 10n)), X.divmod(X.shl(X.psnd(st), Nat.min(1n+e, 10n)), b))

# the last quotient digit and remainder of mant(x) * 2^(e(x) - e(y)) by mant(y)
def fm_qr(+x: F64, +y: F64) -> W.U64 & W.U64:
  fm_go(Nat.sub(dexp(x), dexp(y)), dmant(y), Nat.sub(dexp(x), dexp(y)), X.divmod(dmant(x), dmant(y)))

def fmod_fin(+x: F64, +y: F64, far: Bool) -> F64:
  match far:
    case True{}:
      x
    case False{}:
      round_w(signbit(x), dexp(y), X.psnd(fm_qr(x, y)))

def fmod_z(+x: F64, +y: F64, zx: Bool) -> F64:
  match zx:
    case True{}:
      x
    case False{}:
      fmod_fin(x, y, Nat.is_lt(dexp(x), dexp(y)))

def fmod_yi(+x: F64, +y: F64, yi: Bool) -> F64:
  match yi:
    case True{}:
      x
    case False{}:
      fmod_z(x, y, is_zero(x))

def fmod_bad(+x: F64, +y: F64, bad: Bool) -> F64:
  match bad:
    case True{}:
      nan()
    case False{}:
      fmod_yi(x, y, is_inf(y))

# x - n y for n = trunc(x / y), exact, with the sign of x (C's fmod)
def fmod(+x: F64, +y: F64) -> F64:
  fmod_bad(x, y, Bool.or(Bool.or(unordered(x, y), is_inf(x)), is_zero(y)))

def rm_pick(+s: Bool, +u: Nat, +b: W.U64, +r: W.U64, flip: Bool) -> F64:
  match flip:
    case True{}:
      round_w(Bool.not(s), u, X.sub(b, r))
    case False{}:
      round_w(s, u, r)

# remainder r of divisor b at scale u, last quotient digit q: round the
# quotient to nearest (ties to even) by flipping to r - b
def rm_fix(+s: Bool, +u: Nat, +b: W.U64, +r: W.U64, +q: W.U64) -> F64:
  rm_pick(s, u, b, r, Bool.or(X.lt(b, X.add(r, r)), Bool.and(X.eq(X.add(r, r), b), X.odd(q))))

def rm_qr(+x: F64, +y: F64, p: W.U64 & W.U64) -> F64:
  (+q, +r) = p
  rm_fix(signbit(x), dexp(y), dmant(y), r, q)

def rm_near(+x: F64, +y: F64, one: Bool) -> F64:
  match one:
    case True{}:
      rm_fix(signbit(x), dexp(x), X.add(dmant(y), dmant(y)), dmant(x), W.U64{0, 0})
    case False{}:
      x

def rm_far(+x: F64, +y: F64, far: Bool) -> F64:
  match far:
    case True{}:
      rm_near(x, y, Nat.is_eq(Nat.sub(dexp(y), dexp(x)), 1n))
    case False{}:
      rm_qr(x, y, fm_qr(x, y))

def rm_z(+x: F64, +y: F64, zx: Bool) -> F64:
  match zx:
    case True{}:
      x
    case False{}:
      rm_far(x, y, Nat.is_lt(dexp(x), dexp(y)))

def rm_yi(+x: F64, +y: F64, yi: Bool) -> F64:
  match yi:
    case True{}:
      x
    case False{}:
      rm_z(x, y, is_zero(x))

def rm_bad(+x: F64, +y: F64, bad: Bool) -> F64:
  match bad:
    case True{}:
      nan()
    case False{}:
      rm_yi(x, y, is_inf(y))

# IEEE remainder: x - n y for n = x / y rounded to nearest, ties to even
def remainder(+x: F64, +y: F64) -> F64:
  rm_bad(x, y, Bool.or(Bool.or(unordered(x, y), is_inf(x)), is_zero(y)))

# ---- closeness and exact ratios ----

def ic_d(+a: F64, +b: F64, +rel: F64, +at: F64, +d: F64) -> Bool:
  Bool.or(Bool.or(le(d, abs(mul(rel, b))), le(d, abs(mul(rel, a)))), le(d, at))

def ic_inf(+a: F64, +b: F64, +rel: F64, +at: F64, big: Bool) -> Bool:
  match big:
    case True{}:
      False{}
    case False{}:
      ic_d(a, b, rel, at, abs(sub(b, a)))

def ic_eq(+a: F64, +b: F64, +rel: F64, +at: F64, same: Bool) -> Bool:
  match same:
    case True{}:
      True{}
    case False{}:
      ic_inf(a, b, rel, at, Bool.or(is_inf(a), is_inf(b)))

def ic_tol(+a: F64, +b: F64, +rel: F64, +at: F64, bad: Bool) -> Result<&2, &2, N.NumError, Bool>:
  match bad:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Done{ic_eq(a, b, rel, at, eq(a, b))}

# Python's math.isclose (CPython's algorithm): a negative tolerance is a
# domain error
def isclose(+a: F64, +b: F64, +rel: F64, +at: F64) -> Result<&2, &2, N.NumError, Bool>:
  ic_tol(a, b, rel, at, Bool.or(lt(rel, zero(False{})), lt(at, zero(False{}))))

# +-num / 2^den in lowest terms (num odd or den = 0)
type Ratio is Data:
  Ratio{neg: Bool, num: W.U64, den: Nat}

# trailing zeros of w (at most fuel), one halving at a time
def ctz_go(fuel: Nat, +w: W.U64, odd: Bool) -> Nat:
  match fuel odd:
    case 0n _:
      0n
    case 1n+f True{}:
      0n
    case 1n+f False{}:
      1n+ctz_go(f, X.half(w), X.odd(X.half(w)))

def ctz(+w: W.U64) -> Nat:
  ctz_go(64n, w, X.odd(w))

def ar_small(+s: Bool, +w: W.U64, +k: Nat, +j: Nat) -> Result<&2, &2, N.NumError, Ratio>:
  Done{Ratio{s, X.shr(w, j), Nat.sub(k, j)}}

def ar_big(+s: Bool, +w: W.U64, +k: Nat, fits: Bool) -> Result<&2, &2, N.NumError, Ratio>:
  match fits:
    case True{}:
      Done{Ratio{s, X.shl(w, k), 0n}}
    case False{}:
      Fail{N.Overflow{}}

def ar_fin(+x: F64, big: Bool) -> Result<&2, &2, N.NumError, Ratio>:
  match big:
    case True{}:
      ar_big(signbit(x), dmant(x), Nat.sub(dexp(x), 3000n), Nat.is_le(Nat.add(Nat.sub(dexp(x), 3000n), Nat.sub(64n, X.clz(dmant(x)))), 64n))
    case False{}:
      ar_small(signbit(x), dmant(x), Nat.sub(3000n, dexp(x)), Nat.min(ctz(dmant(x)), Nat.sub(3000n, dexp(x))))

def ar_z(+x: F64, z: Bool) -> Result<&2, &2, N.NumError, Ratio>:
  match z:
    case True{}:
      Done{Ratio{False{}, W.U64{0, 0}, 0n}}
    case False{}:
      ar_fin(x, Nat.is_le(3000n, dexp(x)))

def ar_top(isn: Bool) -> Result<&2, &2, N.NumError, Ratio>:
  match isn:
    case True{}:
      Fail{N.BadDomain{}}
    case False{}:
      Fail{N.Overflow{}}

def ar_cls(+x: F64, top: Bool) -> Result<&2, &2, N.NumError, Ratio>:
  match top:
    case True{}:
      ar_top(nz(frac(x)))
    case False{}:
      ar_z(x, is_zero(x))

# x = +-num / 2^den exactly, in lowest terms (Python's as_integer_ratio with
# the denominator's exponent); NaN is a domain error, infinities and integers
# of 2^64 or more overflow
def as_integer_ratio(+x: F64) -> Result<&2, &2, N.NumError, Ratio>:
  ar_cls(x, Nat.is_eq(exp_field(x), 2047n))

# ---- the num.bend instance ----

def f64_op(o: N.Op<F64>) -> F64:
  match o:
    case N.ZeroOp{}:
      zero(False{})
    case N.One{}:
      one()
    case N.Add{a, b}:
      add(a, b)
    case N.Sub{a, b}:
      sub(a, b)
    case N.Mul{a, b}:
      mul(a, b)
    case N.Neg{a}:
      neg(a)
    case N.Abs{a}:
      abs(a)
    case N.Quot{a, b}:
      div(a, b)
    case N.Rem{a, b}:
      nan()
    case N.Half{a}:
      mul(a, Bits{0, 1071644672})
    case N.MulMod{a, b, m}:
      nan()
    case N.Pow2{k}:
      pow2(k)
    case N.Sqrt{a}:
      sqrt(a)
    case N.PowMod{a, e, m}:
      nan()
    case N.GcdSmall{a, b}:
      nan()

def f64_is(t: N.Test<F64>) -> Bool:
  match t:
    case N.Lt{a, b}:
      lt(a, b)
    case N.AddOver{a, b}:
      False{}
    case N.MulOver{a, b}:
      False{}
    case N.Odd{a}:
      False{}
    case N.IsZero{a}:
      is_zero(a)
    case N.FastDiv{}:
      True{}
    case N.Mont{m}:
      False{}
    case N.Small{a, b}:
      False{}
