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
# the square root an integer square root with one Newton step, each followed
# by a sticky bit, so every result is correctly rounded: subnormals, overflow
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
def div_q(+s: Bool, +e: Nat, +a: W.U64, +b: W.U64) -> F64:
  dq_mid(s, e, b, X.bitlen(X.hi(b)), digit(X.sub(a, b), b, X.bitlen(X.hi(b))))

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

# r * r > n * 2^64
def sq_over(+nh: W.U64, p: W.U64 & W.U64) -> Bool:
  (+pl, +ph) = p
  Bool.or(X.lt(nh, ph), Bool.and(X.eq(nh, ph), nz(pl)))

def sq_exact(+nh: W.U64, p: W.U64 & W.U64) -> Bool:
  (+pl, +ph) = p
  Bool.and(X.eq(nh, ph), X.is_zero(pl))

def sq_down(fuel: Nat, +nh: W.U64, +r: W.U64, over: Bool) -> W.U64:
  match fuel over:
    case 0n _:
      r
    case 1n+f False{}:
      r
    case 1n+f True{}:
      sq_down(f, nh, X.sub(r, W.U64{1, 0}), sq_over(nh, X.mul128(X.sub(r, W.U64{1, 0}), X.sub(r, W.U64{1, 0}))))

def sq_newton2(+nh: W.U64, +r0: W.U64, +d1: U32, p: U32 & W.U64) -> W.U64:
  (+d2, +r2) = p
  X.half(X.add(r0, W.U64{d2, d1}))

def sq_newton1(+nh: W.U64, +r0: W.U64, +t: Nat, p: U32 & W.U64) -> W.U64:
  (+d1, +r1) = p
  sq_newton2(nh, r0, d1, digit(r1, r0, t))

def sq_r1(+nh: W.U64, +r1: W.U64) -> W.U64:
  sq_down(6n, nh, r1, sq_over(nh, X.mul128(r1, r1)))

# floor(sqrt(nh * 2^64)) for 2^60 <= nh < 2^62: r0 = (isqrt(nh) + 1) * 2^32 is
# at or above it and within 2^32, so one Newton step (r0 + N / r0) / 2 lands
# within 2 above it, and a few steps down finish
def isqrt128(+nh: W.U64, +r0: W.U64) -> W.U64:
  sq_r1(nh, sq_newton1(nh, r0, X.bitlen(X.hi(r0)), digit(nh, r0, X.bitlen(X.hi(r0)))))

def sq_fin(+e: Nat, +nh: W.U64, +r: W.U64) -> F64:
  round_pack(False{}, e, X.or_bit(r, Bool.not(sq_exact(nh, X.mul128(r, r)))))

def sq_root(+e: Nat, +nh: W.U64) -> F64:
  sq_fin(e, nh, isqrt128(nh, W.U64{0, U32.add(X.lo(X.isqrt(nh)), 1)}))

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
