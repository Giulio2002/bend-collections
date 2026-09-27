import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./u64laws.bend as UL
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64tools.bend as T
import ./f64rint.bend as RI

# modf (python_style_math_stdlib_design.pdf 4.3; C99 7.12.6.12 and
# F.9.3.12): Modf.value. The fractional part of m 2^-k is low(k, m) at the
# same scale, taken as m - ((m >> k) << k) (Shr, Shl, Sub values) and
# rounded once (exact: it has at most 53 bits); the integral part is trunc
# (f64rint.trunc_value).

# the low k bits of a word, k < 64
def rem_v(+w: WU.U64, +k: Nat, +hb: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {SW.value(X.sub(w, X.shl(X.shr(w, k), k))) == C.low(k, SW.value(w)) : Nat}:
  +V = SW.value(w)
  +q = X.shr(w, k)
  +sq = X.shl(q, k)
  +Hq = C.high(k, V)
  +Lq = C.low(k, V)
  +S = C.shift(k, Hq)
  +hSV0 = L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(S, Lq), Nat.add(Lq, S), NA.add_comm(S, Lq), N.le_add_right(S, Lq))
  +hSV = L.subst(Nat, t => {Nat.is_le(S, t) == True{} : Bool}, Nat.add(Lq, S), V, Equal.sym(Nat, V, Nat.add(Lq, S), WW.low_high(k, V)), hSV0)
  +hSf = SH.fits_lek(64n, S, V, hSV, UL.vb(w))
  +esl = Equal.trans(Nat, SW.value(sq), C.low(64n, S), S, Equal.trans(Nat, SW.value(sq), C.low(64n, C.shift(k, SW.value(q))), C.low(64n, S), SH.shl_value(q, k, hb), Equal.cong(Nat, Nat, t => C.low(64n, C.shift(k, t)), SW.value(q), Hq, SH.shr_value(w, k))), WW.low_fit(64n, S, hSf))
  +hle = L.subst(Nat, t => {Nat.is_le(t, V) == True{} : Bool}, S, SW.value(sq), Equal.sym(Nat, SW.value(sq), S, esl), hSV)
  +er1 = Equal.cong(Nat, Nat, t => Nat.sub(V, t), SW.value(sq), S, esl)
  +er2 = Equal.cong(Nat, Nat, t => Nat.sub(t, S), V, Nat.add(Lq, S), WW.low_high(k, V))
  Equal.trans(Nat, SW.value(X.sub(w, sq)), Nat.sub(V, SW.value(sq)), Lq, WA.sub_value(w, sq, hle), Equal.trans(Nat, Nat.sub(V, SW.value(sq)), Nat.sub(V, S), Lq, er1, Equal.trans(Nat, Nat.sub(V, S), Nat.sub(Nat.add(Lq, S), S), Lq, er2, FR.sub_add_l(Lq, S))))

def mfr_c(+s: Bool, +w: WU.U64, +u: Nat, +hu: {Nat.is_le(63n, u) == True{} : Bool}, +k: Nat, +b: Bool, +hb: {Nat.is_lt(k, 64n) == b : Bool}) -> {F.mf_frac(s, w, u, k, b) == SF.round(s, C.low(k, SW.value(w)), u) : F.F64}:
  match b:
    case True{}:
      +r = X.sub(w, X.shl(X.shr(w, k), k))
      Equal.trans(F.F64, F.round_w(s, u, r), SF.round(s, SW.value(r), u), SF.round(s, C.low(k, SW.value(w)), u), T.rw_value(s, u, r, hu), Equal.cong(Nat, F.F64, t => SF.round(s, t, u), SW.value(r), C.low(k, SW.value(w)), rem_v(w, k, hb)))
    case False{}:
      +V = SW.value(w)
      +el = WW.low_fit(k, V, SH.fits_mono(64n, k, V, N.not_lt_le(k, 64n, hb), UL.vb(w)))
      Equal.trans(F.F64, F.round_w(s, u, w), SF.round(s, V, u), SF.round(s, C.low(k, V), u), T.rw_value(s, u, w, hu), Equal.cong(Nat, F.F64, t => SF.round(s, t, u), V, C.low(k, V), Equal.sym(Nat, C.low(k, V), V, el)))

def FRAC(+x: F.F64) -> F.F64:
  SF.round(SF.sign(x), C.low(Nat.sub(SF.zb(), SF.xexp(x)), SF.mant(x)), SF.xexp(x))

def frac_v(+x: F.F64) -> {F.mf_frac(F.signbit(x), F.dmant(x), F.dexp(x), Nat.sub(3000n, F.dexp(x)), Nat.is_lt(Nat.sub(3000n, F.dexp(x)), 64n)) == FRAC(x) : F.F64}:
  +k = Nat.sub(3000n, F.dexp(x))
  +e0 = mfr_c(F.signbit(x), F.dmant(x), F.dexp(x), T.dexp_ge(x), k, Nat.is_lt(k, 64n), {==})
  +e1 = Equal.cong(Bool, F.F64, t => SF.round(t, C.low(k, SW.value(F.dmant(x))), F.dexp(x)), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), C.low(k, t), F.dexp(x)), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
  +e3 = Equal.cong(Nat, F.F64, t => SF.round(SF.sign(x), C.low(Nat.sub(3000n, t), SF.mant(x)), t), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +r0 = SF.round(F.signbit(x), C.low(k, SW.value(F.dmant(x))), F.dexp(x))
  +r1 = SF.round(SF.sign(x), C.low(k, SW.value(F.dmant(x))), F.dexp(x))
  +r2 = SF.round(SF.sign(x), C.low(k, SF.mant(x)), F.dexp(x))
  Equal.trans(F.F64, F.mf_frac(F.signbit(x), F.dmant(x), F.dexp(x), k, Nat.is_lt(k, 64n)), r0, FRAC(x), e0, Equal.trans(F.F64, r0, r1, FRAC(x), e1, Equal.trans(F.F64, r1, r2, FRAC(x), e2, e3)))

def zs(+x: F.F64) -> {F.zero(F.signbit(x)) == SF.zero(SF.sign(x)) : F.F64}:
  Equal.trans(F.F64, F.zero(F.signbit(x)), SF.zero(F.signbit(x)), SF.zero(SF.sign(x)), T.zero_v(F.signbit(x)), Equal.cong(Bool, F.F64, t => SF.zero(t), F.signbit(x), SF.sign(x), FB.signbit_value(x)))

def mff_c(+x: F.F64, +c: Bool) -> {F.mf_fin(x, c) == SF.pickt(F.F64 & F.F64, c, (SF.zero(SF.sign(x)), x), (FRAC(x), SF.to_integral(F.Trunc{}, x))) : F.F64 & F.F64}:
  match c:
    case True{}:
      Equal.cong(F.F64, F.F64 & F.F64, t => (t, x), F.zero(F.signbit(x)), SF.zero(SF.sign(x)), zs(x))
    case False{}:
      +A0 = F.mf_frac(F.signbit(x), F.dmant(x), F.dexp(x), Nat.sub(3000n, F.dexp(x)), Nat.is_lt(Nat.sub(3000n, F.dexp(x)), 64n))
      +p1 = Equal.cong(F.F64, F.F64 & F.F64, t => (t, F.trunc(x)), A0, FRAC(x), frac_v(x))
      +p2 = Equal.cong(F.F64, F.F64 & F.F64, t => (FRAC(x), t), F.trunc(x), SF.to_integral(F.Trunc{}, x), RI.trunc_value(x))
      Equal.trans(F.F64 & F.F64, (A0, F.trunc(x)), (FRAC(x), F.trunc(x)), (FRAC(x), SF.to_integral(F.Trunc{}, x)), p1, p2)

def mf_c(+x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {F.mf_cls(x, t) == SF.pickt(F.F64 & F.F64, Bool.and(t, Bool.not(z)), (SF.qnan(), SF.qnan()), SF.pickt(F.F64 & F.F64, Bool.or(Bool.and(t, z), Nat.is_le(SF.zb(), SF.xexp(x))), (SF.zero(SF.sign(x)), x), (FRAC(x), SF.to_integral(F.Trunc{}, x)))) : F.F64 & F.F64}:
  match t z:
    case True{} True{}:
      +e1 = Equal.cong(Bool, F.F64 & F.F64, b => (F.nan_or(F.zero(F.signbit(x)), Bool.not(b)), F.nan_or(x, Bool.not(b))), X.is_zero(F.frac(x)), True{}, hz)
      Equal.trans(F.F64 & F.F64, (F.nan_or(F.zero(F.signbit(x)), Bool.not(X.is_zero(F.frac(x)))), F.nan_or(x, Bool.not(X.is_zero(F.frac(x))))), (F.zero(F.signbit(x)), x), (SF.zero(SF.sign(x)), x), e1, Equal.cong(F.F64, F.F64 & F.F64, u => (u, x), F.zero(F.signbit(x)), SF.zero(SF.sign(x)), zs(x)))
    case True{} False{}:
      Equal.cong(Bool, F.F64 & F.F64, b => (F.nan_or(F.zero(F.signbit(x)), Bool.not(b)), F.nan_or(x, Bool.not(b))), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = Equal.cong(Nat, F.F64 & F.F64, u => F.mf_fin(x, Nat.is_le(3000n, u)), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(F.F64 & F.F64, F.mf_fin(x, Nat.is_le(3000n, F.dexp(x))), F.mf_fin(x, Nat.is_le(3000n, SF.xexp(x))), SF.pickt(F.F64 & F.F64, Nat.is_le(3000n, SF.xexp(x)), (SF.zero(SF.sign(x)), x), (FRAC(x), SF.to_integral(F.Trunc{}, x))), e1, mff_c(x, Nat.is_le(3000n, SF.xexp(x))))

def modf_value(+x: F.F64) -> SF.Modf.value(x):
  +e1 = Equal.cong(Nat, F.F64 & F.F64, u => F.mf_cls(x, Nat.is_eq(u, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(F.F64 & F.F64, F.modf(x), F.mf_cls(x, Nat.is_eq(SF.efield(x), 2047n)), SF.modf(x), e1, mf_c(x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))
