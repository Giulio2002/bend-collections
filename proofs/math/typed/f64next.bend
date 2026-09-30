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
import ./u32laws.bend as LW
import ../../lib/word.bend as WD
import ./u64laws.bend as UL
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64addf.bend as AF
import ./f64cmp.bend as FC
import ./f64tools.bend as T

# nextafter, fmin, fmax and is_integer (IEEE 754-2019 5.3.1 nextUp /
# nextDown and 9.6 minimumNumber / maximumNumber; C99 F.9.8.3, F.9.9.2,
# F.9.9.3; python_style_math_stdlib_design.pdf 4.4, 10): Nextafter.value,
# Fmin.value, Fmax.value, IsInteger.value. The comparisons are
# f64cmp.lt_value / eq_value; a step of nextafter is a step of the
# magnitude bits (value(mag x) = pat(x), f64cmp.magv), repacked with the
# sign (f64round.bits_of).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def non(+y: F.F64, +b: Bool) -> {F.nan_or(y, b) == SF.pick(F.F64, b, SF.qnan(), y) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fpk(+x: F.F64, +y: F.F64, +b: Bool) -> {F.fpick(x, y, b) == SF.pick(F.F64, b, x, y) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the comparisons when neither operand is NaN
def ltc(+x: F.F64, +y: F.F64, +u: {Bool.or(SF.is_nan(x), SF.is_nan(y)) == False{} : Bool}) -> {F.lt(x, y) == Cmp.is_lt(SF.ord(x, y)) : Bool}:
  Equal.trans(Bool, F.lt(x, y), Bool.and(Bool.not(Bool.or(SF.is_nan(x), SF.is_nan(y))), Cmp.is_lt(SF.ord(x, y))), Cmp.is_lt(SF.ord(x, y)), FC.lt_value(x, y), Equal.cong(Bool, Bool, b => Bool.and(Bool.not(b), Cmp.is_lt(SF.ord(x, y))), Bool.or(SF.is_nan(x), SF.is_nan(y)), False{}, u))

def eqc(+x: F.F64, +y: F.F64, +u: {Bool.or(SF.is_nan(x), SF.is_nan(y)) == False{} : Bool}) -> {F.eq(x, y) == Cmp.is_eq(SF.ord(x, y)) : Bool}:
  Equal.trans(Bool, F.eq(x, y), Bool.and(Bool.not(Bool.or(SF.is_nan(x), SF.is_nan(y))), Cmp.is_eq(SF.ord(x, y))), Cmp.is_eq(SF.ord(x, y)), FC.eq_value(x, y), Equal.cong(Bool, Bool, b => Bool.and(Bool.not(b), Cmp.is_eq(SF.ord(x, y))), Bool.or(SF.is_nan(x), SF.is_nan(y)), False{}, u))

def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(False{}, b), False{}, Equal.cong(Bool, Bool, t => Bool.or(t, b), a, False{}, ha), hb)

def zeros_v(+x: F.F64, +y: F.F64) -> {F.zeros(x, y) == Bool.and(SF.is_zero(x), SF.is_zero(y)) : Bool}:
  Equal.trans(Bool, Bool.and(F.is_zero(x), F.is_zero(y)), Bool.and(SF.is_zero(x), F.is_zero(y)), Bool.and(SF.is_zero(x), SF.is_zero(y)), Equal.cong(Bool, Bool, t => Bool.and(t, F.is_zero(y)), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x)), Equal.cong(Bool, Bool, t => Bool.and(SF.is_zero(x), t), F.is_zero(y), SF.is_zero(y), FB.is_zero_value(y)))

def zsg(+x: F.F64, +y: F.F64, +and_: Bool) -> Bool:
  SF.pick(Bool, and_, Bool.and(SF.sign(x), SF.sign(y)), Bool.or(SF.sign(x), SF.sign(y)))

# ---- fmin, fmax ----

def fmin_z_c(+x: F.F64, +y: F.F64, +hx: {SF.is_nan(x) == False{} : Bool}, +hy: {SF.is_nan(y) == False{} : Bool}, +zz: Bool) -> {F.fmin_z(x, y, zz) == SF.pick(F.F64, zz, SF.zero(Bool.or(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y)) : F.F64}:
  match zz:
    case True{}:
      +e1 = T.zero_v(Bool.or(F.signbit(x), F.signbit(y)))
      +e2 = Equal.cong(Bool, F.F64, t => SF.zero(Bool.or(t, F.signbit(y))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e3 = Equal.cong(Bool, F.F64, t => SF.zero(Bool.or(SF.sign(x), t)), F.signbit(y), SF.sign(y), FB.signbit_value(y))
      Equal.trans(F.F64, F.zero(Bool.or(F.signbit(x), F.signbit(y))), SF.zero(Bool.or(F.signbit(x), F.signbit(y))), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), e1, Equal.trans(F.F64, SF.zero(Bool.or(F.signbit(x), F.signbit(y))), SF.zero(Bool.or(SF.sign(x), F.signbit(y))), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), e2, e3))
    case False{}:
      +e1 = Equal.cong(Bool, F.F64, b => F.fpick(x, y, b), F.lt(x, y), Cmp.is_lt(SF.ord(x, y)), ltc(x, y, or_ff(SF.is_nan(x), SF.is_nan(y), hx, hy)))
      Equal.trans(F.F64, F.fpick(x, y, F.lt(x, y)), F.fpick(x, y, Cmp.is_lt(SF.ord(x, y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y), e1, fpk(x, y, Cmp.is_lt(SF.ord(x, y))))

def fmax_z_c(+x: F.F64, +y: F.F64, +hx: {SF.is_nan(x) == False{} : Bool}, +hy: {SF.is_nan(y) == False{} : Bool}, +zz: Bool) -> {F.fmax_z(x, y, zz) == SF.pick(F.F64, zz, SF.zero(Bool.and(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y)) : F.F64}:
  match zz:
    case True{}:
      +e1 = T.zero_v(Bool.and(F.signbit(x), F.signbit(y)))
      +e2 = Equal.cong(Bool, F.F64, t => SF.zero(Bool.and(t, F.signbit(y))), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e3 = Equal.cong(Bool, F.F64, t => SF.zero(Bool.and(SF.sign(x), t)), F.signbit(y), SF.sign(y), FB.signbit_value(y))
      Equal.trans(F.F64, F.zero(Bool.and(F.signbit(x), F.signbit(y))), SF.zero(Bool.and(F.signbit(x), F.signbit(y))), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), e1, Equal.trans(F.F64, SF.zero(Bool.and(F.signbit(x), F.signbit(y))), SF.zero(Bool.and(SF.sign(x), F.signbit(y))), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), e2, e3))
    case False{}:
      +e1 = Equal.cong(Bool, F.F64, b => F.fpick(x, y, b), F.lt(y, x), Cmp.is_lt(SF.ord(y, x)), ltc(y, x, or_ff(SF.is_nan(y), SF.is_nan(x), hy, hx)))
      Equal.trans(F.F64, F.fpick(x, y, F.lt(y, x)), F.fpick(x, y, Cmp.is_lt(SF.ord(y, x))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y), e1, fpk(x, y, Cmp.is_lt(SF.ord(y, x))))

def fmin_ny_c(+x: F.F64, +y: F.F64, +hx: {SF.is_nan(x) == False{} : Bool}, +b: Bool, +hb: {SF.is_nan(y) == b : Bool}) -> {F.fmin_ny(x, y, b) == SF.pick(F.F64, b, x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y))) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      +R = SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y))
      +e1 = Equal.cong(Bool, F.F64, t => F.fmin_z(x, y, t), F.zeros(x, y), Bool.and(SF.is_zero(x), SF.is_zero(y)), zeros_v(x, y))
      Equal.trans(F.F64, F.fmin_z(x, y, F.zeros(x, y)), F.fmin_z(x, y, Bool.and(SF.is_zero(x), SF.is_zero(y))), R, e1, fmin_z_c(x, y, hx, hb, Bool.and(SF.is_zero(x), SF.is_zero(y))))

def fmax_ny_c(+x: F.F64, +y: F.F64, +hx: {SF.is_nan(x) == False{} : Bool}, +b: Bool, +hb: {SF.is_nan(y) == b : Bool}) -> {F.fmax_ny(x, y, b) == SF.pick(F.F64, b, x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y))) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      +R = SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y))
      +e1 = Equal.cong(Bool, F.F64, t => F.fmax_z(x, y, t), F.zeros(x, y), Bool.and(SF.is_zero(x), SF.is_zero(y)), zeros_v(x, y))
      Equal.trans(F.F64, F.fmax_z(x, y, F.zeros(x, y)), F.fmax_z(x, y, Bool.and(SF.is_zero(x), SF.is_zero(y))), R, e1, fmax_z_c(x, y, hx, hb, Bool.and(SF.is_zero(x), SF.is_zero(y))))

def fmin_nx_c(+x: F.F64, +y: F.F64, +a: Bool, +ha: {SF.is_nan(x) == a : Bool}) -> {F.fmin_nx(x, y, a) == SF.pick(F.F64, a, SF.pick(F.F64, SF.is_nan(y), SF.qnan(), y), SF.pick(F.F64, SF.is_nan(y), x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y)))) : F.F64}:
  match a:
    case True{}:
      Equal.trans(F.F64, F.nan_or(y, F.is_nan(y)), F.nan_or(y, SF.is_nan(y)), SF.pick(F.F64, SF.is_nan(y), SF.qnan(), y), Equal.cong(Bool, F.F64, t => F.nan_or(y, t), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y)), non(y, SF.is_nan(y)))
    case False{}:
      +R = SF.pick(F.F64, SF.is_nan(y), x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.or(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(x, y)), x, y)))
      Equal.trans(F.F64, F.fmin_ny(x, y, F.is_nan(y)), F.fmin_ny(x, y, SF.is_nan(y)), R, Equal.cong(Bool, F.F64, t => F.fmin_ny(x, y, t), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y)), fmin_ny_c(x, y, ha, SF.is_nan(y), {==}))

def fmax_nx_c(+x: F.F64, +y: F.F64, +a: Bool, +ha: {SF.is_nan(x) == a : Bool}) -> {F.fmax_nx(x, y, a) == SF.pick(F.F64, a, SF.pick(F.F64, SF.is_nan(y), SF.qnan(), y), SF.pick(F.F64, SF.is_nan(y), x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y)))) : F.F64}:
  match a:
    case True{}:
      Equal.trans(F.F64, F.nan_or(y, F.is_nan(y)), F.nan_or(y, SF.is_nan(y)), SF.pick(F.F64, SF.is_nan(y), SF.qnan(), y), Equal.cong(Bool, F.F64, t => F.nan_or(y, t), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y)), non(y, SF.is_nan(y)))
    case False{}:
      +R = SF.pick(F.F64, SF.is_nan(y), x, SF.pick(F.F64, Bool.and(SF.is_zero(x), SF.is_zero(y)), SF.zero(Bool.and(SF.sign(x), SF.sign(y))), SF.pick(F.F64, Cmp.is_lt(SF.ord(y, x)), x, y)))
      Equal.trans(F.F64, F.fmax_ny(x, y, F.is_nan(y)), F.fmax_ny(x, y, SF.is_nan(y)), R, Equal.cong(Bool, F.F64, t => F.fmax_ny(x, y, t), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y)), fmax_ny_c(x, y, ha, SF.is_nan(y), {==}))

def fmin_value(+x: F.F64, +y: F.F64) -> SF.Fmin.value(x, y):
  Equal.trans(F.F64, F.fmin_nx(x, y, F.is_nan(x)), F.fmin_nx(x, y, SF.is_nan(x)), SF.fmin(x, y), Equal.cong(Bool, F.F64, t => F.fmin_nx(x, y, t), F.is_nan(x), SF.is_nan(x), FB.is_nan_value(x)), fmin_nx_c(x, y, SF.is_nan(x), {==}))

def fmax_value(+x: F.F64, +y: F.F64) -> SF.Fmax.value(x, y):
  Equal.trans(F.F64, F.fmax_nx(x, y, F.is_nan(x)), F.fmax_nx(x, y, SF.is_nan(x)), SF.fmax(x, y), Equal.cong(Bool, F.F64, t => F.fmax_nx(x, y, t), F.is_nan(x), SF.is_nan(x), FB.is_nan_value(x)), fmax_nx_c(x, y, SF.is_nan(x), {==}))

# ---- is_integer ----

def notinj(+a: Bool, +b: Bool, +h: {Bool.not(a) == Bool.not(b) : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, LW.true_ne_false(h))
    case False{} False{}:
      {==}

def iik_t(+w: WU.U64, +k: Nat, +hb: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {X.eq(X.shl(X.shr(w, k), k), w) == Nat.is_eq(C.low(k, SW.value(w)), 0n) : Bool}:
  match w:
    case WU.U64{+l, +h}:
      notinj(X.eq(X.shl(X.shr(WU.U64{l, h}, k), k), WU.U64{l, h}), Nat.is_eq(C.low(k, SW.value(WU.U64{l, h})), 0n), SH.sj_bit(l, h, k, hb))

def iik_c(+w: WU.U64, +k: Nat, +b: Bool, +hb: {Nat.is_lt(k, 64n) == b : Bool}) -> {F.ii_k(w, k, b) == Nat.is_eq(C.low(k, SW.value(w)), 0n) : Bool}:
  match b:
    case True{}:
      iik_t(w, k, hb)
    case False{}:
      +V = SW.value(w)
      +el = WW.low_fit(k, V, SH.fits_mono(64n, k, V, N.not_lt_le(k, 64n, hb), UL.vb(w)))
      Equal.trans(Bool, X.is_zero(w), Nat.is_eq(V, 0n), Nat.is_eq(C.low(k, V), 0n), WA.is_zero_value(w), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), V, C.low(k, V), Equal.sym(Nat, C.low(k, V), V, el)))

def LZ(+x: F.F64) -> Bool:
  Nat.is_eq(C.low(Nat.sub(SF.zb(), SF.xexp(x)), SF.mant(x)), 0n)

def iif_c(+x: F.F64, +c: Bool) -> {F.ii_fin(x, c) == Bool.or(c, LZ(x)) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +k = Nat.sub(3000n, F.dexp(x))
      +e1 = iik_c(F.dmant(x), k, Nat.is_lt(k, 64n), {==})
      +e2 = Equal.cong(Nat, Bool, t => Nat.is_eq(C.low(k, t), 0n), SW.value(F.dmant(x)), SF.mant(x), T.dmant_value(x))
      +e3 = Equal.cong(Nat, Bool, t => Nat.is_eq(C.low(Nat.sub(3000n, t), SF.mant(x)), 0n), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(Bool, F.ii_k(F.dmant(x), k, Nat.is_lt(k, 64n)), Nat.is_eq(C.low(k, SW.value(F.dmant(x))), 0n), LZ(x), e1, Equal.trans(Bool, Nat.is_eq(C.low(k, SW.value(F.dmant(x))), 0n), Nat.is_eq(C.low(k, SF.mant(x)), 0n), LZ(x), e2, e3))

def is_integer_value(+x: F.F64) -> SF.IsInteger.value(x):
  +c = Nat.is_le(3000n, F.dexp(x))
  +e1 = Equal.cong(Nat, Bool, t => Bool.and(Nat.is_lt(t, 2047n), F.ii_fin(x, c)), F.exp_field(x), SF.efield(x), T.ea(x))
  +e2 = Equal.cong(Bool, Bool, t => Bool.and(Nat.is_lt(SF.efield(x), 2047n), t), F.ii_fin(x, c), Bool.or(c, LZ(x)), iif_c(x, c))
  +e3 = Equal.cong(Nat, Bool, t => Bool.and(Nat.is_lt(SF.efield(x), 2047n), Bool.or(Nat.is_le(3000n, t), LZ(x))), F.dexp(x), SF.xexp(x), T.dexp_value(x))
  +b1 = Bool.and(Nat.is_lt(SF.efield(x), 2047n), F.ii_fin(x, c))
  +b2 = Bool.and(Nat.is_lt(SF.efield(x), 2047n), Bool.or(c, LZ(x)))
  +b3 = Bool.and(Nat.is_lt(SF.efield(x), 2047n), Bool.or(Nat.is_le(SF.zb(), SF.xexp(x)), LZ(x)))
  Equal.trans(Bool, F.is_integer(x), b1, b3, e1, Equal.trans(Bool, b1, b2, b3, e2, e3))

# ---- nextafter ----

def sub_le_self(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +bp:
      {==}
    case 1n+ +ap 0n:
      N.le_refl(1n+ap)
    case 1n+ +ap 1n+ +bp:
      N.le_trans(Nat.sub(ap, bp), ap, 1n+ap, sub_le_self(ap, bp), N.le_succ(ap))

def magval(+x: F.F64) -> {SW.value(F.mag(x)) == SF.pat(x) : Nat}:
  match x:
    case F.Bits{+xl, +xh}:
      FC.magv(xl, xh, 2147483647, {==})

def patfit(+x: F.F64) -> {C.fits(63n, SF.pat(x)) == True{} : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      L.subst(Nat, t => {C.fits(63n, t) == True{} : Bool}, Nat.add(v(xl), C.shift(32n, C.low(31n, v(xh)))), SF.pat(F.Bits{xl, xh}), FC.magQ(xl, xh), WW.limbs_fit(32n, 31n, v(xl), C.low(31n, v(xh)), LW.vb(xl), WW.low_fits(31n, v(xh))))

def frac52(+x: F.F64) -> {C.fits(52n, SF.frac(x)) == True{} : Bool}:
  match x:
    case F.Bits{+xl, +xh}:
      AF.hF(xl, xh)

def patz(+x: F.F64) -> {Nat.is_eq(SF.pat(x), 0n) == SF.is_zero(x) : Bool}:
  Equal.trans(Bool, Nat.is_eq(SF.pat(x), 0n), Bool.and(Nat.is_eq(SF.frac(x), 0n), Nat.is_eq(SF.efield(x), 0n)), SF.is_zero(x), FB.z2(SF.frac(x), 52n, SF.efield(x)), T.and_comm(Nat.is_eq(SF.frac(x), 0n), Nat.is_eq(SF.efield(x), 0n)))

# pat + 1 still fits 63 bits unless x is a NaN
def per1(+x: F.F64) -> {Nat.add(SF.pat(x), 1n) == Nat.add(Nat.add(SF.frac(x), 1n), C.shift(52n, SF.efield(x))) : Nat}:
  +Fr = SF.frac(x)
  +S = C.shift(52n, SF.efield(x))
  +ea = NA.add_assoc(Fr, S, 1n)
  +ec = Equal.cong(Nat, Nat, t => Nat.add(Fr, t), Nat.add(S, 1n), Nat.add(1n, S), NA.add_comm(S, 1n))
  +eb = Equal.sym(Nat, Nat.add(Nat.add(Fr, 1n), S), Nat.add(Fr, Nat.add(1n, S)), NA.add_assoc(Fr, 1n, S))
  Equal.trans(Nat, Nat.add(SF.pat(x), 1n), Nat.add(Fr, Nat.add(S, 1n)), Nat.add(Nat.add(Fr, 1n), S), ea, Equal.trans(Nat, Nat.add(Fr, Nat.add(S, 1n)), Nat.add(Fr, Nat.add(1n, S)), Nat.add(Nat.add(Fr, 1n), S), ec, eb))

def p1_c(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +hn: {SF.is_nan(x) == False{} : Bool}, +b: Bool, +hb: {Nat.is_eq(SF.efield(x), 2047n) == b : Bool}) -> {C.fits(63n, Nat.add(SF.pat(x), 1n)) == True{} : Bool}:
  match b:
    case True{}:
      +E = SF.efield(x)
      +Fr = SF.frac(x)
      +S = C.shift(52n, E)
      +fE = WW.low_fits(11n, C.high(20n, SF.hi_nat(x)))
      +er = per1(x)
      +hn2 = Equal.trans(Bool, Bool.not(Nat.is_eq(Fr, 0n)), SF.is_nan(x), False{}, Equal.sym(Bool, SF.is_nan(x), Bool.not(Nat.is_eq(Fr, 0n)), Equal.cong(Bool, Bool, t => Bool.and(t, Bool.not(Nat.is_eq(Fr, 0n))), Nat.is_eq(E, 2047n), True{}, hb)), hn)
      +f0 = N.eq_from_is_eq(Fr, 0n, FR.not_f(Nat.is_eq(Fr, 0n), hn2))
      +e1 = Equal.cong(Nat, Nat, t => Nat.add(Nat.add(t, 1n), S), Fr, 0n, f0)
      +e2 = Equal.trans(Nat, Nat.add(SF.pat(x), 1n), Nat.add(Nat.add(Fr, 1n), S), Nat.add(1n, S), er, e1)
      L.subst(Nat, t => {C.fits(63n, t) == True{} : Bool}, Nat.add(1n, S), Nat.add(SF.pat(x), 1n), Equal.sym(Nat, Nat.add(SF.pat(x), 1n), Nat.add(1n, S), e2), WW.limbs_fit(52n, 11n, 1n, E, {==}, fE))
    case False{}:
      +E = SF.efield(x)
      +Fr = SF.frac(x)
      +S = C.shift(52n, E)
      +fE = WW.low_fits(11n, C.high(20n, SF.hi_nat(x)))
      +er = per1(x)
      +hlt0 = WW.lt_of_fits(11n, E, fE)
      +hlt = Equal.trans(Bool, Nat.is_lt(E, 2047n), Bool.not(Nat.is_eq(E, 2047n)), True{}, FB.lt_ne(E, 2047n, hlt0), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_eq(E, 2047n), False{}, hb))
      +f11a = WW.fits_of_lt(11n, 1n+E, hlt)
      +f11 = L.subst(Nat, t => {C.fits(11n, Nat.add(t, E)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), f11a)
      +hF = Equal.trans(Bool, Nat.is_lt(Fr, C.shift(52n, one)), C.fits(52n, Fr), True{}, FR.lt_fit(52n, one, h1, Fr), frac52(x))
      +h1a = FR.succ_le(Fr, C.shift(52n, one), hF)
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(Fr, 1n), S), Nat.add(C.shift(52n, one), S)), Nat.is_le(Nat.add(Fr, 1n), C.shift(52n, one)), True{}, FR.le_cancel_r(Nat.add(Fr, 1n), C.shift(52n, one), S), h1a)
      +e3 = Equal.sym(Nat, C.shift(52n, Nat.add(one, E)), Nat.add(C.shift(52n, one), S), WW.shift_add(52n, one, E))
      +h3 = L.subst(Nat, t => {Nat.is_le(Nat.add(Nat.add(Fr, 1n), S), t) == True{} : Bool}, Nat.add(C.shift(52n, one), S), C.shift(52n, Nat.add(one, E)), e3, h2)
      +f3 = Equal.trans(Bool, C.fits(Nat.add(52n, 11n), C.shift(52n, Nat.add(one, E))), C.fits(11n, Nat.add(one, E)), True{}, RT.fits_sh(52n, 11n, Nat.add(one, E)), f11)
      +f4 = SH.fits_lek(Nat.add(52n, 11n), Nat.add(Nat.add(Fr, 1n), S), C.shift(52n, Nat.add(one, E)), h3, f3)
      L.subst(Nat, t => {C.fits(Nat.add(52n, 11n), t) == True{} : Bool}, Nat.add(Nat.add(Fr, 1n), S), Nat.add(SF.pat(x), 1n), Equal.sym(Nat, Nat.add(SF.pat(x), 1n), Nat.add(Nat.add(Fr, 1n), S), er), f4)

# a word of value n < 2^63 with the sign bit added is bits(s, n)
def ws(+s: Bool, +w: WU.U64, +h63: {C.fits(63n, SW.value(w)) == True{} : Bool}) -> {F.with_sign(s, w) == FR.bits(s, SW.value(w)) : F.F64}:
  +lo = X.lo(w)
  +hi = X.hi(w)
  +V = SW.value(w)
  +b = SF.b2n(s)
  +T31 = C.shift(31n, b)
  +eta = WA.val_eta(w)
  +eh = Equal.trans(Nat, C.high(32n, V), C.high(32n, Nat.add(v(lo), C.shift(32n, v(hi)))), v(hi), Equal.cong(Nat, Nat, t => C.high(32n, t), V, Nat.add(v(lo), C.shift(32n, v(hi))), WA.val_eta(w)), WW.high_u(32n, v(lo), v(hi), LW.vb(lo)))
  +f31 = L.subst(Nat, t => {C.fits(31n, t) == True{} : Bool}, C.high(32n, V), v(hi), eh, SH.fits_high(32n, 31n, V, h63))
  +esg = Equal.trans(Nat, v(F.sgn(s)), v(SF.pick(U32, s, 2147483648, 0)), T31, Equal.cong(U32, Nat, t => v(t), F.sgn(s), SF.pick(U32, s, 2147483648, 0), FR.sgn_pick(s)), FR.sgv(1n, {==}, s, 2147483648, {==}))
  +fs = WW.limbs_fit(31n, 1n, v(hi), b, f31, FR.b2n_le(s))
  +hs0 = WW.lt_one(32n, 1n, {==}, Nat.add(v(hi), T31), fs)
  +hs = L.subst(Nat, t => {Nat.is_lt(Nat.add(v(hi), t), C.shift(32n, 1n)) == True{} : Bool}, T31, v(F.sgn(s)), Equal.sym(Nat, v(F.sgn(s)), T31, esg), hs0)
  +eadd = Equal.trans(Nat, v(U32.add(hi, F.sgn(s))), Nat.add(v(hi), v(F.sgn(s))), Nat.add(v(hi), T31), FB.addv(1n, {==}, hi, F.sgn(s), hs), Equal.cong(Nat, Nat, t => Nat.add(v(hi), t), v(F.sgn(s)), T31, esg))
  +q1 = Nat.add(v(lo), C.shift(32n, v(U32.add(hi, F.sgn(s)))))
  +q2 = Nat.add(v(lo), C.shift(32n, Nat.add(v(hi), T31)))
  +q3 = Nat.add(v(lo), Nat.add(C.shift(32n, v(hi)), C.shift(32n, T31)))
  +q4 = Nat.add(v(lo), Nat.add(C.shift(32n, v(hi)), C.shift(63n, b)))
  +q5 = Nat.add(Nat.add(v(lo), C.shift(32n, v(hi))), C.shift(63n, b))
  +q6 = Nat.add(V, C.shift(63n, b))
  +g1 = Equal.cong(Nat, Nat, t => Nat.add(v(lo), C.shift(32n, t)), v(U32.add(hi, F.sgn(s))), Nat.add(v(hi), T31), eadd)
  +g2 = Equal.cong(Nat, Nat, t => Nat.add(v(lo), t), C.shift(32n, Nat.add(v(hi), T31)), Nat.add(C.shift(32n, v(hi)), C.shift(32n, T31)), WW.shift_add(32n, v(hi), T31))
  +g3 = Equal.cong(Nat, Nat, t => Nat.add(v(lo), Nat.add(C.shift(32n, v(hi)), t)), C.shift(32n, T31), C.shift(63n, b), Equal.sym(Nat, C.shift(63n, b), C.shift(32n, T31), WW.shift_comp(32n, 31n, b)))
  +g4 = Equal.sym(Nat, q5, q4, NA.add_assoc(v(lo), C.shift(32n, v(hi)), C.shift(63n, b)))
  +g5 = Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(63n, b)), Nat.add(v(lo), C.shift(32n, v(hi))), V, Equal.sym(Nat, V, Nat.add(v(lo), C.shift(32n, v(hi))), eta))
  +hw = Equal.trans(Nat, q1, q2, q6, g1, Equal.trans(Nat, q2, q3, q6, g2, Equal.trans(Nat, q3, q4, q6, g3, Equal.trans(Nat, q4, q5, q6, g4, g5))))
  FR.bits_of(s, V, WU.U64{lo, U32.add(hi, F.sgn(s))}, hw)

def opat(+s: Bool, +P: Nat) -> {SF.of_pat(s, P) == FR.bits(s, P) : F.F64}:
  Equal.trans(F.F64, SF.of_pat(s, P), FR.bits(s, Nat.add(C.low(52n, P), C.shift(52n, C.high(52n, P)))), FR.bits(s, P), FR.enc_bits(s, C.high(52n, P), C.low(52n, P)), Equal.cong(Nat, F.F64, t => FR.bits(s, t), Nat.add(C.low(52n, P), C.shift(52n, C.high(52n, P))), P, Equal.sym(Nat, P, Nat.add(C.low(52n, P), C.shift(52n, C.high(52n, P))), WW.low_high(52n, P))))

def step_fin(+x: F.F64, +W: WU.U64, +P2: Nat, +ev: {SW.value(W) == P2 : Nat}, +h63: {C.fits(63n, P2) == True{} : Bool}) -> {F.with_sign(F.signbit(x), W) == SF.of_pat(SF.sign(x), P2) : F.F64}:
  +hW = L.subst(Nat, t => {C.fits(63n, t) == True{} : Bool}, P2, SW.value(W), Equal.sym(Nat, SW.value(W), P2, ev), h63)
  +e1 = ws(F.signbit(x), W, hW)
  +e2 = Equal.cong(Nat, F.F64, t => FR.bits(F.signbit(x), t), SW.value(W), P2, ev)
  +e3 = Equal.cong(Bool, F.F64, t => FR.bits(t, P2), F.signbit(x), SF.sign(x), FB.signbit_value(x))
  +e4 = Equal.sym(F.F64, SF.of_pat(SF.sign(x), P2), FR.bits(SF.sign(x), P2), opat(SF.sign(x), P2))
  Equal.trans(F.F64, F.with_sign(F.signbit(x), W), FR.bits(F.signbit(x), SW.value(W)), SF.of_pat(SF.sign(x), P2), e1, Equal.trans(F.F64, FR.bits(F.signbit(x), SW.value(W)), FR.bits(F.signbit(x), P2), SF.of_pat(SF.sign(x), P2), e2, Equal.trans(F.F64, FR.bits(F.signbit(x), P2), FR.bits(SF.sign(x), P2), SF.of_pat(SF.sign(x), P2), e3, e4)))

def st_c(+x: F.F64, +hn: {SF.is_nan(x) == False{} : Bool}, +hz: {SF.is_zero(x) == False{} : Bool}, +up: Bool) -> {F.na_step(x, up) == SF.of_pat(SF.sign(x), SF.pick(Nat, up, Nat.add(SF.pat(x), 1n), Nat.sub(SF.pat(x), 1n))) : F.F64}:
  match up:
    case True{}:
      +P = SF.pat(x)
      +M = F.mag(x)
      +W = X.add(M, WU.U64{1, 0})
      +h63 = p1_c(1n, {==}, x, hn, Nat.is_eq(SF.efield(x), 2047n), {==})
      +h64 = SH.fits_mono(63n, 64n, Nat.add(P, 1n), {==}, p1_c(1n, {==}, x, hn, Nat.is_eq(SF.efield(x), 2047n), {==}))
      +ev = Equal.trans(Nat, SW.value(W), C.low(64n, Nat.add(SW.value(M), 1n)), Nat.add(P, 1n), WA.add_value(M, WU.U64{1, 0}), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(M), 1n)), C.low(64n, Nat.add(P, 1n)), Nat.add(P, 1n), Equal.cong(Nat, Nat, t => C.low(64n, Nat.add(t, 1n)), SW.value(M), P, magval(x)), WW.low_fit(64n, Nat.add(P, 1n), h64)))
      step_fin(x, W, Nat.add(P, 1n), ev, h63)
    case False{}:
      +P = SF.pat(x)
      +M = F.mag(x)
      +W = X.sub(M, WU.U64{1, 0})
      +hP = AF.nz_le(P, Equal.trans(Bool, Nat.is_eq(P, 0n), SF.is_zero(x), False{}, patz(x), hz))
      +hM = L.subst(Nat, t => {Nat.is_le(1n, t) == True{} : Bool}, P, SW.value(M), Equal.sym(Nat, SW.value(M), P, magval(x)), hP)
      +ev = Equal.trans(Nat, SW.value(W), Nat.sub(SW.value(M), 1n), Nat.sub(P, 1n), WA.sub_value(M, WU.U64{1, 0}, hM), Equal.cong(Nat, Nat, t => Nat.sub(t, 1n), SW.value(M), P, magval(x)))
      +h63 = SH.fits_lek(63n, Nat.sub(P, 1n), P, sub_le_self(P, 1n), patfit(x))
      step_fin(x, W, Nat.sub(P, 1n), ev, h63)

# from a zero: the smallest subnormal with y's sign
def bs0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +c: U32, +hc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {F.Bits{U32.from_nat(1n), U32.from_nat(C.shift(31n, SF.pick(Nat, s, one, 0n)))} == F.Bits{1, SF.pick(U32, s, c, 0)} : F.F64}:
  match s:
    case True{}:
      Equal.cong(U32, F.F64, z => F.Bits{U32.from_nat(1n), z}, U32.from_nat(C.shift(31n, one)), c, Equal.trans(U32, U32.from_nat(C.shift(31n, one)), U32.from_nat(v(c)), c, Equal.cong(Nat, U32, z => U32.from_nat(z), C.shift(31n, one), v(c), Equal.sym(Nat, v(c), C.shift(31n, one), FB.pwv(31n, {==}, one, h1, c, hc))), LW.rt(c)))
    case False{}:
      {==}

def bsg(+s: Bool) -> {FR.bits(s, 1n) == F.Bits{1, F.sgn(s)} : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, z => F.Bits{U32.from_nat(1n), U32.from_nat(C.shift(31n, z))}, SF.b2n(s), SF.pick(Nat, s, 1n, 0n), Equal.sym(Nat, SF.pick(Nat, s, 1n, 0n), SF.b2n(s), FR.pb(s, 1n, {==})))
  +e2 = bs0(1n, {==}, s, 2147483648, {==})
  +e3 = Equal.cong(U32, F.F64, z => F.Bits{1, z}, SF.pick(U32, s, 2147483648, 0), F.sgn(s), Equal.sym(U32, F.sgn(s), SF.pick(U32, s, 2147483648, 0), FR.sgn_pick(s)))
  Equal.trans(F.F64, FR.bits(s, 1n), F.Bits{U32.from_nat(1n), U32.from_nat(C.shift(31n, SF.pick(Nat, s, 1n, 0n)))}, F.Bits{1, F.sgn(s)}, e1, Equal.trans(F.F64, F.Bits{U32.from_nat(1n), U32.from_nat(C.shift(31n, SF.pick(Nat, s, 1n, 0n)))}, F.Bits{1, SF.pick(U32, s, 2147483648, 0)}, F.Bits{1, F.sgn(s)}, e2, e3))

def nz0(+y: F.F64) -> {F.Bits{1, F.sgn(F.signbit(y))} == SF.encode(SF.sign(y), 0n, 1n) : F.F64}:
  +s = SF.sign(y)
  +e1 = Equal.cong(Bool, F.F64, t => F.Bits{1, F.sgn(t)}, F.signbit(y), s, FB.signbit_value(y))
  +e2 = Equal.sym(F.F64, FR.bits(s, 1n), F.Bits{1, F.sgn(s)}, bsg(s))
  +e3 = Equal.sym(F.F64, SF.encode(s, 0n, 1n), FR.bits(s, 1n), FR.enc_bits(s, 0n, 1n))
  Equal.trans(F.F64, F.Bits{1, F.sgn(F.signbit(y))}, F.Bits{1, F.sgn(s)}, SF.encode(s, 0n, 1n), e1, Equal.trans(F.F64, F.Bits{1, F.sgn(s)}, FR.bits(s, 1n), SF.encode(s, 0n, 1n), e2, e3))

def STEP(+x: F.F64, +y: F.F64) -> F.F64:
  SF.of_pat(SF.sign(x), SF.pick(Nat, Bool.xor(Cmp.is_lt(SF.ord(x, y)), SF.sign(x)), Nat.add(SF.pat(x), 1n), Nat.sub(SF.pat(x), 1n)))

def nzc(+x: F.F64, +y: F.F64, +hu: {Bool.or(SF.is_nan(x), SF.is_nan(y)) == False{} : Bool}, +iz: Bool, +hiz: {SF.is_zero(x) == iz : Bool}) -> {F.na_z(x, y, iz) == SF.pick(F.F64, iz, SF.encode(SF.sign(y), 0n, 1n), STEP(x, y)) : F.F64}:
  match iz:
    case True{}:
      nz0(y)
    case False{}:
      +e1 = Equal.cong(Bool, F.F64, t => F.na_step(x, Bool.xor(t, F.signbit(x))), F.lt(x, y), Cmp.is_lt(SF.ord(x, y)), ltc(x, y, hu))
      +e2 = Equal.cong(Bool, F.F64, t => F.na_step(x, Bool.xor(Cmp.is_lt(SF.ord(x, y)), t)), F.signbit(x), SF.sign(x), FB.signbit_value(x))
      +e3 = st_c(x, FC.or_l(SF.is_nan(x), SF.is_nan(y), hu), hiz, Bool.xor(Cmp.is_lt(SF.ord(x, y)), SF.sign(x)))
      +a1 = F.na_step(x, Bool.xor(Cmp.is_lt(SF.ord(x, y)), F.signbit(x)))
      +a2 = F.na_step(x, Bool.xor(Cmp.is_lt(SF.ord(x, y)), SF.sign(x)))
      Equal.trans(F.F64, F.na_step(x, Bool.xor(F.lt(x, y), F.signbit(x))), a1, STEP(x, y), e1, Equal.trans(F.F64, a1, a2, STEP(x, y), e2, e3))

def neq_c(+x: F.F64, +y: F.F64, +hu: {Bool.or(SF.is_nan(x), SF.is_nan(y)) == False{} : Bool}, +e: Bool) -> {F.na_eq(x, y, e) == SF.pick(F.F64, e, y, SF.pick(F.F64, SF.is_zero(x), SF.encode(SF.sign(y), 0n, 1n), STEP(x, y))) : F.F64}:
  match e:
    case True{}:
      {==}
    case False{}:
      +e1 = Equal.cong(Bool, F.F64, t => F.na_z(x, y, t), F.is_zero(x), SF.is_zero(x), FB.is_zero_value(x))
      Equal.trans(F.F64, F.na_z(x, y, F.is_zero(x)), F.na_z(x, y, SF.is_zero(x)), SF.pick(F.F64, SF.is_zero(x), SF.encode(SF.sign(y), 0n, 1n), STEP(x, y)), e1, nzc(x, y, hu, SF.is_zero(x), {==}))

def na_c(+x: F.F64, +y: F.F64, +u: Bool, +hu: {Bool.or(SF.is_nan(x), SF.is_nan(y)) == u : Bool}) -> {F.na_nan(x, y, u) == SF.pick(F.F64, Bool.not(Bool.not(u)), SF.qnan(), SF.pick(F.F64, Cmp.is_eq(SF.ord(x, y)), y, SF.pick(F.F64, SF.is_zero(x), SF.encode(SF.sign(y), 0n, 1n), STEP(x, y)))) : F.F64}:
  match u:
    case True{}:
      {==}
    case False{}:
      +R = SF.pick(F.F64, Cmp.is_eq(SF.ord(x, y)), y, SF.pick(F.F64, SF.is_zero(x), SF.encode(SF.sign(y), 0n, 1n), STEP(x, y)))
      +e1 = Equal.cong(Bool, F.F64, t => F.na_eq(x, y, t), F.eq(x, y), Cmp.is_eq(SF.ord(x, y)), eqc(x, y, hu))
      Equal.trans(F.F64, F.na_eq(x, y, F.eq(x, y)), F.na_eq(x, y, Cmp.is_eq(SF.ord(x, y))), R, e1, neq_c(x, y, hu, Cmp.is_eq(SF.ord(x, y))))

def nextafter_value(+x: F.F64, +y: F.F64) -> SF.Nextafter.value(x, y):
  +e1 = Equal.cong(Bool, F.F64, t => F.na_nan(x, y, Bool.or(t, F.is_nan(y))), F.is_nan(x), SF.is_nan(x), FB.is_nan_value(x))
  +e2 = Equal.cong(Bool, F.F64, t => F.na_nan(x, y, Bool.or(SF.is_nan(x), t)), F.is_nan(y), SF.is_nan(y), FB.is_nan_value(y))
  +a1 = F.na_nan(x, y, Bool.or(SF.is_nan(x), F.is_nan(y)))
  +a2 = F.na_nan(x, y, Bool.or(SF.is_nan(x), SF.is_nan(y)))
  Equal.trans(F.F64, F.nextafter(x, y), a1, SF.nextafter(x, y), e1, Equal.trans(F.F64, a1, a2, SF.nextafter(x, y), e2, na_c(x, y, Bool.or(SF.is_nan(x), SF.is_nan(y)), {==})))
