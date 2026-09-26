import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./u32laws.bend as LW
import ./natcmp.bend as NC
import ./f64bits.bend as FB
import ./f64cmp.bend as FC
import ./f64round.bend as FR
import ./f64norm.bend as NM
import ./f64mexp.bend as EX
import ./f64divv.bend as DV

# Div.value of spec/math/f64.bend: SoftFloat's f64_div (NaN, infinity and
# zero cases, then the quotient of the normalized significands) is the
# spec's div, IEEE 754-2019 §6.2/§7.3 around the exact-then-round quotient.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def hea(+xl: U32, +xh: U32) -> {F.exp_field(F.Bits{xl, xh}) == SF.efield(F.Bits{xl, xh}) : Nat}:
  FB.ef_g(1n, {==}, xh, 1048576, {==}, 2047, {==})

def fval_g(+xl: U32, +xh: U32, +m: U32, +hm: {m == U32{WD.mask(32n, 20n)} : U32}) -> {SW.value(WU.U64{xl, U32.and(xh, m)}) == SF.frac(F.Bits{xl, xh}) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(v(xl), C.shift(32n, z)), v(U32.and(xh, m)), C.low(20n, v(xh)), FB.andm(xh, 20n, m, hm))

def hfr(+xl: U32, +xh: U32) -> {SW.value(F.frac(F.Bits{xl, xh})) == SF.frac(F.Bits{xl, xh}) : Nat}:
  fval_g(xl, xh, 1048575, {==})

def ltf(+xl: U32, +xh: U32, +h: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n) == False{} : Bool}) -> {Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n), Bool.not(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n)), True{}, FB.lt_ne(SF.efield(F.Bits{xl, xh}), 2047n, WW.low_lt(11n, C.high(20n, v(xh)))), Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), False{}, h))

def xl_c(+E: Nat, +h: {Nat.is_lt(E, 2047n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(E, 0n) == c : Bool}) -> {Nat.is_le(SF.pick(Nat, c, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 3971n) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      L.subst(Nat, z => {Nat.is_le(z, 3971n) == True{} : Bool}, Nat.add(1925n, E), Nat.sub(Nat.add(E, SF.zb()), 1075n), Equal.sym(Nat, Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), FC.esub(E)), N.le_add_left(E, 2046n, 1925n, N.lt_succ_le(E, 2046n, h)))

def xexp_le(+E: Nat, +h: {Nat.is_lt(E, 2047n) == True{} : Bool}) -> {Nat.is_le(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 3971n) == True{} : Bool}:
  xl_c(E, h, Nat.is_eq(E, 0n), {==})

def nzle(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.is_le(1n, n) == True{} : Bool}:
  match n:
    case 0n:
      NC.absurd_tf({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hz))
    case 1n+ +np:
      N.zero_le(np)

# a nonzero finite significand is positive
def mpos_c(+sy: Nat, +m: Nat, +w: Nat, +hw: {w == C.shift(sy, m) : Nat}, +h52: {C.fits(52n, w) == False{} : Bool}, +z: Bool, +hz: {Nat.is_eq(m, 0n) == z : Bool}) -> {z == False{} : Bool}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(m, 0n, hz)
      +ew = Equal.trans(Nat, w, C.shift(sy, m), 0n, hw, Equal.trans(Nat, C.shift(sy, m), C.shift(sy, 0n), 0n, Equal.cong(Nat, Nat, t => C.shift(sy, t), m, 0n, e0), WW.shift_zero(sy)))
      Equal.trans(Bool, True{}, C.fits(52n, w), False{}, Equal.cong(Nat, Bool, t => C.fits(52n, t), 0n, w, Equal.sym(Nat, w, 0n, ew)), h52)
    case False{}:
      {==}

def yp_eq(+yl: U32, +yh: U32, +hzy: {Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)) == False{} : Bool}) -> {SF.mant(F.Bits{yl, yh}) == 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n) : Nat}:
  +n1 = NM.n1(1n, {==}, F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +n3 = NM.n3b(1n, {==}, F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +nz = mpos_c(NM.sa(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh}), SW.value(F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), n1, n3, Nat.is_eq(SF.mant(F.Bits{yl, yh}), 0n), {==})
  Equal.sym(Nat, 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n), SF.mant(F.Bits{yl, yh}), N.sub_add(SF.mant(F.Bits{yl, yh}), 1n, nzle(SF.mant(F.Bits{yl, yh}), nz)))

# the finite nonzero quotient
def dfin(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +hzx: {Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)) == False{} : Bool}, +hzy: {Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)) == False{} : Bool}, +hax: {Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n) == True{} : Bool}, +hay: {Nat.is_lt(SF.efield(F.Bits{yl, yh}), 2047n) == True{} : Bool}) -> {F.div_n(s, F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))) == SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s) : F.F64}:
  +n1x = NM.n1(1n, {==}, F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{xl, xh}), hea(xl, xh), hfr(xl, xh), FC.hF(xl, xh), hzx)
  +n1y = NM.n1(1n, {==}, F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +n2x = NM.n2(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{xl, xh}), hea(xl, xh), hfr(xl, xh), FC.hF(xl, xh), hzx)
  +n2y = NM.n2(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +a53 = NM.n3a(1n, {==}, F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{xl, xh}), hea(xl, xh), hfr(xl, xh), FC.hF(xl, xh), hzx)
  +b53 = NM.n3a(1n, {==}, F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +a52 = NM.n3b(1n, {==}, F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.frac(F.Bits{xl, xh}), hea(xl, xh), hfr(xl, xh), FC.hF(xl, xh), hzx)
  +b52 = NM.n3b(1n, {==}, F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{yl, yh}), hea(yl, yh), hfr(yl, yh), FC.hF(yl, yh), hzy)
  +ey = yp_eq(yl, yh, hzy)
  +hB = Equal.trans(Nat, SW.value(F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), C.shift(NM.sa(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), SF.mant(F.Bits{yl, yh})), C.shift(NM.sa(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n)), n1y, Equal.cong(Nat, Nat, t => C.shift(NM.sa(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), t), SF.mant(F.Bits{yl, yh}), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n), ey))
  +r = DV.dcore(1n, {==}, s, F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), SF.mant(F.Bits{xl, xh}), Nat.sub(SF.mant(F.Bits{yl, yh}), 1n), NM.sa(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), NM.sa(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh}), n1x, hB, a53, a52, b53, b52, n2x, n2y, EX.sa_le(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), EX.sa_le(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), EX.xexp_ge(SF.efield(F.Bits{xl, xh})), xexp_le(SF.efield(F.Bits{yl, yh}), hay))
  +sp = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, SF.mant(F.Bits{xl, xh})), z)), Nat.min(Nat.mod(C.shift(200n, SF.mant(F.Bits{xl, xh})), z), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.zb()), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), SF.kq()), 1n))), SF.mant(F.Bits{yl, yh}), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n), ey)
  Equal.trans(F.F64, F.div_n(s, F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, SF.mant(F.Bits{xl, xh})), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n))), Nat.min(Nat.mod(C.shift(200n, SF.mant(F.Bits{xl, xh})), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n)), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), 3000n), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), 200n), 1n))), SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), r, Equal.sym(F.F64, SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, SF.mant(F.Bits{xl, xh})), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n))), Nat.min(Nat.mod(C.shift(200n, SF.mant(F.Bits{xl, xh})), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n)), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), 3000n), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), 200n), 1n))), sp))

def mant0(+xl: U32, +xh: U32, +hc: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n) == True{} : Bool}, +hb: {Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n) == True{} : Bool}) -> {SF.mant(F.Bits{xl, xh}) == 0n : Nat}:
  +e1 = Equal.cong(Bool, Nat, t => Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.b2n(Bool.not(t)))), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), True{}, hc)
  Equal.trans(Nat, SF.mant(F.Bits{xl, xh}), Nat.add(SF.frac(F.Bits{xl, xh}), 0n), 0n, e1, Equal.trans(Nat, Nat.add(SF.frac(F.Bits{xl, xh}), 0n), SF.frac(F.Bits{xl, xh}), 0n, N.add_zero(SF.frac(F.Bits{xl, xh})), N.eq_from_is_eq(SF.frac(F.Bits{xl, xh}), 0n, hb)))

def zero_v(+s: Bool) -> {F.zero(s) == SF.zero(s) : F.F64}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# zero divided by a nonzero finite double
def dz(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +hc: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n) == True{} : Bool}, +hb: {Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n) == True{} : Bool}, +hzy: {Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)) == False{} : Bool}) -> {F.zero(s) == SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, z), SF.mant(F.Bits{yl, yh}))), Nat.min(Nat.mod(C.shift(200n, z), SF.mant(F.Bits{yl, yh})), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.zb()), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), SF.kq()), 1n))), SF.mant(F.Bits{xl, xh}), 0n, mant0(xl, xh, hc, hb))
  +e2 = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, 0n), z)), Nat.min(Nat.mod(C.shift(200n, 0n), z), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.zb()), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), SF.kq()), 1n))), SF.mant(F.Bits{yl, yh}), 1n+Nat.sub(SF.mant(F.Bits{yl, yh}), 1n), yp_eq(yl, yh, hzy))
  Equal.trans(F.F64, F.zero(s), SF.zero(s), SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), zero_v(s), Equal.sym(F.F64, SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), SF.zero(s), Equal.trans(F.F64, SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), SF.round(s, Nat.add(Nat.mul(2n, Nat.div(C.shift(200n, 0n), SF.mant(F.Bits{yl, yh}))), Nat.min(Nat.mod(C.shift(200n, 0n), SF.mant(F.Bits{yl, yh})), 1n)), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.zb()), Nat.add(Nat.add(SF.xexp(F.Bits{yl, yh}), SF.kq()), 1n))), SF.zero(s), e1, e2)))

def dimpl(+s: Bool, +a1: Bool, +b1: Bool, +c1: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +r: F.F64) -> F.F64:
  SF.pick(F.F64, a1, SF.pick(F.F64, Bool.or(Bool.not(b1), a2), F.nan(), F.inf(s)), SF.pick(F.F64, a2, SF.pick(F.F64, Bool.not(b2), F.nan(), F.zero(s)), SF.pick(F.F64, Bool.and(c2, b2), SF.pick(F.F64, Bool.and(c1, b1), F.nan(), F.inf(s)), SF.pick(F.F64, Bool.and(c1, b1), F.zero(s), r))))

def dspec(+s: Bool, +a1: Bool, +b1: Bool, +c1: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +r: F.F64) -> F.F64:
  SF.pick(F.F64, Bool.or(Bool.and(a1, Bool.not(b1)), Bool.and(a2, Bool.not(b2))), SF.qnan(), SF.pick(F.F64, Bool.and(a1, b1), SF.pick(F.F64, Bool.and(a2, b2), SF.qnan(), SF.inf(s)), SF.pick(F.F64, Bool.and(a2, b2), SF.zero(s), SF.pick(F.F64, Bool.and(c2, b2), SF.pick(F.F64, Bool.and(c1, b1), SF.qnan(), SF.inf(s)), r))))

def ion(+s: Bool, +b: Bool) -> {F.inf_or_nan(s, b) == SF.pick(F.F64, b, F.nan(), F.inf(s)) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def non(+x: F.F64, +b: Bool) -> {F.nan_or(x, b) == SF.pick(F.F64, b, F.nan(), x) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dsh4(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +z: Bool) -> {F.div_za(s, ea, fa, eb, fb, z) == SF.pick(F.F64, z, F.zero(s), F.div_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb))) : F.F64}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def dsh3(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +z: Bool) -> {F.div_z(s, ea, fa, eb, fb, z) == SF.pick(F.F64, z, SF.pick(F.F64, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), F.nan(), F.inf(s)), SF.pick(F.F64, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), F.zero(s), F.div_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb)))) : F.F64}:
  match z:
    case True{}:
      ion(s, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)))
    case False{}:
      dsh4(s, ea, fa, eb, fb, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)))

def dsh2(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +t: Bool) -> {F.div_b(s, ea, fa, eb, fb, t) == SF.pick(F.F64, t, SF.pick(F.F64, Bool.not(X.is_zero(fb)), F.nan(), F.zero(s)), SF.pick(F.F64, Bool.and(Nat.is_eq(eb, 0n), X.is_zero(fb)), SF.pick(F.F64, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), F.nan(), F.inf(s)), SF.pick(F.F64, Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), F.zero(s), F.div_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb))))) : F.F64}:
  match t:
    case True{}:
      non(F.zero(s), Bool.not(X.is_zero(fb)))
    case False{}:
      dsh3(s, ea, fa, eb, fb, Bool.and(Nat.is_eq(eb, 0n), X.is_zero(fb)))

def dsh1(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +t: Bool) -> {F.div_cls(s, ea, fa, eb, fb, t) == dimpl(s, t, X.is_zero(fa), Nat.is_eq(ea, 0n), Nat.is_eq(eb, 2047n), X.is_zero(fb), Nat.is_eq(eb, 0n), F.div_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb))) : F.F64}:
  match t:
    case True{}:
      ion(s, Bool.or(Bool.not(X.is_zero(fa)), Nat.is_eq(eb, 2047n)))
    case False{}:
      dsh2(s, ea, fa, eb, fb, Nat.is_eq(eb, 2047n))

def dcase(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +r1: F.F64, +r2: F.F64, +a1: Bool, +b1: Bool, +c1: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +hR: {SF.pick(F.F64, Bool.or(Bool.or(a1, a2), Bool.or(Bool.and(c1, b1), Bool.and(c2, b2))), r2, r1) == r2 : F.F64}, +hZ: {SF.pick(F.F64, Bool.or(Bool.or(a1, a2), Bool.or(Bool.not(Bool.and(c1, b1)), Bool.and(c2, b2))), r2, F.zero(s)) == r2 : F.F64}) -> {dimpl(s, a1, b1, c1, a2, b2, c2, r1) == dspec(s, a1, b1, c1, a2, b2, c2, r2) : F.F64}:
  match a1 b1 c1 a2 b2 c2:
    case True{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      FR.inf_v(s)
    case True{} True{} True{} False{} True{} False{}:
      FR.inf_v(s)
    case True{} True{} True{} False{} False{} True{}:
      FR.inf_v(s)
    case True{} True{} True{} False{} False{} False{}:
      FR.inf_v(s)
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      FR.inf_v(s)
    case True{} True{} False{} False{} True{} False{}:
      FR.inf_v(s)
    case True{} True{} False{} False{} False{} True{}:
      FR.inf_v(s)
    case True{} True{} False{} False{} False{} False{}:
      FR.inf_v(s)
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      zero_v(s)
    case False{} True{} True{} True{} True{} False{}:
      zero_v(s)
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      hZ
    case False{} True{} True{} False{} False{} True{}:
      hZ
    case False{} True{} True{} False{} False{} False{}:
      hZ
    case False{} True{} False{} True{} True{} True{}:
      zero_v(s)
    case False{} True{} False{} True{} True{} False{}:
      zero_v(s)
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      FR.inf_v(s)
    case False{} True{} False{} False{} True{} False{}:
      hR
    case False{} True{} False{} False{} False{} True{}:
      hR
    case False{} True{} False{} False{} False{} False{}:
      hR
    case False{} False{} True{} True{} True{} True{}:
      zero_v(s)
    case False{} False{} True{} True{} True{} False{}:
      zero_v(s)
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      FR.inf_v(s)
    case False{} False{} True{} False{} True{} False{}:
      hR
    case False{} False{} True{} False{} False{} True{}:
      hR
    case False{} False{} True{} False{} False{} False{}:
      hR
    case False{} False{} False{} True{} True{} True{}:
      zero_v(s)
    case False{} False{} False{} True{} True{} False{}:
      zero_v(s)
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      FR.inf_v(s)
    case False{} False{} False{} False{} True{} False{}:
      hR
    case False{} False{} False{} False{} False{} True{}:
      hR
    case False{} False{} False{} False{} False{} False{}:
      hR

def dswap(+s1: Bool, +s2: Bool, +hs: {s1 == s2 : Bool}, +r1: F.F64, +r2: F.F64, +hr: {r1 == r2 : F.F64}, +p1: Bool, +q1: Bool, +h0: {p1 == q1 : Bool}, +p2: Bool, +q2: Bool, +h1: {p2 == q2 : Bool}, +p3: Bool, +q3: Bool, +h2: {p3 == q3 : Bool}, +p4: Bool, +q4: Bool, +h3: {p4 == q4 : Bool}, +p5: Bool, +q5: Bool, +h4: {p5 == q5 : Bool}, +p6: Bool, +q6: Bool, +h5: {p6 == q6 : Bool}) -> {dimpl(s1, p1, p2, p3, p4, p5, p6, r1) == dimpl(s2, q1, q2, q3, q4, q5, q6, r2) : F.F64}:
  Equal.trans(F.F64, dimpl(s1, p1, p2, p3, p4, p5, p6, r1), dimpl(s2, p1, p2, p3, p4, p5, p6, r1), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(w, p1, p2, p3, p4, p5, p6, r1), s1, s2, hs), Equal.trans(F.F64, dimpl(s2, p1, p2, p3, p4, p5, p6, r1), dimpl(s2, p1, p2, p3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(F.F64, F.F64, w => dimpl(s2, p1, p2, p3, p4, p5, p6, w), r1, r2, hr), Equal.trans(F.F64, dimpl(s2, p1, p2, p3, p4, p5, p6, r2), dimpl(s2, q1, p2, p3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(s2, w, p2, p3, p4, p5, p6, r2), p1, q1, h0), Equal.trans(F.F64, dimpl(s2, q1, p2, p3, p4, p5, p6, r2), dimpl(s2, q1, q2, p3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(s2, q1, w, p3, p4, p5, p6, r2), p2, q2, h1), Equal.trans(F.F64, dimpl(s2, q1, q2, p3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(s2, q1, q2, w, p4, p5, p6, r2), p3, q3, h2), Equal.trans(F.F64, dimpl(s2, q1, q2, q3, p4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(s2, q1, q2, q3, w, p5, p6, r2), p4, q4, h3), Equal.trans(F.F64, dimpl(s2, q1, q2, q3, q4, p5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, p6, r2), dimpl(s2, q1, q2, q3, q4, q5, q6, r2), Equal.cong(Bool, F.F64, w => dimpl(s2, q1, q2, q3, q4, w, p6, r2), p5, q5, h4), Equal.cong(Bool, F.F64, w => dimpl(s2, q1, q2, q3, q4, q5, w, r2), p6, q6, h5))))))))

def dkR_c(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +g: Bool, +hg: {Bool.or(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)))) == g : Bool}) -> {SF.pick(F.F64, g, SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), F.div_n(s, F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})))) == SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s) : F.F64}:
  match g:
    case True{}:
      {==}
    case False{}:
      +ha = FC.or_l(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n))), hg)
      +hz = FC.or_r(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n))), hg)
      dfin(s, xl, xh, yl, yh, FC.or_l(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)), hz), FC.or_r(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)), hz), ltf(xl, xh, FC.or_l(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), ha)), ltf(yl, yh, FC.or_r(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), ha)))

def dkZ_c(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +g: Bool, +hg: {Bool.or(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.not(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n))), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)))) == g : Bool}) -> {SF.pick(F.F64, g, SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s), F.zero(s)) == SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, s) : F.F64}:
  match g:
    case True{}:
      {==}
    case False{}:
      +hz = FC.or_r(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.not(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n))), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n))), hg)
      +h1 = FR.not_f(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), FC.or_l(Bool.not(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n))), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)), hz))
      dz(s, xl, xh, yl, yh, FC.and_l(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), h1), FC.and_r(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), h1), FC.or_r(Bool.not(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n))), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)), hz))

def div_value(+x: F.F64, +y: F.F64) -> SF.Div.value(x, y):
  match x y:
    case F.Bits{+xl, +xh} F.Bits{+yl, +yh}:
      +hs = Equal.trans(Bool, Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), Bool.xor(SF.sign(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Equal.cong(Bool, Bool, z => Bool.xor(z, F.signbit(F.Bits{yl, yh})), F.signbit(F.Bits{xl, xh}), SF.sign(F.Bits{xl, xh}), FB.signbit_value(F.Bits{xl, xh})), Equal.cong(Bool, Bool, z => Bool.xor(SF.sign(F.Bits{xl, xh}), z), F.signbit(F.Bits{yl, yh}), SF.sign(F.Bits{yl, yh}), FB.signbit_value(F.Bits{yl, yh})))
      +i1 = dsh1(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 2047n))
      +i2 = dswap(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), hs, F.div_n(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), F.div_n(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), Equal.cong(Bool, F.F64, z => F.div_n(z, F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), hs), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 2047n), F.exp_field(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), hea(xl, xh)), X.is_zero(F.frac(F.Bits{xl, xh})), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), FB.fz_g(xl, xh, 1048575, {==}), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), F.exp_field(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), hea(xl, xh)), Nat.is_eq(F.exp_field(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 2047n), F.exp_field(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hea(yl, yh)), X.is_zero(F.frac(F.Bits{yl, yh})), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), FB.fz_g(yl, yh, 1048575, {==}), Nat.is_eq(F.exp_field(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), F.exp_field(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hea(yl, yh)))
      +i3 = dcase(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), xl, xh, yl, yh, F.div_n(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}))), SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), dkR_c(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), xl, xh, yl, yh, Bool.or(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n)), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)))), {==}), dkZ_c(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), xl, xh, yl, yh, Bool.or(Bool.or(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n)), Bool.or(Bool.not(Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n))), Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n)))), {==}))
      Equal.trans(F.F64, F.div_cls(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 2047n)), dimpl(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), F.div_n(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})))), dspec(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), SF.div_fin(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})))), Equal.trans(F.F64, F.div_cls(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh}), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 2047n)), dimpl(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 2047n), X.is_zero(F.frac(F.Bits{xl, xh})), Nat.is_eq(F.exp_field(F.Bits{xl, xh}), 0n), Nat.is_eq(F.exp_field(F.Bits{yl, yh}), 2047n), X.is_zero(F.frac(F.Bits{yl, yh})), Nat.is_eq(F.exp_field(F.Bits{yl, yh}), 0n), F.div_n(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})))), dimpl(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n), F.div_n(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh})), F.norm_e(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_f(F.exp_field(F.Bits{xl, xh}), F.frac(F.Bits{xl, xh})), F.norm_e(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})), F.norm_f(F.exp_field(F.Bits{yl, yh}), F.frac(F.Bits{yl, yh})))), i1, i2), i3)
