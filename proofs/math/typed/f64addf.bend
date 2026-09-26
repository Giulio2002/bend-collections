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
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64add.bend as WA
import ./natcmp.bend as NC
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64addc.bend as AC
import ./f64adde.bend as AE
import ./f64addg.bend as AG
import ./f64addh.bend as AH

# The finite case of Add.value: SoftFloat's addF64 on two finite doubles is
# the spec's add_fin, the exact sum or difference at the common scale
# rounded once (Flocq's round_NE of the exact sum; SoftFloat's addMagsF64 and
# subMagsF64 case split on the exponent order).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def hea(+xl: U32, +xh: U32) -> {F.exp_field(F.Bits{xl, xh}) == SF.efield(F.Bits{xl, xh}) : Nat}:
  FB.ef_g(1n, {==}, xh, 1048576, {==}, 2047, {==})

def fval_g(+xl: U32, +xh: U32, +m: U32, +hm: {m == U32{WD.mask(32n, 20n)} : U32}) -> {SW.value(WU.U64{xl, U32.and(xh, m)}) == SF.frac(F.Bits{xl, xh}) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(v(xl), C.shift(32n, z)), v(U32.and(xh, m)), C.low(20n, v(xh)), FB.andm(xh, 20n, m, hm))

def hfr(+xl: U32, +xh: U32) -> {SW.value(F.frac(F.Bits{xl, xh})) == SF.frac(F.Bits{xl, xh}) : Nat}:
  fval_g(xl, xh, 1048575, {==})

def hF(+xl: U32, +xh: U32) -> {C.fits(52n, SF.frac(F.Bits{xl, xh})) == True{} : Bool}:
  WW.limbs_fit(32n, 20n, v(xl), C.low(20n, v(xh)), LW.vb(xl), WW.low_fits(20n, v(xh)))

def ap(+x: F.F64, +y: F.F64, +same: Bool) -> {F.add_pick(x, y, same) == SF.pick(F.F64, same, F.add_mags(x, y, F.signbit(x)), F.sub_mags(x, y, F.signbit(x))) : F.F64}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def le_rw(+a: Nat, +a2: Nat, +ha: {a == a2 : Nat}, +b: Nat, +b2: Nat, +hb: {b == b2 : Nat}, +h: {Nat.is_le(a2, b2) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  +h2 = L.subst(Nat, z => {Nat.is_le(z, b2) == True{} : Bool}, a2, a, Equal.sym(Nat, a, a2, ha), h)
  L.subst(Nat, z => {Nat.is_le(a, z) == True{} : Bool}, b2, b, Equal.sym(Nat, b, b2, hb), h2)

def nz_le(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.is_le(1n, n) == True{} : Bool}:
  match n:
    case 0n:
      NC.absurd_tf({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hz))
    case 1n+ +np:
      N.zero_le(np)

def xe_le_c(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(a, 0n) == z : Bool}) -> {Nat.is_le(AG.xe(a), AG.xe(b)) == True{} : Bool}:
  match z:
    case True{}:
      +hb = N.le_trans(1n, 1n+a, b, N.zero_le(a), N.lt_succ_le_succ(a, b, h))
      +xb = AG.xe_n(b, AG.posz(b, hb))
      le_rw(AG.xe(a), 1926n, AG.xe_z(a, hz), AG.xe(b), Nat.add(1925n, b), xb, N.le_add_left(1n, b, 1925n, hb))
    case False{}:
      +hb = N.le_trans(1n, 1n+a, b, N.zero_le(a), N.lt_succ_le_succ(a, b, h))
      +xb = AG.xe_n(b, AG.posz(b, hb))
      le_rw(AG.xe(a), Nat.add(1925n, a), AG.xe_n(a, hz), AG.xe(b), Nat.add(1925n, b), xb, N.le_add_left(a, b, 1925n, N.lt_le(a, b, h)))

def xe_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(AG.xe(a), AG.xe(b)) == True{} : Bool}:
  xe_le_c(a, b, h, Nat.is_eq(a, 0n), {==})

def xem_c(+e: Nat, +z: Bool, +hz: {Nat.is_eq(e, 0n) == z : Bool}) -> {Nat.add(1926n, Nat.sub(e, 1n)) == AG.xe(e) : Nat}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(e, 0n, hz)
      L.subst(Nat, w => {Nat.add(1926n, Nat.sub(w, 1n)) == AG.xe(w) : Nat}, 0n, e, Equal.sym(Nat, e, 0n, e0), {==})
    case False{}:
      +e1 = Equal.cong(Nat, Nat, w => Nat.add(1925n, w), Nat.add(1n, Nat.sub(e, 1n)), e, N.sub_add(e, 1n, nz_le(e, hz)))
      Equal.trans(Nat, Nat.add(1926n, Nat.sub(e, 1n)), Nat.add(1925n, e), AG.xe(e), e1, Equal.sym(Nat, AG.xe(e), Nat.add(1925n, e), AG.xe_n(e, hz)))

def xem(+e: Nat) -> {Nat.add(1926n, Nat.sub(e, 1n)) == AG.xe(e) : Nat}:
  xem_c(e, Nat.is_eq(e, 0n), {==})

def hovm(+e: Nat, +h: {Nat.is_lt(e, 2047n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.sub(e, 1n), 1n), 2047n) == True{} : Bool}:
  match e:
    case 0n:
      {==}
    case 1n+ +p:
      +e1 = Equal.trans(Nat, Nat.add(Nat.sub(p, 0n), 1n), Nat.add(p, 1n), 1n+p, Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.sub(p, 0n), p, N.sub_zero(p)), Equal.trans(Nat, Nat.add(p, 1n), 1n+Nat.add(p, 0n), 1n+p, N.add_succ(p, 0n), N.succ_cong(Nat.add(p, 0n), p, N.add_zero(p))))
      L.subst(Nat, z => {Nat.is_lt(z, 2047n) == True{} : Bool}, 1n+p, Nat.add(Nat.sub(p, 0n), 1n), Equal.sym(Nat, Nat.add(Nat.sub(p, 0n), 1n), 1n+p, e1), h)

def rc2(+s: Bool, +s2: Bool, +hs: {s == s2 : Bool}, +m: Nat, +m2: Nat, +hm: {m == m2 : Nat}, +x: Nat, +x2: Nat, +hx: {x == x2 : Nat}) -> {SF.round(s, m, x) == SF.round(s2, m2, x2) : F.F64}:
  +e1 = L.subst(Bool, z => {SF.round(s, m, x) == SF.round(z, m, x) : F.F64}, s, s2, hs, {==})
  +e2 = L.subst(Nat, z => {SF.round(s, m, x) == SF.round(s2, z, x) : F.F64}, m, m2, hm, e1)
  L.subst(Nat, z => {SF.round(s, m, x) == SF.round(s2, m2, z) : F.F64}, x, x2, hx, e2)

def spec_lt(+sa: Bool, +sb: Bool, +ea: Nat, +eb: Nat, +Fa: Nat, +Fb: Nat, +h: {Nat.is_le(AG.xe(ea), AG.xe(eb)) == True{} : Bool}) -> {SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))) == SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, w => SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), w), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), w), AG.mt(eb, Fb)), w), Nat.min(AG.xe(ea), AG.xe(eb)), AG.xe(ea), AG.min_l(AG.xe(ea), AG.xe(eb), h))
  +e2 = Equal.cong(Nat, F.F64, z => SF.add_mag(sa, C.shift(z, AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), Nat.sub(AG.xe(ea), AG.xe(ea)), 0n, N.sub_self(AG.xe(ea)))
  Equal.trans(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(ea)), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), e1, e2)

def spec_gt(+sa: Bool, +sb: Bool, +ea: Nat, +eb: Nat, +Fa: Nat, +Fb: Nat, +h: {Nat.is_le(AG.xe(eb), AG.xe(ea)) == True{} : Bool}) -> {SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))) == SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, w => SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), w), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), w), AG.mt(eb, Fb)), w), Nat.min(AG.xe(ea), AG.xe(eb)), AG.xe(eb), AG.min_r(AG.xe(ea), AG.xe(eb), h))
  +e2 = Equal.cong(Nat, F.F64, z => SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, C.shift(z, AG.mt(eb, Fb)), AG.xe(eb)), Nat.sub(AG.xe(eb), AG.xe(eb)), 0n, N.sub_self(AG.xe(eb)))
  Equal.trans(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(eb)), AG.mt(eb, Fb)), AG.xe(eb)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), e1, e2)

def spec_eq(+sa: Bool, +sb: Bool, +ea: Nat, +Fa: Nat, +Fb: Nat) -> {SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fb)), Nat.min(AG.xe(ea), AG.xe(ea))) == SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)) : F.F64}:
  +e1 = Equal.cong(Nat, F.F64, w => SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), w), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), w), AG.mt(ea, Fb)), w), Nat.min(AG.xe(ea), AG.xe(ea)), AG.xe(ea), AG.min_l(AG.xe(ea), AG.xe(ea), N.le_refl(AG.xe(ea))))
  +e2 = Equal.cong(Nat, F.F64, z => SF.add_mag(sa, C.shift(z, AG.mt(ea, Fa)), sb, C.shift(z, AG.mt(ea, Fb)), AG.xe(ea)), Nat.sub(AG.xe(ea), AG.xe(ea)), 0n, N.sub_self(AG.xe(ea)))
  Equal.trans(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fb)), Nat.min(AG.xe(ea), AG.xe(ea))), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(ea)), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), AG.xe(ea)), AG.mt(ea, Fb)), AG.xe(ea)), SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), e1, e2)

def caseLT(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +sb: Bool, +ea: Nat, +eb: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +hb: {Nat.is_eq(eb, 2047n) == False{} : Bool}, +hlt: {Nat.is_lt(ea, eb) == True{} : Bool}, +sg: Bool, +hsg: {Bool.not(Bool.xor(sa, sb)) == sg : Bool}) -> {SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, eb, LT{}), F.sm_case(x, y, sa, ea, eb, LT{})) == SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)) : F.F64}:
  match sg:
    case True{}:
      +i1 = Equal.cong(Bool, F.F64, t => F.am_big(y, sa, eb, F.frac(y), ea, F.frac(x), t), Nat.is_eq(eb, 2047n), False{}, hb)
      +i2 = AH.bigA(one, h1, sa, eb, F.frac(y), ea, F.frac(x), Fb, Fa, hfb, hfa, hFb, hFa, hlt)
      +sp = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))))), Bool.not(Bool.xor(sa, sb)), True{}, hsg)
      Equal.trans(F.F64, F.am_case(x, y, sa, ea, eb, LT{}), SF.round(sa, Nat.add(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), AG.xe(ea)), SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), Equal.trans(F.F64, F.am_case(x, y, sa, ea, eb, LT{}), F.rp62(sa, Nat.add(F.off(), eb), X.add(X.add(WU.U64{0, 536870912}, X.shl(F.frac(y), 9n)), X.shr_jam(F.am_small(ea, X.shl(F.frac(x), 9n)), Nat.sub(eb, ea)))), SF.round(sa, Nat.add(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), AG.xe(ea)), i1, i2), Equal.sym(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), SF.round(sa, Nat.add(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), AG.xe(ea)), sp))
    case False{}:
      +i1 = Equal.cong(Bool, F.F64, t => F.sm_big(y, Bool.not(sa), eb, F.frac(y), ea, F.frac(x), t), Nat.is_eq(eb, 2047n), False{}, hb)
      +i2 = AH.bigS(one, h1, Bool.not(sa), eb, F.frac(y), ea, F.frac(x), Fb, Fa, hfb, hfa, hFb, hFa, hlt)
      +i3 = Equal.cong(Bool, F.F64, t => SF.round(t, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), Bool.not(sa), sb, AG.sgn(sa, sb, hsg))
      +sp1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))))), Bool.not(Bool.xor(sa, sb)), False{}, hsg)
      +sp2 = Equal.cong(Cmp, F.F64, t => SF.sub_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea), t), Nat.cmp(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb))), LT{}, AG.bigcmp(one, h1, eb, ea, Fb, Fa, hFb, hFa, hlt))
      +imp = Equal.trans(F.F64, F.sm_case(x, y, sa, ea, eb, LT{}), F.norm_round_pack(Bool.not(sa), Nat.add(F.off(), Nat.sub(eb, 1n)), X.sub(X.add(X.shl(F.frac(y), 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(ea, X.shl(F.frac(x), 10n)), Nat.sub(eb, ea)))), SF.round(sb, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), i1, Equal.trans(F.F64, F.norm_round_pack(Bool.not(sa), Nat.add(F.off(), Nat.sub(eb, 1n)), X.sub(X.add(X.shl(F.frac(y), 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(ea, X.shl(F.frac(x), 10n)), Nat.sub(eb, ea)))), SF.round(Bool.not(sa), Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), SF.round(sb, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), i2, i3))
      +spc = Equal.trans(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)))), SF.round(sb, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), sp1, sp2)
      Equal.trans(F.F64, F.sm_case(x, y, sa, ea, eb, LT{}), SF.round(sb, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), imp, Equal.sym(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), SF.round(sb, Nat.sub(C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.mt(ea, Fa)), AG.xe(ea)), spc))

def caseGT(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +sb: Bool, +ea: Nat, +eb: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +ha: {Nat.is_eq(ea, 2047n) == False{} : Bool}, +hgt: {Nat.is_lt(eb, ea) == True{} : Bool}, +sg: Bool, +hsg: {Bool.not(Bool.xor(sa, sb)) == sg : Bool}) -> {SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, eb, GT{}), F.sm_case(x, y, sa, ea, eb, GT{})) == SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)) : F.F64}:
  match sg:
    case True{}:
      +i1 = Equal.cong(Bool, F.F64, t => F.am_big(x, sa, ea, F.frac(x), eb, F.frac(y), t), Nat.is_eq(ea, 2047n), False{}, ha)
      +i2 = AH.bigA(one, h1, sa, ea, F.frac(x), eb, F.frac(y), Fa, Fb, hfa, hfb, hFa, hFb, hgt)
      +i3 = Equal.cong(Nat, F.F64, z => SF.round(sa, z, AG.xe(eb)), Nat.add(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa))), Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), NA.add_comm(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa))))
      +sp = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), SF.sub_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb), Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)))), Bool.not(Bool.xor(sa, sb)), True{}, hsg)
      +imp = Equal.trans(F.F64, F.am_case(x, y, sa, ea, eb, GT{}), F.rp62(sa, Nat.add(F.off(), ea), X.add(X.add(WU.U64{0, 536870912}, X.shl(F.frac(x), 9n)), X.shr_jam(F.am_small(eb, X.shl(F.frac(y), 9n)), Nat.sub(ea, eb)))), SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), i1, Equal.trans(F.F64, F.rp62(sa, Nat.add(F.off(), ea), X.add(X.add(WU.U64{0, 536870912}, X.shl(F.frac(x), 9n)), X.shr_jam(F.am_small(eb, X.shl(F.frac(y), 9n)), Nat.sub(ea, eb)))), SF.round(sa, Nat.add(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa))), AG.xe(eb)), SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), i2, i3))
      Equal.trans(F.F64, F.am_case(x, y, sa, ea, eb, GT{}), SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), imp, Equal.sym(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), sp))
    case False{}:
      +i1 = Equal.cong(Bool, F.F64, t => F.sm_big(x, sa, ea, F.frac(x), eb, F.frac(y), t), Nat.is_eq(ea, 2047n), False{}, ha)
      +i2 = AH.bigS(one, h1, sa, ea, F.frac(x), eb, F.frac(y), Fa, Fb, hfa, hfb, hFa, hFb, hgt)
      +c1 = AG.bigcmp(one, h1, ea, eb, Fa, Fb, hFa, hFb, hgt)
      +c2 = Equal.trans(Cmp, Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), SF.flip(Nat.cmp(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)))), GT{}, Equal.sym(Cmp, SF.flip(Nat.cmp(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)))), Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), NC.cmp_flip(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)))), Equal.cong(Cmp, Cmp, t => SF.flip(t), Nat.cmp(AG.mt(eb, Fb), C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa))), LT{}, c1))
      +sp1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), SF.sub_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb), Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)))), Bool.not(Bool.xor(sa, sb)), False{}, hsg)
      +sp2 = Equal.cong(Cmp, F.F64, t => SF.sub_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb), t), Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), GT{}, c2)
      +imp = Equal.trans(F.F64, F.sm_case(x, y, sa, ea, eb, GT{}), F.norm_round_pack(sa, Nat.add(F.off(), Nat.sub(ea, 1n)), X.sub(X.add(X.shl(F.frac(x), 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(eb, X.shl(F.frac(y), 10n)), Nat.sub(ea, eb)))), SF.round(sa, Nat.sub(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), i1, i2)
      +spc = Equal.trans(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), SF.sub_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb), Nat.cmp(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb))), SF.round(sa, Nat.sub(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), sp1, sp2)
      Equal.trans(F.F64, F.sm_case(x, y, sa, ea, eb, GT{}), SF.round(sa, Nat.sub(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), imp, Equal.sym(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), SF.round(sa, Nat.sub(C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), AG.mt(eb, Fb)), AG.xe(eb)), spc))

def aeq_c(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +ea: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +ha: {Nat.is_eq(ea, 2047n) == False{} : Bool}, +z: Bool, +hz: {Nat.is_eq(ea, 0n) == z : Bool}) -> {F.am_eq(x, sa, ea, F.frac(x), F.frac(y)) == SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)) : F.F64}:
  match z:
    case True{}:
      +e0 = N.eq_from_is_eq(ea, 0n, hz)
      +r0 = AC.ame0(one, h1, sa, F.frac(x), F.frac(y), Fa, Fb, hfa, hfb, hFa, hFb)
      +b0 = Equal.cong(Nat, F.F64, w => SF.round(sa, w, 1926n), Nat.add(Fa, Fb), Nat.add(Nat.add(Fa, 0n), Nat.add(Fb, 0n)), Equal.trans(Nat, Nat.add(Fa, Fb), Nat.add(Nat.add(Fa, 0n), Fb), Nat.add(Nat.add(Fa, 0n), Nat.add(Fb, 0n)), Equal.cong(Nat, Nat, w => Nat.add(w, Fb), Fa, Nat.add(Fa, 0n), Equal.sym(Nat, Nat.add(Fa, 0n), Fa, N.add_zero(Fa))), Equal.cong(Nat, Nat, w => Nat.add(Nat.add(Fa, 0n), w), Fb, Nat.add(Fb, 0n), Equal.sym(Nat, Nat.add(Fb, 0n), Fb, N.add_zero(Fb)))))
      +p0 = Equal.trans(F.F64, F.am_eq(x, sa, 0n, F.frac(x), F.frac(y)), SF.round(sa, Nat.add(Fa, Fb), 1926n), SF.round(sa, Nat.add(AG.mt(0n, Fa), AG.mt(0n, Fb)), AG.xe(0n)), r0, b0)
      L.subst(Nat, w => {F.am_eq(x, sa, w, F.frac(x), F.frac(y)) == SF.round(sa, Nat.add(AG.mt(w, Fa), AG.mt(w, Fb)), AG.xe(w)) : F.F64}, 0n, ea, Equal.sym(Nat, ea, 0n, e0), p0)
    case False{}:
      +ep = AG.pred_eq(ea, hz)
      +hp = L.subst(Nat, w => {Nat.is_eq(w, 2047n) == False{} : Bool}, ea, 1n+N.pred(ea), Equal.sym(Nat, 1n+N.pred(ea), ea, ep), ha)
      +i1 = Equal.cong(Bool, F.F64, t => F.am_eq_n(x, sa, 1n+N.pred(ea), F.frac(x), F.frac(y), t), Nat.is_eq(1n+N.pred(ea), 2047n), False{}, hp)
      +i2 = AC.amen(one, h1, sa, 1n+N.pred(ea), F.frac(x), F.frac(y), Fa, Fb, hfa, hfb, hFa, hFb, 2097152, {==})
      +q1 = Equal.trans(F.F64, F.am_eq(x, sa, 1n+N.pred(ea), F.frac(x), F.frac(y)), F.round_pack(sa, Nat.add(F.off(), 1n+N.pred(ea)), X.shl(X.add(WU.U64{0, 2097152}, X.add(F.frac(x), F.frac(y))), 9n)), SF.round(sa, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, 1n+N.pred(ea))), i1, i2)
      +q = L.subst(Nat, w => {F.am_eq(x, sa, w, F.frac(x), F.frac(y)) == SF.round(sa, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, w)) : F.F64}, 1n+N.pred(ea), ea, ep, q1)
      +ma = AG.mt_n(one, h1, ea, Fa, hz)
      +mb = AG.mt_n(one, h1, ea, Fb, hz)
      +em = Equal.trans(Nat, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(AG.mt(ea, Fa), Nat.add(Fb, C.shift(52n, one))), Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), Equal.cong(Nat, Nat, w => Nat.add(w, Nat.add(Fb, C.shift(52n, one))), Nat.add(Fa, C.shift(52n, one)), AG.mt(ea, Fa), Equal.sym(Nat, AG.mt(ea, Fa), Nat.add(Fa, C.shift(52n, one)), ma)), Equal.cong(Nat, Nat, w => Nat.add(AG.mt(ea, Fa), w), Nat.add(Fb, C.shift(52n, one)), AG.mt(ea, Fb), Equal.sym(Nat, AG.mt(ea, Fb), Nat.add(Fb, C.shift(52n, one)), mb)))
      +b = rc2(sa, sa, {==}, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), em, Nat.add(1925n, ea), AG.xe(ea), Equal.sym(Nat, AG.xe(ea), Nat.add(1925n, ea), AG.xe_n(ea, hz)))
      Equal.trans(F.F64, F.am_eq(x, sa, ea, F.frac(x), F.frac(y)), SF.round(sa, Nat.add(Nat.add(Fa, C.shift(52n, one)), Nat.add(Fb, C.shift(52n, one))), Nat.add(1925n, ea)), SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), q, b)

def seq(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +sb: Bool, +hsg: {Bool.not(Bool.xor(sa, sb)) == False{} : Bool}, +ea: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +hlta: {Nat.is_lt(ea, 2047n) == True{} : Bool}, +d: Cmp, +hd: {Nat.cmp(Fa, Fb) == d : Cmp}) -> {F.sm_eq2(sa, ea, F.frac(x), F.frac(y), d) == SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), d) : F.F64}:
  match d:
    case EQ{}:
      AG.zero_v(False{})
    case GT{}:
      +hlt = NC.lt_of_gt(Fa, Fb, hd)
      +hle = L.subst(Nat, w => {Nat.is_le(w, SW.value(F.frac(x))) == True{} : Bool}, Fb, SW.value(F.frac(y)), Equal.sym(Nat, SW.value(F.frac(y)), Fb, hfb), L.subst(Nat, w => {Nat.is_le(Fb, w) == True{} : Bool}, Fa, SW.value(F.frac(x)), Equal.sym(Nat, SW.value(F.frac(x)), Fa, hfa), N.lt_le(Fb, Fa, hlt)))
      +hdv = Equal.trans(Nat, SW.value(X.sub(F.frac(x), F.frac(y))), Nat.sub(SW.value(F.frac(x)), SW.value(F.frac(y))), Nat.sub(Fa, Fb), WA.sub_value(F.frac(x), F.frac(y), hle), Equal.trans(Nat, Nat.sub(SW.value(F.frac(x)), SW.value(F.frac(y))), Nat.sub(Fa, SW.value(F.frac(y))), Nat.sub(Fa, Fb), Equal.cong(Nat, Nat, w => Nat.sub(w, SW.value(F.frac(y))), SW.value(F.frac(x)), Fa, hfa), Equal.cong(Nat, Nat, w => Nat.sub(Fa, w), SW.value(F.frac(y)), Fb, hfb)))
      +hD = Equal.trans(Bool, C.fits(52n, Nat.sub(Fa, Fb)), Nat.is_lt(Nat.sub(Fa, Fb), C.shift(52n, one)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.sub(Fa, Fb), C.shift(52n, one)), C.fits(52n, Nat.sub(Fa, Fb)), FR.lt_fit(52n, one, h1, Nat.sub(Fa, Fb))), N.le_lt_trans(Nat.sub(Fa, Fb), Fa, C.shift(52n, one), AG.sub_le(Fa, Fb), Equal.trans(Bool, Nat.is_lt(Fa, C.shift(52n, one)), C.fits(52n, Fa), True{}, FR.lt_fit(52n, one, h1, Fa), hFa)))
      +hz = AG.posz(Nat.sub(Fa, Fb), FR.lt_sub_pos(Fb, Fa, hlt))
      +r = AE.smx(one, h1, sa, Nat.sub(ea, 1n), X.sub(F.frac(x), F.frac(y)), Nat.sub(Fa, Fb), hdv, hD, hz, hovm(ea, hlta))
      +b = rc2(sa, sa, {==}, Nat.sub(Fa, Fb), Nat.sub(AG.mt(ea, Fa), AG.mt(ea, Fb)), Equal.sym(Nat, Nat.sub(AG.mt(ea, Fa), AG.mt(ea, Fb)), Nat.sub(Fa, Fb), FR.sub_cancel_r(Fa, Fb, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(ea, 0n)))))), Nat.add(1926n, Nat.sub(ea, 1n)), AG.xe(ea), xem(ea))
      Equal.trans(F.F64, F.sm_exact(sa, Nat.sub(ea, 1n), X.sub(F.frac(x), F.frac(y))), SF.round(sa, Nat.sub(Fa, Fb), Nat.add(1926n, Nat.sub(ea, 1n))), SF.round(sa, Nat.sub(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), r, b)
    case LT{}:
      +hlt = NC.lt_of_cmp(Fa, Fb, hd)
      +hle = L.subst(Nat, w => {Nat.is_le(w, SW.value(F.frac(y))) == True{} : Bool}, Fa, SW.value(F.frac(x)), Equal.sym(Nat, SW.value(F.frac(x)), Fa, hfa), L.subst(Nat, w => {Nat.is_le(Fa, w) == True{} : Bool}, Fb, SW.value(F.frac(y)), Equal.sym(Nat, SW.value(F.frac(y)), Fb, hfb), N.lt_le(Fa, Fb, hlt)))
      +hdv = Equal.trans(Nat, SW.value(X.sub(F.frac(y), F.frac(x))), Nat.sub(SW.value(F.frac(y)), SW.value(F.frac(x))), Nat.sub(Fb, Fa), WA.sub_value(F.frac(y), F.frac(x), hle), Equal.trans(Nat, Nat.sub(SW.value(F.frac(y)), SW.value(F.frac(x))), Nat.sub(Fb, SW.value(F.frac(x))), Nat.sub(Fb, Fa), Equal.cong(Nat, Nat, w => Nat.sub(w, SW.value(F.frac(x))), SW.value(F.frac(y)), Fb, hfb), Equal.cong(Nat, Nat, w => Nat.sub(Fb, w), SW.value(F.frac(x)), Fa, hfa)))
      +hD = Equal.trans(Bool, C.fits(52n, Nat.sub(Fb, Fa)), Nat.is_lt(Nat.sub(Fb, Fa), C.shift(52n, one)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.sub(Fb, Fa), C.shift(52n, one)), C.fits(52n, Nat.sub(Fb, Fa)), FR.lt_fit(52n, one, h1, Nat.sub(Fb, Fa))), N.le_lt_trans(Nat.sub(Fb, Fa), Fb, C.shift(52n, one), AG.sub_le(Fb, Fa), Equal.trans(Bool, Nat.is_lt(Fb, C.shift(52n, one)), C.fits(52n, Fb), True{}, FR.lt_fit(52n, one, h1, Fb), hFb)))
      +hz = AG.posz(Nat.sub(Fb, Fa), FR.lt_sub_pos(Fa, Fb, hlt))
      +r = AE.smx(one, h1, Bool.not(sa), Nat.sub(ea, 1n), X.sub(F.frac(y), F.frac(x)), Nat.sub(Fb, Fa), hdv, hD, hz, hovm(ea, hlta))
      +b = rc2(Bool.not(sa), sb, AG.sgn(sa, sb, hsg), Nat.sub(Fb, Fa), Nat.sub(AG.mt(ea, Fb), AG.mt(ea, Fa)), Equal.sym(Nat, Nat.sub(AG.mt(ea, Fb), AG.mt(ea, Fa)), Nat.sub(Fb, Fa), FR.sub_cancel_r(Fb, Fa, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(ea, 0n)))))), Nat.add(1926n, Nat.sub(ea, 1n)), AG.xe(ea), xem(ea))
      Equal.trans(F.F64, F.sm_exact(Bool.not(sa), Nat.sub(ea, 1n), X.sub(F.frac(y), F.frac(x))), SF.round(Bool.not(sa), Nat.sub(Fb, Fa), Nat.add(1926n, Nat.sub(ea, 1n))), SF.round(sb, Nat.sub(AG.mt(ea, Fb), AG.mt(ea, Fa)), AG.xe(ea)), r, b)

def caseEQ(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +sb: Bool, +ea: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +hlta: {Nat.is_lt(ea, 2047n) == True{} : Bool}, +sg: Bool, +hsg: {Bool.not(Bool.xor(sa, sb)) == sg : Bool}) -> {SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, ea, EQ{}), F.sm_case(x, y, sa, ea, ea, EQ{})) == SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)) : F.F64}:
  match sg:
    case True{}:
      +ha = N.is_eq_lt(ea, 2047n, hlta)
      +i1 = aeq_c(one, h1, x, y, sa, ea, Fa, Fb, hfa, hfb, hFa, hFb, ha, Nat.is_eq(ea, 0n), {==})
      +sp = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), AG.mt(ea, Fb)))), Bool.not(Bool.xor(sa, sb)), True{}, hsg)
      Equal.trans(F.F64, F.am_case(x, y, sa, ea, ea, EQ{}), SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), i1, Equal.sym(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), sp))
    case False{}:
      +ha = N.is_eq_lt(ea, 2047n, hlta)
      +i1 = Equal.cong(Bool, F.F64, t => F.sm_eq(sa, ea, F.frac(x), F.frac(y), t), Nat.is_eq(ea, 2047n), False{}, ha)
      +ec = Equal.trans(Cmp, X.cmp(F.frac(x), F.frac(y)), Nat.cmp(SW.value(F.frac(x)), SW.value(F.frac(y))), Nat.cmp(Fa, Fb), AC.cmpv(F.frac(x), F.frac(y)), Equal.trans(Cmp, Nat.cmp(SW.value(F.frac(x)), SW.value(F.frac(y))), Nat.cmp(Fa, SW.value(F.frac(y))), Nat.cmp(Fa, Fb), Equal.cong(Nat, Cmp, w => Nat.cmp(w, SW.value(F.frac(y))), SW.value(F.frac(x)), Fa, hfa), Equal.cong(Nat, Cmp, w => Nat.cmp(Fa, w), SW.value(F.frac(y)), Fb, hfb)))
      +i2 = Equal.cong(Cmp, F.F64, t => F.sm_eq2(sa, ea, F.frac(x), F.frac(y), t), X.cmp(F.frac(x), F.frac(y)), Nat.cmp(Fa, Fb), ec)
      +i3 = seq(one, h1, x, y, sa, sb, hsg, ea, Fa, Fb, hfa, hfb, hFa, hFb, hlta, Nat.cmp(Fa, Fb), {==})
      +sp1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.round(sa, Nat.add(AG.mt(ea, Fa), AG.mt(ea, Fb)), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), AG.mt(ea, Fb)))), Bool.not(Bool.xor(sa, sb)), False{}, hsg)
      +sp2 = Equal.cong(Cmp, F.F64, t => SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), t), Nat.cmp(AG.mt(ea, Fa), AG.mt(ea, Fb)), Nat.cmp(Fa, Fb), NC.cmp_addr(Fa, Fb, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(ea, 0n))))))
      +imp = Equal.trans(F.F64, F.sm_case(x, y, sa, ea, ea, EQ{}), F.sm_eq2(sa, ea, F.frac(x), F.frac(y), X.cmp(F.frac(x), F.frac(y))), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(Fa, Fb)), i1, Equal.trans(F.F64, F.sm_eq2(sa, ea, F.frac(x), F.frac(y), X.cmp(F.frac(x), F.frac(y))), F.sm_eq2(sa, ea, F.frac(x), F.frac(y), Nat.cmp(Fa, Fb)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(Fa, Fb)), i2, i3))
      +spc = Equal.trans(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(AG.mt(ea, Fa), AG.mt(ea, Fb))), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(Fa, Fb)), sp1, sp2)
      Equal.trans(F.F64, F.sm_case(x, y, sa, ea, ea, EQ{}), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(Fa, Fb)), SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), imp, Equal.sym(F.F64, SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), SF.sub_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea), Nat.cmp(Fa, Fb)), spc))

def core_c(+one: Nat, +h1: {one == 1n : Nat}, +x: F.F64, +y: F.F64, +sa: Bool, +sb: Bool, +ea: Nat, +eb: Nat, +Fa: Nat, +Fb: Nat, +hfa: {SW.value(F.frac(x)) == Fa : Nat}, +hfb: {SW.value(F.frac(y)) == Fb : Nat}, +hFa: {C.fits(52n, Fa) == True{} : Bool}, +hFb: {C.fits(52n, Fb) == True{} : Bool}, +hlta: {Nat.is_lt(ea, 2047n) == True{} : Bool}, +hltb: {Nat.is_lt(eb, 2047n) == True{} : Bool}, +sg: Bool, +hsg: {Bool.not(Bool.xor(sa, sb)) == sg : Bool}, +c: Cmp, +hc: {Nat.cmp(ea, eb) == c : Cmp}) -> {SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, eb, c), F.sm_case(x, y, sa, ea, eb, c)) == SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))) : F.F64}:
  match c:
    case LT{}:
      +hlt = NC.lt_of_cmp(ea, eb, hc)
      +r = caseLT(one, h1, x, y, sa, sb, ea, eb, Fa, Fb, hfa, hfb, hFa, hFb, N.is_eq_lt(eb, 2047n, hltb), hlt, sg, hsg)
      Equal.trans(F.F64, SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, eb, LT{}), F.sm_case(x, y, sa, ea, eb, LT{})), SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), r, Equal.sym(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), SF.add_mag(sa, AG.mt(ea, Fa), sb, C.shift(Nat.sub(AG.xe(eb), AG.xe(ea)), AG.mt(eb, Fb)), AG.xe(ea)), spec_lt(sa, sb, ea, eb, Fa, Fb, xe_le(ea, eb, hlt))))
    case GT{}:
      +hgt = NC.lt_of_gt(ea, eb, hc)
      +r = caseGT(one, h1, x, y, sa, sb, ea, eb, Fa, Fb, hfa, hfb, hFa, hFb, N.is_eq_lt(ea, 2047n, hlta), hgt, sg, hsg)
      Equal.trans(F.F64, SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, eb, GT{}), F.sm_case(x, y, sa, ea, eb, GT{})), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), r, Equal.sym(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(eb), Nat.min(AG.xe(ea), AG.xe(eb))), AG.mt(eb, Fb)), Nat.min(AG.xe(ea), AG.xe(eb))), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), AG.xe(eb)), AG.mt(ea, Fa)), sb, AG.mt(eb, Fb), AG.xe(eb)), spec_gt(sa, sb, ea, eb, Fa, Fb, xe_le(eb, ea, hgt))))
    case EQ{}:
      +e = NC.eq_of_cmp(ea, eb, hc)
      +r = caseEQ(one, h1, x, y, sa, sb, ea, Fa, Fb, hfa, hfb, hFa, hFb, hlta, sg, hsg)
      +p = Equal.trans(F.F64, SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, ea, EQ{}), F.sm_case(x, y, sa, ea, ea, EQ{})), SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fb)), Nat.min(AG.xe(ea), AG.xe(ea))), r, Equal.sym(F.F64, SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(ea))), AG.mt(ea, Fb)), Nat.min(AG.xe(ea), AG.xe(ea))), SF.add_mag(sa, AG.mt(ea, Fa), sb, AG.mt(ea, Fb), AG.xe(ea)), spec_eq(sa, sb, ea, Fa, Fb)))
      L.subst(Nat, w => {SF.pick(F.F64, sg, F.am_case(x, y, sa, ea, w, EQ{}), F.sm_case(x, y, sa, ea, w, EQ{})) == SF.add_mag(sa, C.shift(Nat.sub(AG.xe(ea), Nat.min(AG.xe(ea), AG.xe(w))), AG.mt(ea, Fa)), sb, C.shift(Nat.sub(AG.xe(w), Nat.min(AG.xe(ea), AG.xe(w))), AG.mt(w, Fb)), Nat.min(AG.xe(ea), AG.xe(w))) : F.F64}, ea, eb, e, p)

# F.add on finite operands is the spec's add_fin
def afin(+xl: U32, +xh: U32, +yl: U32, +yh: U32, +ha: {Nat.is_lt(SF.efield(F.Bits{xl, xh}), 2047n) == True{} : Bool}, +hb: {Nat.is_lt(SF.efield(F.Bits{yl, yh}), 2047n) == True{} : Bool}) -> {F.add(F.Bits{xl, xh}, F.Bits{yl, yh}) == SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}) : F.F64}:
  +e0 = ap(F.Bits{xl, xh}, F.Bits{yl, yh}, Bool.not(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh}))))
  +c1 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, Bool.not(Bool.xor(t, F.signbit(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, t, F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, t, F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), F.signbit(F.Bits{xl, xh}), SF.sign(F.Bits{xl, xh}), FB.signbit_value(F.Bits{xl, xh}))
  +c2 = Equal.cong(Bool, F.F64, t => SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), t)), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), F.signbit(F.Bits{yl, yh}), SF.sign(F.Bits{yl, yh}), FB.signbit_value(F.Bits{yl, yh}))
  +c3 = Equal.cong(Nat, F.F64, t => SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), t, F.exp_field(F.Bits{yl, yh}), Nat.cmp(t, F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), t, F.exp_field(F.Bits{yl, yh}), Nat.cmp(t, F.exp_field(F.Bits{yl, yh})))), F.exp_field(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), hea(xl, xh))
  +c4 = Equal.cong(Nat, F.F64, t => SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), t, Nat.cmp(SF.efield(F.Bits{xl, xh}), t)), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), t, Nat.cmp(SF.efield(F.Bits{xl, xh}), t))), F.exp_field(F.Bits{yl, yh}), SF.efield(F.Bits{yl, yh}), hea(yl, yh))
  +r = core_c(1n, {==}, F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}), SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), SF.frac(F.Bits{xl, xh}), SF.frac(F.Bits{yl, yh}), hfr(xl, xh), hfr(yl, yh), hF(xl, xh), hF(yl, yh), ha, hb, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), {==}, Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})), {==})
  Equal.trans(F.F64, F.add(F.Bits{xl, xh}, F.Bits{yl, yh}), SF.pick(F.F64, Bool.not(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}), e0, Equal.trans(F.F64, SF.pick(F.F64, Bool.not(Bool.xor(F.signbit(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, F.signbit(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}), c1, Equal.trans(F.F64, SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), F.signbit(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}), c2, Equal.trans(F.F64, SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(F.exp_field(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}), c3, Equal.trans(F.F64, SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), F.exp_field(F.Bits{yl, yh})))), SF.pick(F.F64, Bool.not(Bool.xor(SF.sign(F.Bits{xl, xh}), SF.sign(F.Bits{yl, yh}))), F.am_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}))), F.sm_case(F.Bits{xl, xh}, F.Bits{yl, yh}, SF.sign(F.Bits{xl, xh}), SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh}), Nat.cmp(SF.efield(F.Bits{xl, xh}), SF.efield(F.Bits{yl, yh})))), SF.add_fin(F.Bits{xl, xh}, F.Bits{yl, yh}), c4, r)))))
