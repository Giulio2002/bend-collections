import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ../../lib/word.bend as WD
import ./w64sh.bend as SH
import ./u32laws.bend as LW
import ./natcmp.bend as NC
import ./f64bits.bend as FB
import ./f64cmp.bend as FC
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64norm.bend as NM
import ./f64mexp.bend as EX
import ./f64mul.bend as MU

# Mul.value of spec/math/f64.bend: the special-case analysis.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- fields of the operands ----

def hea(+xl: U32, +xh: U32) -> {F.exp_field(F.Bits{xl, xh}) == SF.efield(F.Bits{xl, xh}) : Nat}:
  FB.ef_g(1n, {==}, xh, 1048576, {==}, 2047, {==})

def mimpl(+s: Bool, +a1: Bool, +b1: Bool, +c1: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +r: F.F64) -> F.F64:
  SF.pick(F.F64, a1, SF.pick(F.F64, Bool.or(Bool.or(Bool.not(b1), Bool.and(a2, Bool.not(b2))), Bool.and(c2, b2)), F.nan(), F.inf(s)), SF.pick(F.F64, a2, SF.pick(F.F64, Bool.or(Bool.not(b2), Bool.and(c1, b1)), F.nan(), F.inf(s)), SF.pick(F.F64, Bool.or(Bool.and(c1, b1), Bool.and(c2, b2)), F.zero(s), r)))

def mspec(+s: Bool, +a1: Bool, +b1: Bool, +c1: Bool, +a2: Bool, +b2: Bool, +c2: Bool, +r: F.F64) -> F.F64:
  SF.pick(F.F64, Bool.or(Bool.and(a1, Bool.not(b1)), Bool.and(a2, Bool.not(b2))), SF.qnan(), SF.pick(F.F64, Bool.or(Bool.and(a1, b1), Bool.and(a2, b2)), SF.pick(F.F64, Bool.or(Bool.and(c1, b1), Bool.and(c2, b2)), SF.qnan(), SF.inf(s)), r))

def ion(+s: Bool, +b: Bool) -> {F.inf_or_nan(s, b) == SF.pick(F.F64, b, F.nan(), F.inf(s)) : F.F64}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def zero_v(+s: Bool) -> {F.zero(s) == SF.zero(s) : F.F64}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def ne2047(+E: Nat) -> {Bool.and(Nat.is_eq(E, 2047n), Nat.is_eq(E, 0n)) == False{} : Bool}:
  match E:
    case 0n:
      {==}
    case 1n+ +p:
      FR.and_f(Nat.is_eq(1n+p, 2047n))

def sh3(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +z: Bool) -> {F.mul_z(s, ea, fa, eb, fb, z) == SF.pick(F.F64, z, F.zero(s), F.mul_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb))) : F.F64}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def sh2(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +t: Bool) -> {F.mul_b(s, ea, fa, eb, fb, t) == SF.pick(F.F64, t, SF.pick(F.F64, Bool.or(Bool.not(X.is_zero(fb)), Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa))), F.nan(), F.inf(s)), SF.pick(F.F64, Bool.or(Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), Bool.and(Nat.is_eq(eb, 0n), X.is_zero(fb))), F.zero(s), F.mul_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb)))) : F.F64}:
  match t:
    case True{}:
      ion(s, Bool.or(Bool.not(X.is_zero(fb)), Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa))))
    case False{}:
      sh3(s, ea, fa, eb, fb, Bool.or(Bool.and(Nat.is_eq(ea, 0n), X.is_zero(fa)), Bool.and(Nat.is_eq(eb, 0n), X.is_zero(fb))))

def sh1(+s: Bool, +ea: Nat, +fa: WU.U64, +eb: Nat, +fb: WU.U64, +t: Bool) -> {F.mul_cls(s, ea, fa, eb, fb, t) == mimpl(s, t, X.is_zero(fa), Nat.is_eq(ea, 0n), Nat.is_eq(eb, 2047n), X.is_zero(fb), Nat.is_eq(eb, 0n), F.mul_n(s, F.norm_e(ea, fa), F.norm_f(ea, fa), F.norm_e(eb, fb), F.norm_f(eb, fb))) : F.F64}:
  match t:
    case True{}:
      ion(s, Bool.or(Bool.or(Bool.not(X.is_zero(fa)), Bool.and(Nat.is_eq(eb, 2047n), Bool.not(X.is_zero(fb)))), Bool.and(Nat.is_eq(eb, 0n), X.is_zero(fb))))
    case False{}:
      sh2(s, ea, fa, eb, fb, Nat.is_eq(eb, 2047n))

def mant0(+xl: U32, +xh: U32, +hc: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n) == True{} : Bool}, +hb: {Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n) == True{} : Bool}) -> {SF.mant(F.Bits{xl, xh}) == 0n : Nat}:
  +e1 = Equal.cong(Bool, Nat, t => Nat.add(SF.frac(F.Bits{xl, xh}), C.shift(52n, SF.b2n(Bool.not(t)))), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n), True{}, hc)
  Equal.trans(Nat, SF.mant(F.Bits{xl, xh}), Nat.add(SF.frac(F.Bits{xl, xh}), 0n), 0n, e1, Equal.trans(Nat, Nat.add(SF.frac(F.Bits{xl, xh}), 0n), SF.frac(F.Bits{xl, xh}), 0n, N.add_zero(SF.frac(F.Bits{xl, xh})), N.eq_from_is_eq(SF.frac(F.Bits{xl, xh}), 0n, hb)))

def zx(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +hc: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n) == True{} : Bool}, +hb: {Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n) == True{} : Bool}) -> {F.zero(s) == SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())) : F.F64}:
  Equal.trans(F.F64, F.zero(s), SF.zero(s), SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), zero_v(s), Equal.sym(F.F64, SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), SF.zero(s), Equal.cong(Nat, F.F64, z => SF.round(s, Nat.mul(z, SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), SF.mant(F.Bits{xl, xh}), 0n, mant0(xl, xh, hc, hb))))

def zy(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +hc: {Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n) == True{} : Bool}, +hb: {Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n) == True{} : Bool}) -> {F.zero(s) == SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())) : F.F64}:
  +em = Equal.trans(Nat, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.mul(SF.mant(F.Bits{xl, xh}), 0n), 0n, Equal.cong(Nat, Nat, z => Nat.mul(SF.mant(F.Bits{xl, xh}), z), SF.mant(F.Bits{yl, yh}), 0n, mant0(yl, yh, hc, hb)), NA.mul_zero(SF.mant(F.Bits{xl, xh})))
  Equal.trans(F.F64, F.zero(s), SF.zero(s), SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), zero_v(s), Equal.sym(F.F64, SF.round(s, Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), SF.zero(s), Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.sub(Nat.add(SF.xexp(F.Bits{xl, xh}), SF.xexp(F.Bits{yl, yh})), SF.zb())), Nat.mul(SF.mant(F.Bits{xl, xh}), SF.mant(F.Bits{yl, yh})), 0n, em)))

def mcase(+s: Bool, +xl: U32, +xh: U32, +yl: U32, +yh: U32, +r1: F.F64, +r2: F.F64, +a1: Bool, +ha1: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n) == a1 : Bool}, +b1: Bool, +hb1: {Nat.is_eq(SF.frac(F.Bits{xl, xh}), 0n) == b1 : Bool}, +c1: Bool, +hc1: {Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n) == c1 : Bool}, +a2: Bool, +ha2: {Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n) == a2 : Bool}, +b2: Bool, +hb2: {Nat.is_eq(SF.frac(F.Bits{yl, yh}), 0n) == b2 : Bool}, +c2: Bool, +hc2: {Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n) == c2 : Bool}, +hR: {SF.pick(F.F64, Bool.or(Bool.or(a1, a2), Bool.or(Bool.and(c1, b1), Bool.and(c2, b2))), r2, r1) == r2 : F.F64}, +hZ: {SF.pick(F.F64, Bool.or(Bool.or(a1, a2), Bool.not(Bool.or(Bool.and(c1, b1), Bool.and(c2, b2)))), r2, F.zero(s)) == r2 : F.F64}) -> {mimpl(s, a1, b1, c1, a2, b2, c2, r1) == mspec(s, a1, b1, c1, a2, b2, c2, r2) : F.F64}:
  match a1 b1 c1 a2 b2 c2:
    case True{} True{} True{} True{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, True{}, True{}, True{}, r1) == mspec(s, True{}, True{}, True{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} True{} True{} False{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, True{}, True{}, False{}, r1) == mspec(s, True{}, True{}, True{}, True{}, True{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} True{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, True{}, False{}, True{}, r1) == mspec(s, True{}, True{}, True{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} True{} False{} False{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, True{}, False{}, False{}, r1) == mspec(s, True{}, True{}, True{}, True{}, False{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} False{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, False{}, True{}, True{}, r1) == mspec(s, True{}, True{}, True{}, False{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} False{} True{} False{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, False{}, True{}, False{}, r1) == mspec(s, True{}, True{}, True{}, False{}, True{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} False{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, False{}, False{}, True{}, r1) == mspec(s, True{}, True{}, True{}, False{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} True{} False{} False{} False{}:
      Empty.absurd({mimpl(s, True{}, True{}, True{}, False{}, False{}, False{}, r1) == mspec(s, True{}, True{}, True{}, False{}, False{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} True{} False{} True{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, False{}, True{}, True{}, True{}, r1) == mspec(s, True{}, True{}, False{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case True{} True{} False{} True{} True{} False{}:
      FR.inf_v(s)
    case True{} True{} False{} True{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, True{}, False{}, True{}, False{}, True{}, r1) == mspec(s, True{}, True{}, False{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      FR.inf_v(s)
    case True{} True{} False{} False{} False{} True{}:
      FR.inf_v(s)
    case True{} True{} False{} False{} False{} False{}:
      FR.inf_v(s)
    case True{} False{} True{} True{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, True{}, True{}, True{}, r1) == mspec(s, True{}, False{}, True{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} True{} True{} False{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, True{}, True{}, False{}, r1) == mspec(s, True{}, False{}, True{}, True{}, True{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} True{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, True{}, False{}, True{}, r1) == mspec(s, True{}, False{}, True{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} True{} False{} False{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, True{}, False{}, False{}, r1) == mspec(s, True{}, False{}, True{}, True{}, False{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} False{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, False{}, True{}, True{}, r1) == mspec(s, True{}, False{}, True{}, False{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} False{} True{} False{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, False{}, True{}, False{}, r1) == mspec(s, True{}, False{}, True{}, False{}, True{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} False{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, False{}, False{}, True{}, r1) == mspec(s, True{}, False{}, True{}, False{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} True{} False{} False{} False{}:
      Empty.absurd({mimpl(s, True{}, False{}, True{}, False{}, False{}, False{}, r1) == mspec(s, True{}, False{}, True{}, False{}, False{}, False{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{xl, xh}), 0n)), Nat.is_eq(SF.efield(F.Bits{xl, xh}), 2047n), True{}, ha1), hc1)), ne2047(SF.efield(F.Bits{xl, xh})))))
    case True{} False{} False{} True{} True{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, False{}, True{}, True{}, True{}, r1) == mspec(s, True{}, False{}, False{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      Empty.absurd({mimpl(s, True{}, False{}, False{}, True{}, False{}, True{}, r1) == mspec(s, True{}, False{}, False{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
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
      Empty.absurd({mimpl(s, False{}, True{}, True{}, True{}, True{}, True{}, r1) == mspec(s, False{}, True{}, True{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      Empty.absurd({mimpl(s, False{}, True{}, True{}, True{}, False{}, True{}, r1) == mspec(s, False{}, True{}, True{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      hZ
    case False{} True{} True{} False{} True{} False{}:
      hZ
    case False{} True{} True{} False{} False{} True{}:
      hZ
    case False{} True{} True{} False{} False{} False{}:
      hZ
    case False{} True{} False{} True{} True{} True{}:
      Empty.absurd({mimpl(s, False{}, True{}, False{}, True{}, True{}, True{}, r1) == mspec(s, False{}, True{}, False{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} True{} False{} True{} True{} False{}:
      FR.inf_v(s)
    case False{} True{} False{} True{} False{} True{}:
      Empty.absurd({mimpl(s, False{}, True{}, False{}, True{}, False{}, True{}, r1) == mspec(s, False{}, True{}, False{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      hZ
    case False{} True{} False{} False{} True{} False{}:
      hR
    case False{} True{} False{} False{} False{} True{}:
      hR
    case False{} True{} False{} False{} False{} False{}:
      hR
    case False{} False{} True{} True{} True{} True{}:
      Empty.absurd({mimpl(s, False{}, False{}, True{}, True{}, True{}, True{}, r1) == mspec(s, False{}, False{}, True{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} False{} True{} True{} True{} False{}:
      FR.inf_v(s)
    case False{} False{} True{} True{} False{} True{}:
      Empty.absurd({mimpl(s, False{}, False{}, True{}, True{}, False{}, True{}, r1) == mspec(s, False{}, False{}, True{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      hZ
    case False{} False{} True{} False{} True{} False{}:
      hR
    case False{} False{} True{} False{} False{} True{}:
      hR
    case False{} False{} True{} False{} False{} False{}:
      hR
    case False{} False{} False{} True{} True{} True{}:
      Empty.absurd({mimpl(s, False{}, False{}, False{}, True{}, True{}, True{}, r1) == mspec(s, False{}, False{}, False{}, True{}, True{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} False{} False{} True{} True{} False{}:
      FR.inf_v(s)
    case False{} False{} False{} True{} False{} True{}:
      Empty.absurd({mimpl(s, False{}, False{}, False{}, True{}, False{}, True{}, r1) == mspec(s, False{}, False{}, False{}, True{}, False{}, True{}, r2) : F.F64}, LW.true_ne_false(Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.trans(Bool, Bool.and(Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Bool.and(True{}, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), True{}, Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_eq(SF.efield(F.Bits{yl, yh}), 0n)), Nat.is_eq(SF.efield(F.Bits{yl, yh}), 2047n), True{}, ha2), hc2)), ne2047(SF.efield(F.Bits{yl, yh})))))
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      hZ
    case False{} False{} False{} False{} True{} False{}:
      hR
    case False{} False{} False{} False{} False{} True{}:
      hR
    case False{} False{} False{} False{} False{} False{}:
      hR

