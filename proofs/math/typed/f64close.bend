import Base
import ../../../spec/math/f64.bend as SF
import ../../../src/math/f64.bend as F
import ../../../src/math/num.bend as NE
import ./f64bits.bend as FB
import ./f64cmp.bend as FC
import ./f64addv.bend as AV
import ./f64mulv.bend as MV

# isclose (python_style_math_stdlib_design.pdf 4.4; CPython's
# math_isclose_impl): IsClose.value. The implementation is CPython's
# algorithm on the proved operations, so each step is a proved clause:
# Lt / Le / Eq (f64cmp), Sub and Mul (f64addv, f64mulv), Abs and IsInf
# (f64bits).

def fabs_v(+z: F.F64, +z2: F.F64, +h: {z == z2 : F.F64}) -> {F.abs(z) == SF.fabs(z2) : F.F64}:
  Equal.trans(F.F64, F.abs(z), F.abs(z2), SF.fabs(z2), Equal.cong(F.F64, F.F64, t => F.abs(t), z, z2, h), FB.abs_value(z2))

def D(+a: F.F64, +b: F.F64) -> F.F64:
  SF.fabs(SF.add(b, SF.neg(a)))

def icd(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> {F.ic_d(a, b, rel, at, F.abs(F.sub(b, a))) == SF.ic_near(a, b, rel, at, D(a, b)) : Bool}:
  +d = D(a, b)
  +RB = SF.fabs(SF.mul(rel, b))
  +RA = SF.fabs(SF.mul(rel, a))
  +e0 = Equal.cong(F.F64, Bool, t => F.ic_d(a, b, rel, at, t), F.abs(F.sub(b, a)), d, fabs_v(F.sub(b, a), SF.add(b, SF.neg(a)), AV.sub_value(b, a)))
  +e1 = Equal.cong(F.F64, Bool, t => Bool.or(Bool.or(F.le(d, t), F.le(d, F.abs(F.mul(rel, a)))), F.le(d, at)), F.abs(F.mul(rel, b)), RB, fabs_v(F.mul(rel, b), SF.mul(rel, b), MV.mul_value(rel, b)))
  +e2 = Equal.cong(F.F64, Bool, t => Bool.or(Bool.or(F.le(d, RB), F.le(d, t)), F.le(d, at)), F.abs(F.mul(rel, a)), RA, fabs_v(F.mul(rel, a), SF.mul(rel, a), MV.mul_value(rel, a)))
  +e3 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(t, F.le(d, RA)), F.le(d, at)), F.le(d, RB), SF.le_s(d, RB), FC.le_value(d, RB))
  +e4 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(SF.le_s(d, RB), t), F.le(d, at)), F.le(d, RA), SF.le_s(d, RA), FC.le_value(d, RA))
  +e5 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(SF.le_s(d, RB), SF.le_s(d, RA)), t), F.le(d, at), SF.le_s(d, at), FC.le_value(d, at))
  +b0 = F.ic_d(a, b, rel, at, F.abs(F.sub(b, a)))
  +b1 = Bool.or(Bool.or(F.le(d, F.abs(F.mul(rel, b))), F.le(d, F.abs(F.mul(rel, a)))), F.le(d, at))
  +b2 = Bool.or(Bool.or(F.le(d, RB), F.le(d, F.abs(F.mul(rel, a)))), F.le(d, at))
  +b3 = Bool.or(Bool.or(F.le(d, RB), F.le(d, RA)), F.le(d, at))
  +b4 = Bool.or(Bool.or(SF.le_s(d, RB), F.le(d, RA)), F.le(d, at))
  +b5 = Bool.or(Bool.or(SF.le_s(d, RB), SF.le_s(d, RA)), F.le(d, at))
  +b6 = SF.ic_near(a, b, rel, at, d)
  Equal.trans(Bool, b0, b1, b6, e0, Equal.trans(Bool, b1, b2, b6, e1, Equal.trans(Bool, b2, b3, b6, e2, Equal.trans(Bool, b3, b4, b6, e3, Equal.trans(Bool, b4, b5, b6, e4, e5)))))

def iinf(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +big: Bool) -> {F.ic_inf(a, b, rel, at, big) == SF.pick(Bool, big, False{}, SF.ic_near(a, b, rel, at, D(a, b))) : Bool}:
  match big:
    case True{}:
      {==}
    case False{}:
      icd(a, b, rel, at)

def ieq(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +e: Bool) -> {F.ic_eq(a, b, rel, at, e) == SF.pick(Bool, e, True{}, SF.pick(Bool, Bool.or(SF.is_inf(a), SF.is_inf(b)), False{}, SF.ic_near(a, b, rel, at, D(a, b)))) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      +e1 = Equal.cong(Bool, Bool, t => F.ic_inf(a, b, rel, at, Bool.or(t, F.is_inf(b))), F.is_inf(a), SF.is_inf(a), FB.is_inf_value(a))
      +e2 = Equal.cong(Bool, Bool, t => F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), t)), F.is_inf(b), SF.is_inf(b), FB.is_inf_value(b))
      +b1 = F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), F.is_inf(b)))
      +b2 = F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), SF.is_inf(b)))
      +b3 = SF.pick(Bool, Bool.or(SF.is_inf(a), SF.is_inf(b)), False{}, SF.ic_near(a, b, rel, at, D(a, b)))
      Equal.trans(Bool, F.ic_inf(a, b, rel, at, Bool.or(F.is_inf(a), F.is_inf(b))), b1, b3, e1, Equal.trans(Bool, b1, b2, b3, e2, iinf(a, b, rel, at, Bool.or(SF.is_inf(a), SF.is_inf(b)))))

def NEAR(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> Bool:
  SF.pick(Bool, SF.eq_s(a, b), True{}, SF.pick(Bool, Bool.or(SF.is_inf(a), SF.is_inf(b)), False{}, SF.ic_near(a, b, rel, at, D(a, b))))

def itol(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +bad: Bool) -> {F.ic_tol(a, b, rel, at, bad) == SF.pick(Result<&2, &2, NE.NumError, Bool>, bad, Fail{NE.BadDomain{}}, Done{NEAR(a, b, rel, at)}) : Result<&2, &2, NE.NumError, Bool>}:
  match bad:
    case True{}:
      {==}
    case False{}:
      +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Bool>, t => Done{F.ic_eq(a, b, rel, at, t)}, F.eq(a, b), SF.eq_s(a, b), FC.eq_value(a, b))
      +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Bool>, t => Done{t}, F.ic_eq(a, b, rel, at, SF.eq_s(a, b)), NEAR(a, b, rel, at), ieq(a, b, rel, at, SF.eq_s(a, b)))
      Equal.trans(Result<&2, &2, NE.NumError, Bool>, Done{F.ic_eq(a, b, rel, at, F.eq(a, b))}, Done{F.ic_eq(a, b, rel, at, SF.eq_s(a, b))}, Done{NEAR(a, b, rel, at)}, e1, e2)

def isclose_value(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> SF.IsClose.value(a, b, rel, at):
  +z = F.zero(False{})
  +e1 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Bool>, t => F.ic_tol(a, b, rel, at, Bool.or(t, F.lt(at, z))), F.lt(rel, z), SF.lt_s(rel, z), FC.lt_value(rel, z))
  +e2 = Equal.cong(Bool, Result<&2, &2, NE.NumError, Bool>, t => F.ic_tol(a, b, rel, at, Bool.or(SF.lt_s(rel, z), t)), F.lt(at, z), SF.lt_s(at, z), FC.lt_value(at, z))
  +r1 = F.ic_tol(a, b, rel, at, Bool.or(SF.lt_s(rel, z), F.lt(at, z)))
  +r2 = F.ic_tol(a, b, rel, at, Bool.or(SF.lt_s(rel, z), SF.lt_s(at, z)))
  Equal.trans(Result<&2, &2, NE.NumError, Bool>, F.isclose(a, b, rel, at), r1, SF.isclose(a, b, rel, at), e1, Equal.trans(Result<&2, &2, NE.NumError, Bool>, r1, r2, SF.isclose(a, b, rel, at), e2, itol(a, b, rel, at, Bool.or(SF.lt_s(rel, z), SF.lt_s(at, z)))))
