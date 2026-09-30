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

# three-way disjunction congruence over abstract Booleans (book-less: the
# checker never unfolds the comparisons it is applied to)
def or3(+x1: Bool, +x2: Bool, +x3: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +h1: {x1 == y1 : Bool}, +h2: {x2 == y2 : Bool}, +h3: {x3 == y3 : Bool}) -> {Bool.or(Bool.or(x1, x2), x3) == Bool.or(Bool.or(y1, y2), y3) : Bool}:
  +c1 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(t, x2), x3), x1, y1, h1)
  +c2 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(y1, t), x3), x2, y2, h2)
  +c3 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(y1, y2), t), x3, y3, h3)
  Equal.trans(Bool, Bool.or(Bool.or(x1, x2), x3), Bool.or(Bool.or(y1, x2), x3), Bool.or(Bool.or(y1, y2), y3), c1, Equal.trans(Bool, Bool.or(Bool.or(y1, x2), x3), Bool.or(Bool.or(y1, y2), x3), Bool.or(Bool.or(y1, y2), y3), c2, c3))

# d <= |r * x| on the implementation is le_s against the spec's |r * x|
def lek(+d: F.F64, +r: F.F64, +x: F.F64) -> {F.le(d, F.abs(F.mul(r, x))) == SF.le_s(d, SF.fabs(SF.mul(r, x))) : Bool}:
  +R = SF.fabs(SF.mul(r, x))
  Equal.trans(Bool, F.le(d, F.abs(F.mul(r, x))), F.le(d, R), SF.le_s(d, R), Equal.cong(F.F64, Bool, t => F.le(d, t), F.abs(F.mul(r, x)), R, fabs_v(F.mul(r, x), SF.mul(r, x), MV.mul_value(r, x))), FC.le_value(d, R))

def icd_t(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +d: F.F64) -> {F.ic_d(a, b, rel, at, d) == SF.ic_near(a, b, rel, at, d) : Bool}:
  or3(F.le(d, F.abs(F.mul(rel, b))), F.le(d, F.abs(F.mul(rel, a))), F.le(d, at), SF.le_s(d, SF.fabs(SF.mul(rel, b))), SF.le_s(d, SF.fabs(SF.mul(rel, a))), SF.le_s(d, at), lek(d, rel, b), lek(d, rel, a), FC.le_value(d, at))

def icd(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> {F.ic_d(a, b, rel, at, F.abs(F.sub(b, a))) == SF.ic_near(a, b, rel, at, D(a, b)) : Bool}:
  +d = D(a, b)
  +e0 = Equal.cong(F.F64, Bool, t => F.ic_d(a, b, rel, at, t), F.abs(F.sub(b, a)), d, fabs_v(F.sub(b, a), SF.add(b, SF.neg(a)), AV.sub_value(b, a)))
  Equal.trans(Bool, F.ic_d(a, b, rel, at, F.abs(F.sub(b, a))), F.ic_d(a, b, rel, at, d), SF.ic_near(a, b, rel, at, d), e0, icd_t(a, b, rel, at, d))

# one unfolding step each, stated so the checker compares syntactically
def ii_f(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> {F.ic_inf(a, b, rel, at, False{}) == F.ic_d(a, b, rel, at, F.abs(F.sub(b, a))) : Bool}:
  {==}

def pk_f(+x: Bool, +y: Bool) -> {SF.pick(Bool, False{}, x, y) == y : Bool}:
  {==}

def iinf(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +big: Bool) -> {F.ic_inf(a, b, rel, at, big) == SF.pick(Bool, big, False{}, SF.ic_near(a, b, rel, at, D(a, b))) : Bool}:
  match big:
    case True{}:
      {==}
    case False{}:
      +u = F.ic_d(a, b, rel, at, F.abs(F.sub(b, a)))
      +n = SF.ic_near(a, b, rel, at, D(a, b))
      Equal.trans(Bool, F.ic_inf(a, b, rel, at, False{}), u, SF.pick(Bool, False{}, False{}, n), ii_f(a, b, rel, at), Equal.trans(Bool, u, n, SF.pick(Bool, False{}, False{}, n), icd(a, b, rel, at), Equal.sym(Bool, SF.pick(Bool, False{}, False{}, n), n, pk_f(False{}, n))))

def ie_f(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64) -> {F.ic_eq(a, b, rel, at, False{}) == F.ic_inf(a, b, rel, at, Bool.or(F.is_inf(a), F.is_inf(b))) : Bool}:
  {==}

def ieq(+a: F.F64, +b: F.F64, +rel: F.F64, +at: F.F64, +e: Bool) -> {F.ic_eq(a, b, rel, at, e) == SF.pick(Bool, e, True{}, SF.pick(Bool, Bool.or(SF.is_inf(a), SF.is_inf(b)), False{}, SF.ic_near(a, b, rel, at, D(a, b)))) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      +e1 = Equal.cong(Bool, Bool, t => F.ic_inf(a, b, rel, at, Bool.or(t, F.is_inf(b))), F.is_inf(a), SF.is_inf(a), FB.is_inf_value(a))
      +e2 = Equal.cong(Bool, Bool, t => F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), t)), F.is_inf(b), SF.is_inf(b), FB.is_inf_value(b))
      +b0 = F.ic_inf(a, b, rel, at, Bool.or(F.is_inf(a), F.is_inf(b)))
      +b1 = F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), F.is_inf(b)))
      +b2 = F.ic_inf(a, b, rel, at, Bool.or(SF.is_inf(a), SF.is_inf(b)))
      +b3 = SF.pick(Bool, Bool.or(SF.is_inf(a), SF.is_inf(b)), False{}, SF.ic_near(a, b, rel, at, D(a, b)))
      +g = SF.pick(Bool, False{}, True{}, b3)
      Equal.trans(Bool, F.ic_eq(a, b, rel, at, False{}), b0, g, ie_f(a, b, rel, at), Equal.trans(Bool, b0, b1, g, e1, Equal.trans(Bool, b1, b2, g, e2, Equal.trans(Bool, b2, b3, g, iinf(a, b, rel, at, Bool.or(SF.is_inf(a), SF.is_inf(b))), Equal.sym(Bool, g, b3, pk_f(True{}, b3))))))

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
