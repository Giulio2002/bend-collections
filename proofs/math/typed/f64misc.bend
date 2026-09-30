import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ./width.bend as WW
import ./f64bits.bend as FB
import ./f64cmp.bend as FC
import ./f64tools.bend as T

# The conversion from unsigned integers, ulp, the classification predicates
# and the bit casts of spec/math/f64.bend: OfU64.value, OfU32.value,
# Ulp.value, IsNormal.value, IsSubnormal.value, Bits.value, Bits.roundtrip
# and Bits.inverse. of_u64 and ulp are round_w on an exact integer at a scale
# (f64tools.rw_value: Flocq's round_NE, Boldo and Melquiond 2011), the rest
# read the IEEE 754-2019 3.4 fields (f64bits, f64cmp.magQ).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- of_u64, of_u32 ----

def of_u64_value(+w: WU.U64) -> SF.OfU64.value(w):
  T.rw_value(False{}, 3000n, w, {==})

def of_u32_value(+u: U32) -> SF.OfU32.value(u):
  +e1 = T.rw_value(False{}, 3000n, WU.U64{u, 0}, {==})
  +e2 = Equal.cong(Nat, F.F64, t => SF.round(False{}, t, 3000n), Nat.add(v(u), 0n), v(u), N.add_zero(v(u)))
  Equal.trans(F.F64, F.of_u32(u), SF.round(False{}, Nat.add(v(u), 0n), 3000n), SF.round(False{}, v(u), SF.zb()), e1, e2)

# ---- ulp ----

def ulp_c(+x: F.F64, +t: Bool, +z: Bool, +hz: {X.is_zero(F.frac(x)) == z : Bool}) -> {F.ulp_cls(x, t) == SF.pick(F.F64, Bool.and(t, Bool.not(z)), SF.qnan(), SF.pick(F.F64, Bool.and(t, z), SF.inf(False{}), SF.round(False{}, 1n, SF.xexp(x)))) : F.F64}:
  match t z:
    case True{} True{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(F.inf(False{}), Bool.not(b)), X.is_zero(F.frac(x)), True{}, hz)
    case True{} False{}:
      Equal.cong(Bool, F.F64, b => F.nan_or(F.inf(False{}), Bool.not(b)), X.is_zero(F.frac(x)), False{}, hz)
    case False{} _:
      +e1 = T.rw_value(False{}, F.dexp(x), WU.U64{1, 0}, T.dexp_ge(x))
      +e2 = Equal.cong(Nat, F.F64, t => SF.round(False{}, 1n, t), F.dexp(x), SF.xexp(x), T.dexp_value(x))
      Equal.trans(F.F64, F.round_w(False{}, F.dexp(x), WU.U64{1, 0}), SF.round(False{}, 1n, F.dexp(x)), SF.round(False{}, 1n, SF.xexp(x)), e1, e2)

def ulp_value(+x: F.F64) -> SF.Ulp.value(x):
  +e1 = Equal.cong(Nat, F.F64, t => F.ulp_cls(x, Nat.is_eq(t, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))
  Equal.trans(F.F64, F.ulp(x), F.ulp_cls(x, Nat.is_eq(SF.efield(x), 2047n)), SF.pick(F.F64, SF.is_nan(x), SF.qnan(), SF.pick(F.F64, SF.is_inf(x), SF.inf(False{}), SF.round(False{}, 1n, SF.xexp(x)))), e1, ulp_c(x, Nat.is_eq(SF.efield(x), 2047n), Nat.is_eq(SF.frac(x), 0n), T.fz(x)))

# ---- is_normal, is_subnormal ----

def is_normal_value(+x: F.F64) -> SF.IsNormal.value(x):
  Equal.cong(Nat, Bool, t => Bool.and(Bool.not(Nat.is_eq(t, 0n)), Nat.is_lt(t, 2047n)), F.exp_field(x), SF.efield(x), T.ea(x))

def is_subnormal_value(+x: F.F64) -> SF.IsSubnormal.value(x):
  +e1 = Equal.cong(Nat, Bool, t => Bool.and(Nat.is_eq(t, 0n), Bool.not(X.is_zero(F.frac(x)))), F.exp_field(x), SF.efield(x), T.ea(x))
  +e2 = Equal.cong(Bool, Bool, b => Bool.and(Nat.is_eq(SF.efield(x), 0n), Bool.not(b)), X.is_zero(F.frac(x)), Nat.is_eq(SF.frac(x), 0n), T.fz(x))
  Equal.trans(Bool, F.is_subnormal(x), Bool.and(Nat.is_eq(SF.efield(x), 0n), Bool.not(X.is_zero(F.frac(x)))), Bool.and(Nat.is_eq(SF.efield(x), 0n), Bool.not(Nat.is_eq(SF.frac(x), 0n))), e1, e2)

# ---- bit casts ----

def bits_g(+l: U32, +h: U32) -> {Nat.add(v(l), C.shift(32n, v(h))) == Nat.add(SF.pat(F.Bits{l, h}), C.shift(63n, SF.b2n(SF.sign(F.Bits{l, h})))) : Nat}:
  +H = v(h)
  +Lo = C.low(31n, H)
  +Hh = C.high(31n, H)
  +e1 = Equal.cong(Nat, Nat, t => Nat.add(v(l), C.shift(32n, t)), H, Nat.add(Lo, C.shift(31n, Hh)), WW.low_high(31n, H))
  +e2 = Equal.cong(Nat, Nat, t => Nat.add(v(l), t), C.shift(32n, Nat.add(Lo, C.shift(31n, Hh))), Nat.add(C.shift(32n, Lo), C.shift(32n, C.shift(31n, Hh))), WW.shift_add(32n, Lo, C.shift(31n, Hh)))
  +e3 = Equal.cong(Nat, Nat, t => Nat.add(v(l), Nat.add(C.shift(32n, Lo), t)), C.shift(32n, C.shift(31n, Hh)), C.shift(63n, Hh), Equal.sym(Nat, C.shift(63n, Hh), C.shift(32n, C.shift(31n, Hh)), WW.shift_comp(32n, 31n, Hh)))
  +e4 = Equal.sym(Nat, Nat.add(Nat.add(v(l), C.shift(32n, Lo)), C.shift(63n, Hh)), Nat.add(v(l), Nat.add(C.shift(32n, Lo), C.shift(63n, Hh))), NA.add_assoc(v(l), C.shift(32n, Lo), C.shift(63n, Hh)))
  +e5 = Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(63n, Hh)), Nat.add(v(l), C.shift(32n, Lo)), SF.pat(F.Bits{l, h}), FC.magQ(l, h))
  +e6 = Equal.cong(Nat, Nat, t => Nat.add(SF.pat(F.Bits{l, h}), C.shift(63n, t)), Hh, SF.b2n(SF.sign(F.Bits{l, h})), FB.bit_c(Hh, FB.half0(h)))
  +a1 = Nat.add(v(l), C.shift(32n, Nat.add(Lo, C.shift(31n, Hh))))
  +a2 = Nat.add(v(l), Nat.add(C.shift(32n, Lo), C.shift(32n, C.shift(31n, Hh))))
  +a3 = Nat.add(v(l), Nat.add(C.shift(32n, Lo), C.shift(63n, Hh)))
  +a4 = Nat.add(Nat.add(v(l), C.shift(32n, Lo)), C.shift(63n, Hh))
  +a5 = Nat.add(SF.pat(F.Bits{l, h}), C.shift(63n, Hh))
  +a6 = Nat.add(SF.pat(F.Bits{l, h}), C.shift(63n, SF.b2n(SF.sign(F.Bits{l, h}))))
  Equal.trans(Nat, Nat.add(v(l), C.shift(32n, H)), a1, a6, e1, Equal.trans(Nat, a1, a2, a6, e2, Equal.trans(Nat, a2, a3, a6, e3, Equal.trans(Nat, a3, a4, a6, e4, Equal.trans(Nat, a4, a5, a6, e5, e6)))))

def bits_value(+x: F.F64) -> SF.Bits.value(x):
  match x:
    case F.Bits{+l, +h}:
      bits_g(l, h)

def bits_roundtrip(+x: F.F64) -> SF.Bits.roundtrip(x):
  match x:
    case F.Bits{+l, +h}:
      {==}

def bits_inverse(+w: WU.U64) -> SF.Bits.inverse(w):
  match w:
    case WU.U64{+l, +h}:
      {==}
