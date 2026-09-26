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
import ./w64sh.bend as SH
import ./w64dm.bend as DM
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64mulp.bend as MP
import ./f64addb.bend as AB
import ./f64divn.bend as DN

# SoftFloat's f64_div significand: 2^62 + floor(Q / 4) with the sticky bit
# of Q mod 4 and the remainder, rounded by roundPackToF64.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# the low two bits of Q come from its low digit
def lowq(+d1: U32, +d2: U32) -> {C.low(2n, v(d2)) == C.low(2n, SW.value(WU.U64{d2, d1})) : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(v(d2), z), C.shift(32n, v(d1)), C.shift(2n, C.shift(30n, v(d1))), WW.shift_comp(2n, 30n, v(d1)))
  +e2 = WW.low_add_shift(2n, v(d2), C.shift(30n, v(d1)))
  Equal.sym(Nat, C.low(2n, SW.value(WU.U64{d2, d1})), C.low(2n, v(d2)), Equal.trans(Nat, C.low(2n, SW.value(WU.U64{d2, d1})), C.low(2n, Nat.add(v(d2), C.shift(2n, C.shift(30n, v(d1))))), C.low(2n, v(d2)), Equal.cong(Nat, Nat, z => C.low(2n, z), SW.value(WU.U64{d2, d1}), Nat.add(v(d2), C.shift(2n, C.shift(30n, v(d1)))), e1), e2))

def flag_v(+d1: U32, +d2: U32, +r2w: WU.U64) -> {Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))) == Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))) : Bool}:
  +f1 = Equal.cong(Bool, Bool, t => Bool.or(Bool.not(t), Bool.not(U32.is_zero(U32.and(d2, 3)))), X.is_zero(r2w), Nat.is_eq(SW.value(r2w), 0n), WA.is_zero_value(r2w))
  +f2 = Equal.cong(Bool, Bool, t => Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(t)), U32.is_zero(U32.and(d2, 3)), Nat.is_eq(v(U32.and(d2, 3)), 0n), LW.zero_nat(U32.and(d2, 3)))
  +f3 = Equal.cong(Nat, Bool, t => Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(t, 0n))), v(U32.and(d2, 3)), C.low(2n, SW.value(WU.U64{d2, d1})), Equal.trans(Nat, v(U32.and(d2, 3)), C.low(2n, v(d2)), C.low(2n, SW.value(WU.U64{d2, d1})), FB.andm(d2, 2n, 3, {==}), lowq(d1, d2)))
  Equal.trans(Bool, Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))), Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(U32.is_zero(U32.and(d2, 3)))), Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))), f1, Equal.trans(Bool, Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(U32.is_zero(U32.and(d2, 3)))), Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(v(U32.and(d2, 3)), 0n))), Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))), f2, f3))

def hq62(+d1: U32, +d2: U32) -> {C.fits(62n, C.high(2n, SW.value(WU.U64{d2, d1}))) == True{} : Bool}:
  Equal.trans(Bool, C.fits(62n, C.high(2n, SW.value(WU.U64{d2, d1}))), C.fits(Nat.add(2n, 62n), SW.value(WU.U64{d2, d1})), True{}, Equal.sym(Bool, C.fits(Nat.add(2n, 62n), SW.value(WU.U64{d2, d1})), C.fits(62n, C.high(2n, SW.value(WU.U64{d2, d1}))), FR.fits_hc(2n, 62n, SW.value(WU.U64{d2, d1}))), DM.fit64(WU.U64{d2, d1}))

def t63(+one: Nat, +h1: {one == 1n : Nat}, +d1: U32, +d2: U32) -> {C.fits(63n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1})))) == True{} : Bool}:
  +f = WW.limbs_fit(62n, 1n, C.high(2n, SW.value(WU.U64{d2, d1})), one, hq62(d1, d2), L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))
  L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(C.high(2n, SW.value(WU.U64{d2, d1})), C.shift(62n, one)), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), NA.add_comm(C.high(2n, SW.value(WU.U64{d2, d1})), C.shift(62n, one)), f)

def t62(+one: Nat, +h1: {one == 1n : Nat}, +d1: U32, +d2: U32) -> {C.fits(62n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1})))) == False{} : Bool}:
  L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, Nat.add(C.high(2n, SW.value(WU.U64{d2, d1})), C.shift(62n, one)), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), NA.add_comm(C.high(2n, SW.value(WU.U64{d2, d1})), C.shift(62n, one)), WW.unfit_one(62n, one, h1, C.high(2n, SW.value(WU.U64{d2, d1}))))

def w1_v(+one: Nat, +h1: {one == 1n : Nat}, +d1: U32, +d2: U32, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {SW.value(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))) == Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))) : Nat}:
  a1 = WA.add_value(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))
  +a2 = Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, SW.value(X.shr(WU.U64{d2, d1}, 2n)))), SW.value(WU.U64{0, c}), C.shift(62n, one), AB.c62(one, h1, c, hc))
  +a3 = Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(C.shift(62n, one), z)), SW.value(X.shr(WU.U64{d2, d1}, 2n)), C.high(2n, SW.value(WU.U64{d2, d1})), SH.shr_value(WU.U64{d2, d1}, 2n))
  +a4 = WW.low_fit(64n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SH.fits_mono(63n, 64n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), {==}, t63(one, h1, d1, d2)))
  Equal.trans(Nat, SW.value(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))), C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shr(WU.U64{d2, d1}, 2n)))), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shr(WU.U64{d2, d1}, 2n)))), C.low(64n, Nat.add(C.shift(62n, one), SW.value(X.shr(WU.U64{d2, d1}, 2n)))), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), a2, Equal.trans(Nat, C.low(64n, Nat.add(C.shift(62n, one), SW.value(X.shr(WU.U64{d2, d1}, 2n)))), C.low(64n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1})))), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), a3, a4)))

def sig_v(+one: Nat, +h1: {one == 1n : Nat}, +d1: U32, +d2: U32, +r2w: WU.U64, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))) == SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))) : Nat}:
  +o1 = MP.orv(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))
  +o2 = Equal.cong(Nat, Nat, z => SW.jam(z, SF.b2n(Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.value(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))), Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), w1_v(one, h1, d1, d2, c, hc))
  +o3 = Equal.cong(Bool, Nat, t => SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(t)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))), Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))), flag_v(d1, d2, r2w))
  Equal.trans(Nat, SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(SW.value(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))), SF.b2n(Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), o1, Equal.trans(Nat, SW.jam(SW.value(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n))), SF.b2n(Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), o2, o3))

# roundPackToF64 of the quotient significand is the spec's round of its value
def dq_round(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +d1: U32, +d2: U32, +r2w: WU.U64, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {F.round_pack(s, e, X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))) == SF.round(s, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), x) : F.F64}:
  +ev = sig_v(one, h1, d1, d2, r2w, c, hc)
  +J = SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n)))))
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), Equal.sym(Nat, SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), ev), Equal.trans(Bool, C.fits(63n, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n)))))), C.fits(63n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1})))), True{}, RT.jam_fits(62n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), t63(one, h1, d1, d2)))
  +h62 = L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), Equal.sym(Nat, SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), ev), Equal.trans(Bool, C.fits(62n, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n)))))), C.fits(62n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1})))), False{}, RT.jam_fits(61n, Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), t62(one, h1, d1, d2)))
  +r1 = FR.round_pack(s, e, X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3))))), x, hx, h62, h63)
  Equal.trans(F.F64, F.round_pack(s, e, X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SF.round(s, SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), x), SF.round(s, SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), x), r1, Equal.cong(Nat, F.F64, z => SF.round(s, z, x), SW.value(X.or_bit(X.add(WU.U64{0, c}, X.shr(WU.U64{d2, d1}, 2n)), Bool.or(F.nz(r2w), Bool.not(U32.is_zero(U32.and(d2, 3)))))), SW.jam(Nat.add(C.shift(62n, one), C.high(2n, SW.value(WU.U64{d2, d1}))), SF.b2n(Bool.or(Bool.not(Nat.is_eq(SW.value(r2w), 0n)), Bool.not(Nat.is_eq(C.low(2n, SW.value(WU.U64{d2, d1})), 0n))))), ev))

# a * 2^62 = T * b + e for a = (a - b) + b
def iq_T(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +R: Nat, +Q: Nat, +r2: Nat, +hQ: {Nat.add(Nat.mul(Q, 1n+bp), r2) == C.shift(64n, R) : Nat}) -> {Nat.add(Nat.mul(Nat.add(C.shift(62n, one), C.high(2n, Q)), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))) == C.shift(62n, Nat.add(R, 1n+bp)) : Nat}:
  +k1 = Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), Nat.mul(Nat.add(C.shift(62n, one), C.high(2n, Q)), 1n+bp), Nat.add(Nat.mul(C.shift(62n, one), 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp)), NA.mul_add_right(C.shift(62n, one), C.high(2n, Q), 1n+bp))
  +e62 = Equal.trans(Nat, Nat.mul(C.shift(62n, one), 1n+bp), Nat.mul(1n+bp, C.shift(62n, one)), C.shift(62n, 1n+bp), NA.mul_comm(C.shift(62n, one), 1n+bp), Equal.sym(Nat, C.shift(62n, 1n+bp), Nat.mul(1n+bp, C.shift(62n, one)), WW.shift_mul_one(62n, one, h1, 1n+bp)))
  +k2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.mul(C.high(2n, Q), 1n+bp)), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), Nat.mul(C.shift(62n, one), 1n+bp), C.shift(62n, 1n+bp), e62)
  +k3 = NA.add_assoc(C.shift(62n, 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp)))
  +k4 = Equal.cong(Nat, Nat, z => Nat.add(C.shift(62n, 1n+bp), z), Nat.add(Nat.mul(C.high(2n, Q), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), C.shift(62n, R), N.sub_add(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp), DN.iq_le(1n+bp, R, Q, r2, hQ)))
  +k5 = NA.add_comm(C.shift(62n, 1n+bp), C.shift(62n, R))
  +k6 = Equal.sym(Nat, C.shift(62n, Nat.add(R, 1n+bp)), Nat.add(C.shift(62n, R), C.shift(62n, 1n+bp)), WW.shift_add(62n, R, 1n+bp))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(C.shift(62n, one), C.high(2n, Q)), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), Nat.add(Nat.add(Nat.mul(C.shift(62n, one), 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp)), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), C.shift(62n, Nat.add(R, 1n+bp)), k1, Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(C.shift(62n, one), 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp)), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), Nat.add(Nat.add(C.shift(62n, 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp)), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), C.shift(62n, Nat.add(R, 1n+bp)), k2, Equal.trans(Nat, Nat.add(Nat.add(C.shift(62n, 1n+bp), Nat.mul(C.high(2n, Q), 1n+bp)), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp))), Nat.add(C.shift(62n, 1n+bp), Nat.add(Nat.mul(C.high(2n, Q), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp)))), C.shift(62n, Nat.add(R, 1n+bp)), k3, Equal.trans(Nat, Nat.add(C.shift(62n, 1n+bp), Nat.add(Nat.mul(C.high(2n, Q), 1n+bp), Nat.sub(C.shift(62n, R), Nat.mul(C.high(2n, Q), 1n+bp)))), Nat.add(C.shift(62n, 1n+bp), C.shift(62n, R)), C.shift(62n, Nat.add(R, 1n+bp)), k4, Equal.trans(Nat, Nat.add(C.shift(62n, 1n+bp), C.shift(62n, R)), Nat.add(C.shift(62n, R), C.shift(62n, 1n+bp)), C.shift(62n, Nat.add(R, 1n+bp)), k5, k6)))))
