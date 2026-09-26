import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/arith.bend as AR2
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64mul.bend as W64M
import ./w64sh.bend as SH
import ./w64m128.bend as M128
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64mulp.bend as MP

# Mul.value of spec/math/f64.bend: SoftFloat's f64_mul multiplies the two
# normalized 53-bit significands (shifted by 10 and 11) into 128 bits, jams
# the low half into bit 0 and rounds with rp62; the spec rounds the exact
# product of the significands. round_jam and round_shift bridge the two.

def fits_mul(+k: Nat, +x: Nat, +y: Nat, +hx: {C.fits(k, x) == True{} : Bool}, +hy: {C.fits(k, y) == True{} : Bool}) -> {C.fits(Nat.add(k, k), Nat.mul(x, y)) == True{} : Bool}:
  +h = W64M.mul_lt_sq(x, y, C.pow2(k), WW.lt_of_fits(k, x, hx), WW.lt_of_fits(k, y, hy))
  WW.fits_of_lt(Nat.add(k, k), Nat.mul(x, y), L.subst(Nat, z => {Nat.is_lt(Nat.mul(x, y), z) == True{} : Bool}, Nat.mul(C.pow2(k), C.pow2(k)), C.pow2(Nat.add(k, k)), WW.pow2_sq(k), h))

def nfits_mul(+k: Nat, +x: Nat, +y: Nat, +hx: {C.fits(k, x) == False{} : Bool}, +hy: {C.fits(k, y) == False{} : Bool}) -> {C.fits(Nat.add(k, k), Nat.mul(x, y)) == False{} : Bool}:
  +P = C.pow2(k)
  +px = N.not_lt_le(x, P, Equal.trans(Bool, Nat.is_lt(x, P), C.fits(k, x), False{}, Equal.sym(Bool, C.fits(k, x), Nat.is_lt(x, P), WW.fits_lt(k, x)), hx))
  +py = N.not_lt_le(y, P, Equal.trans(Bool, Nat.is_lt(y, P), C.fits(k, y), False{}, Equal.sym(Bool, C.fits(k, y), Nat.is_lt(y, P), WW.fits_lt(k, y)), hy))
  +h1 = N.le_trans(Nat.mul(P, P), Nat.mul(x, P), Nat.mul(x, y), AR2.mul_le(P, x, P, px), W64M.le_mul_r(x, P, y, py))
  +h2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(x, y)) == True{} : Bool}, Nat.mul(P, P), C.pow2(Nat.add(k, k)), WW.pow2_sq(k), h1)
  Equal.trans(Bool, C.fits(Nat.add(k, k), Nat.mul(x, y)), Nat.is_lt(Nat.mul(x, y), C.pow2(Nat.add(k, k))), False{}, WW.fits_lt(Nat.add(k, k), Nat.mul(x, y)), N.le_not_lt(Nat.mul(x, y), C.pow2(Nat.add(k, k)), h2))

def shl_v(+a: WU.U64, +k: Nat, +j: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(k, j), 64n) == True{} : Bool}, +ha: {C.fits(j, SW.value(a)) == True{} : Bool}) -> {SW.value(X.shl(a, k)) == C.shift(k, SW.value(a)) : Nat}:
  sv = SH.shl_value(a, k, hk)
  +f = SH.fits_mono(Nat.add(k, j), 64n, C.shift(k, SW.value(a)), hj, Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, SW.value(a))), C.fits(j, SW.value(a)), True{}, RT.fits_sh(k, j, SW.value(a)), ha))
  Equal.trans(Nat, SW.value(X.shl(a, k)), C.low(64n, C.shift(k, SW.value(a))), C.shift(k, SW.value(a)), sv, WW.low_fit(64n, C.shift(k, SW.value(a)), f))

def m128g(+a: WU.U64, +b: WU.U64) -> {Nat.add(SW.value(X.pfst(X.mul128(a, b))), C.shift(64n, SW.value(X.psnd(X.mul128(a, b))))) == Nat.mul(SW.value(a), SW.value(b)) : Nat}:
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      M128.m128_value(al, ah, bl, bh)

# the 128-bit product jammed to 64 bits and rounded by rp62
def mc2(+s: Bool, +e: Nat, +pl: WU.U64, +ph: WU.U64, +P: Nat, +hp: {Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))) == P : Nat}, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, x) == True{} : Bool}, +h127: {C.fits(127n, P) == True{} : Bool}, +h125: {C.fits(125n, P) == False{} : Bool}) -> {F.rp62(s, e, X.or_bit(ph, F.nz(pl))) == SF.round(s, SW.jam(C.high(64n, P), C.low(64n, P)), x) : F.F64}:
  +fl = M128.fit64(pl)
  +eh = Equal.trans(Nat, C.high(64n, P), C.high(64n, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), SW.value(ph), Equal.cong(Nat, Nat, z => C.high(64n, z), P, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), Equal.sym(Nat, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), P, hp)), WW.high_u(64n, SW.value(pl), SW.value(ph), fl))
  +el = Equal.trans(Nat, C.low(64n, P), C.low(64n, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph)))), SW.value(pl), Equal.cong(Nat, Nat, z => C.low(64n, z), P, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), Equal.sym(Nat, Nat.add(SW.value(pl), C.shift(64n, SW.value(ph))), P, hp)), WW.low_u(64n, SW.value(pl), SW.value(ph), fl))
  +ez = Equal.cong(Bool, Nat, t => SF.b2n(Bool.not(t)), X.is_zero(pl), Nat.is_eq(SW.value(pl), 0n), WA.is_zero_value(pl))
  +ev = Equal.trans(Nat, SW.value(X.or_bit(ph, F.nz(pl))), SW.jam(SW.value(ph), SF.b2n(F.nz(pl))), SW.jam(C.high(64n, P), C.low(64n, P)), MP.orv(ph, F.nz(pl)), Equal.trans(Nat, SW.jam(SW.value(ph), SF.b2n(F.nz(pl))), SW.jam(SW.value(ph), SF.b2n(Bool.not(Nat.is_eq(SW.value(pl), 0n)))), SW.jam(C.high(64n, P), C.low(64n, P)), Equal.cong(Nat, Nat, z => SW.jam(SW.value(ph), z), SF.b2n(F.nz(pl)), SF.b2n(Bool.not(Nat.is_eq(SW.value(pl), 0n))), ez), Equal.trans(Nat, SW.jam(SW.value(ph), SF.b2n(Bool.not(Nat.is_eq(SW.value(pl), 0n)))), SW.jam(SW.value(ph), SW.value(pl)), SW.jam(C.high(64n, P), C.low(64n, P)), MP.jmin(SW.value(ph), SW.value(pl)), Equal.trans(Nat, SW.jam(SW.value(ph), SW.value(pl)), SW.jam(C.high(64n, P), SW.value(pl)), SW.jam(C.high(64n, P), C.low(64n, P)), Equal.cong(Nat, Nat, z => SW.jam(z, SW.value(pl)), SW.value(ph), C.high(64n, P), Equal.sym(Nat, C.high(64n, P), SW.value(ph), eh)), Equal.cong(Nat, Nat, z => SW.jam(C.high(64n, P), z), SW.value(pl), C.low(64n, P), Equal.sym(Nat, C.low(64n, P), SW.value(pl), el))))))
  +f63h = Equal.trans(Bool, C.fits(63n, C.high(64n, P)), C.fits(Nat.add(64n, 63n), P), True{}, Equal.sym(Bool, C.fits(Nat.add(64n, 63n), P), C.fits(63n, C.high(64n, P)), FR.fits_hc(64n, 63n, P)), h127)
  +f61h = Equal.trans(Bool, C.fits(61n, C.high(64n, P)), C.fits(Nat.add(64n, 61n), P), False{}, Equal.sym(Bool, C.fits(Nat.add(64n, 61n), P), C.fits(61n, C.high(64n, P)), FR.fits_hc(64n, 61n, P)), h125)
  +fJ63 = Equal.trans(Bool, C.fits(63n, SW.jam(C.high(64n, P), C.low(64n, P))), C.fits(63n, C.high(64n, P)), True{}, RT.jam_fits(62n, C.high(64n, P), C.low(64n, P)), f63h)
  +t = Nat.max(C.bit(C.high(64n, P)), Nat.min(C.low(64n, P), 1n))
  +ejf = FR.jam_form(C.high(64n, P), C.low(64n, P))
  +hhb = WW.le_add_r(C.bit(C.high(64n, P)), t, Nat.double(C.half(C.high(64n, P))), RT.max_ge_l(C.bit(C.high(64n, P)), Nat.min(C.low(64n, P), 1n)))
  +hhJ = L.subst(Nat, z => {Nat.is_le(z, SW.jam(C.high(64n, P), C.low(64n, P))) == True{} : Bool}, Nat.add(C.bit(C.high(64n, P)), Nat.double(C.half(C.high(64n, P)))), C.high(64n, P), Equal.sym(Nat, C.high(64n, P), Nat.add(C.bit(C.high(64n, P)), Nat.double(C.half(C.high(64n, P)))), WW.hb(C.high(64n, P))), L.subst(Nat, z => {Nat.is_le(Nat.add(C.bit(C.high(64n, P)), Nat.double(C.half(C.high(64n, P)))), z) == True{} : Bool}, Nat.add(t, Nat.double(C.half(C.high(64n, P)))), SW.jam(C.high(64n, P), C.low(64n, P)), Equal.sym(Nat, SW.jam(C.high(64n, P), C.low(64n, P)), Nat.add(t, Nat.double(C.half(C.high(64n, P)))), ejf), hhb))
  +fJ61 = FR.nfit(61n, C.high(64n, P), SW.jam(C.high(64n, P), C.low(64n, P)), hhJ, f61h)
  +sig = X.or_bit(ph, F.nz(pl))
  +h61 = L.subst(Nat, z => {C.fits(61n, z) == False{} : Bool}, SW.jam(C.high(64n, P), C.low(64n, P)), SW.value(sig), Equal.sym(Nat, SW.value(sig), SW.jam(C.high(64n, P), C.low(64n, P)), ev), fJ61)
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SW.jam(C.high(64n, P), C.low(64n, P)), SW.value(sig), Equal.sym(Nat, SW.value(sig), SW.jam(C.high(64n, P), C.low(64n, P)), ev), fJ63)
  Equal.trans(F.F64, F.rp62(s, e, sig), SF.round(s, SW.value(sig), x), SF.round(s, SW.jam(C.high(64n, P), C.low(64n, P)), x), MP.rp62(s, e, sig, x, hx, hx1, h61, h63), Equal.cong(Nat, F.F64, z => SF.round(s, z, x), SW.value(sig), SW.jam(C.high(64n, P), C.low(64n, P)), ev))

def mcore(+s: Bool, +e: Nat, p: WU.U64 & WU.U64, +P: Nat, +hp: {Nat.add(SW.value(X.pfst(p)), C.shift(64n, SW.value(X.psnd(p)))) == P : Nat}, +x: Nat, +hx: {Nat.add(x, 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, x) == True{} : Bool}, +h127: {C.fits(127n, P) == True{} : Bool}, +h125: {C.fits(125n, P) == False{} : Bool}) -> {F.mul_n2(s, e, p) == SF.round(s, SW.jam(C.high(64n, P), C.low(64n, P)), x) : F.F64}:
  (+pl, +ph) = p
  mc2(s, e, pl, ph, P, hp, x, hx, hx1, h127, h125)
