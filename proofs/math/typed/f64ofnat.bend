import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/bits.bend as BT
import ../../lib/u32half.bend as UHX
import ./width.bend as WW
import ./w64sh.bend as SH
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64bl.bend as BL

# OfNat.value of spec/math/f64.bend: of_nat rounds n through
# roundPackToF64, its bit length b moving the top bit to bit 62: an exact
# shift when b <= 63, a sticky jam otherwise (SoftFloat's ui64_to_f64 and
# softfloat_shiftRightJam), so the clause follows from round_pack and the
# two invariances of round (f64rtools.bend).

def hx(+bb: Nat) -> {Nat.add(Nat.add(2937n, bb), 2180n) == Nat.add(5117n, bb) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(2937n, bb), 2180n), Nat.add(2937n, Nat.add(bb, 2180n)), Nat.add(5117n, bb), NA.add_assoc(2937n, bb, 2180n), Equal.cong(Nat, Nat, z => Nat.add(2937n, z), Nat.add(bb, 2180n), Nat.add(2180n, bb), NA.add_comm(bb, 2180n)))

def jn(+dd: Nat, +n: Nat) -> {F.jam_nat(dd, n) == SW.jam(C.high(dd, n), C.low(dd, n)) : Nat}:
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(z, 2n)), Nat.max(Nat.mod(F.high_bits(dd, n), 2n), Nat.min(F.low_bits(dd, n), 1n))), F.high_bits(dd, n), C.high(dd, n), BL.hbits(dd, n))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(C.high(dd, n), 2n)), Nat.max(Nat.mod(z, 2n), Nat.min(F.low_bits(dd, n), 1n))), F.high_bits(dd, n), C.high(dd, n), BL.hbits(dd, n))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(2n, Nat.div(C.high(dd, n), 2n)), Nat.max(Nat.mod(C.high(dd, n), 2n), Nat.min(z, 1n))), F.low_bits(dd, n), C.low(dd, n), BL.lbits(dd, n))
  Equal.trans(Nat, F.jam_nat(dd, n), Nat.add(Nat.mul(2n, Nat.div(C.high(dd, n), 2n)), Nat.max(Nat.mod(F.high_bits(dd, n), 2n), Nat.min(F.low_bits(dd, n), 1n))), SW.jam(C.high(dd, n), C.low(dd, n)), e1, Equal.trans(Nat, Nat.add(Nat.mul(2n, Nat.div(C.high(dd, n), 2n)), Nat.max(Nat.mod(F.high_bits(dd, n), 2n), Nat.min(F.low_bits(dd, n), 1n))), Nat.add(Nat.mul(2n, Nat.div(C.high(dd, n), 2n)), Nat.max(Nat.mod(C.high(dd, n), 2n), Nat.min(F.low_bits(dd, n), 1n))), SW.jam(C.high(dd, n), C.low(dd, n)), e2, e3))

# b <= 63: an exact shift
def on_le(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}, +hc: {Nat.is_le(M.bit_length(n), 63n) == True{} : Bool}) -> {F.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))) == SF.round(False{}, n, SF.zb()) : F.F64}:
  +fb = RT.bl_fit(n)
  +h64 = SH.fits_mono(M.bit_length(n), 64n, n, N.le_trans(M.bit_length(n), 63n, 64n, hc, {==}), fb)
  +ew = BL.wval(n, h64)
  +ek = Equal.trans(Nat, Nat.add(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), Nat.add(M.bit_length(n), Nat.sub(63n, M.bit_length(n))), 63n, NA.add_comm(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), N.sub_add(63n, M.bit_length(n), hc))
  +hqu = L.subst(Nat, z => {Nat.is_lt(C.shift(Nat.sub(63n, M.bit_length(n)), n), z) == True{} : Bool}, C.shift(Nat.sub(63n, M.bit_length(n)), C.pow2(M.bit_length(n))), C.pow2(Nat.add(Nat.sub(63n, M.bit_length(n)), M.bit_length(n))), WW.shift_pow2(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), WW.shift_lt(Nat.sub(63n, M.bit_length(n)), n, C.pow2(M.bit_length(n)), BT.bit_length_lt(n)))
  +f63 = L.subst(Nat, z => {C.fits(z, C.shift(Nat.sub(63n, M.bit_length(n)), n)) == True{} : Bool}, Nat.add(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), 63n, ek, WW.fits_of_lt(Nat.add(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), C.shift(Nat.sub(63n, M.bit_length(n)), n), hqu))
  +epb = N.sub_add(M.bit_length(n), 1n, BL.bl_pos(n, hz, M.bit_length(n), {==}))
  +K2 = Nat.add(Nat.sub(63n, M.bit_length(n)), Nat.sub(M.bit_length(n), 1n))
  +e62 = N.succ_inj(K2, 62n, Equal.trans(Nat, 1n+K2, Nat.add(Nat.sub(63n, M.bit_length(n)), 1n+Nat.sub(M.bit_length(n), 1n)), 63n, Equal.sym(Nat, Nat.add(Nat.sub(63n, M.bit_length(n)), 1n+Nat.sub(M.bit_length(n), 1n)), 1n+K2, N.add_succ(Nat.sub(63n, M.bit_length(n)), Nat.sub(M.bit_length(n), 1n))), Equal.trans(Nat, Nat.add(Nat.sub(63n, M.bit_length(n)), 1n+Nat.sub(M.bit_length(n), 1n)), Nat.add(Nat.sub(63n, M.bit_length(n)), M.bit_length(n)), 63n, Equal.cong(Nat, Nat, z => Nat.add(Nat.sub(63n, M.bit_length(n)), z), 1n+Nat.sub(M.bit_length(n), 1n), M.bit_length(n), epb), ek)))
  +hql = L.subst(Nat, z => {Nat.is_le(z, C.shift(Nat.sub(63n, M.bit_length(n)), n)) == True{} : Bool}, C.shift(Nat.sub(63n, M.bit_length(n)), C.pow2(Nat.sub(M.bit_length(n), 1n))), C.pow2(K2), WW.shift_pow2(Nat.sub(63n, M.bit_length(n)), Nat.sub(M.bit_length(n), 1n)), WW.shift_mono(Nat.sub(63n, M.bit_length(n)), C.pow2(Nat.sub(M.bit_length(n), 1n)), n, BL.lower(n, hz)))
  +nf = Equal.trans(Bool, C.fits(K2, C.pow2(K2)), Nat.is_lt(C.pow2(K2), C.pow2(K2)), False{}, WW.fits_lt(K2, C.pow2(K2)), N.lt_irrefl(C.pow2(K2)))
  +f62 = L.subst(Nat, z => {C.fits(z, C.shift(Nat.sub(63n, M.bit_length(n)), n)) == False{} : Bool}, K2, 62n, e62, FR.nfit(K2, C.pow2(K2), C.shift(Nat.sub(63n, M.bit_length(n)), n), hql, nf))
  +hk = N.le_lt_trans(Nat.sub(63n, M.bit_length(n)), 63n, 64n, UHX.sub_le(63n, M.bit_length(n)), {==})
  sv = SH.shl_value(F.word64(n), Nat.sub(63n, M.bit_length(n)), hk)
  +em = Equal.trans(Nat, SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), C.low(64n, C.shift(Nat.sub(63n, M.bit_length(n)), SW.value(F.word64(n)))), C.shift(Nat.sub(63n, M.bit_length(n)), n), sv, Equal.trans(Nat, C.low(64n, C.shift(Nat.sub(63n, M.bit_length(n)), SW.value(F.word64(n)))), C.low(64n, C.shift(Nat.sub(63n, M.bit_length(n)), n)), C.shift(Nat.sub(63n, M.bit_length(n)), n), Equal.cong(Nat, Nat, z => C.low(64n, C.shift(Nat.sub(63n, M.bit_length(n)), z)), SW.value(F.word64(n)), n, ew), WW.low_fit(64n, C.shift(Nat.sub(63n, M.bit_length(n)), n), SH.fits_mono(63n, 64n, C.shift(Nat.sub(63n, M.bit_length(n)), n), {==}, f63))))
  +h62 = L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, C.shift(Nat.sub(63n, M.bit_length(n)), n), SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), Equal.sym(Nat, SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), C.shift(Nat.sub(63n, M.bit_length(n)), n), em), f62)
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, C.shift(Nat.sub(63n, M.bit_length(n)), n), SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), Equal.sym(Nat, SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), C.shift(Nat.sub(63n, M.bit_length(n)), n), em), f63)
  +r1 = FR.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n))), Nat.add(2937n, M.bit_length(n)), hx(M.bit_length(n)), h62, h63)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(False{}, z, Nat.add(2937n, M.bit_length(n))), SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), C.shift(Nat.sub(63n, M.bit_length(n)), n), em)
  +r3 = RT.round_shift(False{}, Nat.sub(63n, M.bit_length(n)), n, Nat.add(2937n, M.bit_length(n)))
  +ex = Equal.trans(Nat, Nat.add(Nat.add(2937n, M.bit_length(n)), Nat.sub(63n, M.bit_length(n))), Nat.add(2937n, Nat.add(M.bit_length(n), Nat.sub(63n, M.bit_length(n)))), 3000n, NA.add_assoc(2937n, M.bit_length(n), Nat.sub(63n, M.bit_length(n))), Equal.cong(Nat, Nat, z => Nat.add(2937n, z), Nat.add(M.bit_length(n), Nat.sub(63n, M.bit_length(n))), 63n, N.sub_add(63n, M.bit_length(n), hc)))
  +r4 = Equal.cong(Nat, F.F64, z => SF.round(False{}, n, z), Nat.add(Nat.add(2937n, M.bit_length(n)), Nat.sub(63n, M.bit_length(n))), SF.zb(), ex)
  Equal.trans(F.F64, F.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), SF.round(False{}, SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, n, SF.zb()), r1, Equal.trans(F.F64, SF.round(False{}, SW.value(X.shl(F.word64(n), Nat.sub(63n, M.bit_length(n)))), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, C.shift(Nat.sub(63n, M.bit_length(n)), n), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, n, SF.zb()), r2, Equal.trans(F.F64, SF.round(False{}, C.shift(Nat.sub(63n, M.bit_length(n)), n), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, n, Nat.add(Nat.add(2937n, M.bit_length(n)), Nat.sub(63n, M.bit_length(n)))), SF.round(False{}, n, SF.zb()), r3, r4)))

# b > 63: a sticky jam of n >> (b - 63)
def on_gt(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}, +hc: {Nat.is_le(M.bit_length(n), 63n) == False{} : Bool}) -> {F.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))) == SF.round(False{}, n, SF.zb()) : F.F64}:
  +h63b = N.lt_le(63n, M.bit_length(n), N.not_le_lt(M.bit_length(n), 63n, hc))
  +eb = N.sub_add(M.bit_length(n), 63n, h63b)
  +ed63 = Equal.trans(Nat, Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), Nat.add(63n, Nat.sub(M.bit_length(n), 63n)), M.bit_length(n), NA.add_comm(Nat.sub(M.bit_length(n), 63n), 63n), eb)
  +epb = N.sub_add(M.bit_length(n), 1n, BL.bl_pos(n, hz, M.bit_length(n), {==}))
  +ed62 = N.succ_inj(Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), Nat.sub(M.bit_length(n), 1n), Equal.trans(Nat, 1n+Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), 1n+Nat.sub(M.bit_length(n), 1n), Equal.sym(Nat, Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), 1n+Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), N.add_succ(Nat.sub(M.bit_length(n), 63n), 62n)), Equal.trans(Nat, Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), M.bit_length(n), 1n+Nat.sub(M.bit_length(n), 1n), ed63, Equal.sym(Nat, 1n+Nat.sub(M.bit_length(n), 1n), M.bit_length(n), epb))))
  +h = C.high(Nat.sub(M.bit_length(n), 63n), n)
  +fh63 = Equal.trans(Bool, C.fits(63n, h), C.fits(Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), n), True{}, Equal.sym(Bool, C.fits(Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), n), C.fits(63n, h), FR.fits_hc(Nat.sub(M.bit_length(n), 63n), 63n, n)), L.subst(Nat, z => {C.fits(z, n) == True{} : Bool}, M.bit_length(n), Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), Equal.sym(Nat, Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), M.bit_length(n), ed63), RT.bl_fit(n)))
  +fh62 = Equal.trans(Bool, C.fits(62n, h), C.fits(Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), n), False{}, Equal.sym(Bool, C.fits(Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), n), C.fits(62n, h), FR.fits_hc(Nat.sub(M.bit_length(n), 63n), 62n, n)), L.subst(Nat, z => {C.fits(z, n) == False{} : Bool}, Nat.sub(M.bit_length(n), 1n), Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), Equal.sym(Nat, Nat.add(Nat.sub(M.bit_length(n), 63n), 62n), Nat.sub(M.bit_length(n), 1n), ed62), RT.bl_nfit(n, hz)))
  +f63 = Equal.trans(Bool, C.fits(63n, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n))), C.fits(63n, h), True{}, RT.jam_fits(62n, h, C.low(Nat.sub(M.bit_length(n), 63n), n)), fh63)
  +t = Nat.max(C.bit(h), Nat.min(C.low(Nat.sub(M.bit_length(n), 63n), n), 1n))
  +ejf = FR.jam_form(h, C.low(Nat.sub(M.bit_length(n), 63n), n))
  +hhb = WW.le_add_r(C.bit(h), t, Nat.double(C.half(h)), RT.max_ge_l(C.bit(h), Nat.min(C.low(Nat.sub(M.bit_length(n), 63n), n), 1n)))
  +hhJ = L.subst(Nat, z => {Nat.is_le(z, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n))) == True{} : Bool}, Nat.add(C.bit(h), Nat.double(C.half(h))), h, Equal.sym(Nat, h, Nat.add(C.bit(h), Nat.double(C.half(h))), WW.hb(h)), L.subst(Nat, z => {Nat.is_le(Nat.add(C.bit(h), Nat.double(C.half(h))), z) == True{} : Bool}, Nat.add(t, Nat.double(C.half(h))), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Equal.sym(Nat, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(t, Nat.double(C.half(h))), ejf), hhb))
  +f62 = FR.nfit(62n, h, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), hhJ, fh62)
  +ej = jn(Nat.sub(M.bit_length(n), 63n), n)
  +ew = Equal.trans(Nat, SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), F.jam_nat(Nat.sub(M.bit_length(n), 63n), n), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), BL.wval(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n), SH.fits_mono(63n, 64n, F.jam_nat(Nat.sub(M.bit_length(n), 63n), n), {==}, L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), F.jam_nat(Nat.sub(M.bit_length(n), 63n), n), Equal.sym(Nat, F.jam_nat(Nat.sub(M.bit_length(n), 63n), n), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), ej), f63))), ej)
  +h62 = L.subst(Nat, z => {C.fits(62n, z) == False{} : Bool}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), Equal.sym(Nat, SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), ew), f62)
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), Equal.sym(Nat, SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), ew), f63)
  +r1 = FR.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(2937n, M.bit_length(n)), hx(M.bit_length(n)), h62, h63)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(False{}, z, Nat.add(2937n, M.bit_length(n))), SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), ew)
  +ex = Equal.trans(Nat, Nat.add(2937n, M.bit_length(n)), Nat.add(2937n, Nat.add(63n, Nat.sub(M.bit_length(n), 63n))), Nat.add(SF.zb(), Nat.sub(M.bit_length(n), 63n)), Equal.cong(Nat, Nat, z => Nat.add(2937n, z), M.bit_length(n), Nat.add(63n, Nat.sub(M.bit_length(n), 63n)), Equal.sym(Nat, Nat.add(63n, Nat.sub(M.bit_length(n), 63n)), M.bit_length(n), eb)), {==})
  +r3 = Equal.cong(Nat, F.F64, z => SF.round(False{}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), z), Nat.add(2937n, M.bit_length(n)), Nat.add(SF.zb(), Nat.sub(M.bit_length(n), 63n)), ex)
  +hb55 = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.sub(M.bit_length(n), 63n), 55n), z) == True{} : Bool}, Nat.add(Nat.sub(M.bit_length(n), 63n), 63n), M.bit_length(n), ed63, N.le_add_left(55n, 63n, Nat.sub(M.bit_length(n), 63n), {==}))
  +r4 = Equal.sym(F.F64, SF.round(False{}, n, SF.zb()), SF.round(False{}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(SF.zb(), Nat.sub(M.bit_length(n), 63n))), RT.round_jam(False{}, Nat.sub(M.bit_length(n), 63n), n, SF.zb(), hb55))
  Equal.trans(F.F64, F.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), SF.round(False{}, SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, n, SF.zb()), r1, Equal.trans(F.F64, SF.round(False{}, SW.value(F.word64(F.jam_nat(Nat.sub(M.bit_length(n), 63n), n))), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, n, SF.zb()), r2, Equal.trans(F.F64, SF.round(False{}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(2937n, M.bit_length(n))), SF.round(False{}, SW.jam(C.high(Nat.sub(M.bit_length(n), 63n), n), C.low(Nat.sub(M.bit_length(n), 63n), n)), Nat.add(SF.zb(), Nat.sub(M.bit_length(n), 63n))), SF.round(False{}, n, SF.zb()), r3, r4)))

def on_c(+n: Nat, +hz: {Nat.is_eq(n, 0n) == False{} : Bool}, +c: Bool, +hc: {Nat.is_le(M.bit_length(n), 63n) == c : Bool}) -> {F.round_pack(False{}, Nat.add(5117n, M.bit_length(n)), F.sig63(n, M.bit_length(n), c)) == SF.round(False{}, n, SF.zb()) : F.F64}:
  match c:
    case True{}:
      on_le(n, hz, hc)
    case False{}:
      on_gt(n, hz, hc)

def ofz(+n: Nat, +z: Bool, +hz: {Nat.is_eq(n, 0n) == z : Bool}) -> {F.of_nat_z(n, z) == SF.round(False{}, n, SF.zb()) : F.F64}:
  match z:
    case True{}:
      Equal.sym(F.F64, SF.round(False{}, n, SF.zb()), SF.zero(False{}), Equal.cong(Bool, F.F64, t => SF.pick(F.F64, t, SF.zero(False{}), SF.round_u(False{}, n, SF.zb(), Nat.max(Nat.sub(Nat.add(SF.zb(), M.bit_length(n)), 53n), Nat.sub(SF.zb(), 1074n)))), Nat.is_eq(n, 0n), True{}, hz))
    case False{}:
      on_c(n, hz, Nat.is_le(M.bit_length(n), 63n), {==})

def of_nat_value(+n: Nat) -> SF.OfNat.value(n):
  ofz(n, Nat.is_eq(n, 0n), {==})
