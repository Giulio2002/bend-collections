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
import ./w64sh.bend as SH
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64bl.bend as BL
import ./f64norm.bend as NM
import ./f64nrp.bend as NP
import ./f64addc.bend as AC

# subMagsF64 with equal exponents: the exact difference d (0 < d < 2^52) at
# the exponent field e1 + 1 is normalized without rounding.

def lt_add_sub(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(a, Nat.sub(c, b)) == True{} : Bool}, +hb: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(a, b), c) == True{} : Bool}:
  +h1 = N.lt_succ_le_succ(a, Nat.sub(c, b), h)
  +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(1n+a, b), Nat.add(Nat.sub(c, b), b)), Nat.is_le(1n+a, Nat.sub(c, b)), True{}, FR.le_cancel_r(1n+a, Nat.sub(c, b), b), h1)
  +ec = Equal.trans(Nat, Nat.add(Nat.sub(c, b), b), Nat.add(b, Nat.sub(c, b)), c, NA.add_comm(Nat.sub(c, b), b), N.sub_add(c, b, hb))
  L.subst(Nat, z => {Nat.is_le(Nat.add(1n+a, b), z) == True{} : Bool}, Nat.add(Nat.sub(c, b), b), c, ec, h2)

def smx_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e1: Nat, +d: WU.U64, +D: Nat, +hd: {SW.value(d) == D : Nat}, +hD: {C.fits(52n, D) == True{} : Bool}, +hz: {Nat.is_eq(D, 0n) == False{} : Bool}, +hov: {Nat.is_lt(Nat.add(e1, 1n), 2047n) == True{} : Bool}, +u: Bool, +hu: {Nat.is_lt(e1, Nat.sub(X.clz(d), 11n)) == u : Bool}) -> {F.sm_exact3(s, e1, d, Nat.sub(X.clz(d), 11n), u) == SF.round(s, D, Nat.add(1926n, e1)) : F.F64}:
  match u:
    case True{}:
      +hb = BL.bl_le(52n, D, hD, Nat.is_le(M.bit_length(D), 52n), {==})
      +eb = NM.clz_t(d, D, hd, hb)
      +hlt = L.subst(Nat, z => {Nat.is_lt(e1, z) == True{} : Bool}, Nat.sub(X.clz(d), 11n), Nat.sub(53n, M.bit_length(D)), eb, hu)
      +h53 = N.le_trans(M.bit_length(D), 52n, 53n, hb, {==})
      +hl = lt_add_sub(e1, M.bit_length(D), 53n, hlt, h53)
      +fK = SH.fits_mono(Nat.add(e1, M.bit_length(D)), 52n, C.shift(e1, D), hl, Equal.trans(Bool, C.fits(Nat.add(e1, M.bit_length(D)), C.shift(e1, D)), C.fits(M.bit_length(D), D), True{}, RT.fits_sh(e1, M.bit_length(D), D), RT.bl_fit(D)))
      +hj = N.le_trans(Nat.add(e1, M.bit_length(D)), 52n, 64n, hl, {==})
      +hk = N.le_lt_trans(e1, Nat.add(e1, M.bit_length(D)), 64n, N.le_add_right(e1, M.bit_length(D)), N.le_lt_trans(Nat.add(e1, M.bit_length(D)), 52n, 64n, hl, {==}))
      +ha = L.subst(Nat, z => {C.fits(M.bit_length(D), z) == True{} : Bool}, D, SW.value(d), Equal.sym(Nat, SW.value(d), D, hd), RT.bl_fit(D))
      +ev = Equal.trans(Nat, SW.value(X.shl(d, e1)), C.shift(e1, SW.value(d)), C.shift(e1, D), AC.shl_v(d, e1, M.bit_length(D), hk, hj, ha), Equal.cong(Nat, Nat, z => C.shift(e1, z), SW.value(d), D, hd))
      +f53 = SH.fits_mono(52n, 53n, C.shift(e1, D), {==}, fK)
      +f63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, C.shift(e1, D), Nat.add(C.shift(e1, D), C.shift(52n, 0n)), Equal.sym(Nat, Nat.add(C.shift(e1, D), C.shift(52n, 0n)), C.shift(e1, D), N.add_zero(C.shift(e1, D))), SH.fits_mono(52n, 63n, C.shift(e1, D), {==}, fK))
      +hn = L.subst(Nat, z => {C.fits(63n, Nat.add(z, C.shift(52n, 0n))) == True{} : Bool}, C.shift(e1, D), SW.value(X.shl(d, e1)), Equal.sym(Nat, SW.value(X.shl(d, e1)), C.shift(e1, D), ev), f63)
      +i1 = FR.pack_v(s, 0n, {==}, X.shl(d, e1), hn)
      +i2 = Equal.cong(Nat, F.F64, z => FR.bits(s, Nat.add(z, C.shift(52n, 0n))), SW.value(X.shl(d, e1)), C.shift(e1, D), ev)
      +r1 = AC.r1926(one, h1, s, C.shift(e1, D), f53, 1926n, {==}, Nat.is_eq(C.shift(e1, D), 0n), {==})
      +r0 = RT.round_shift(s, e1, D, 1926n)
      Equal.trans(F.F64, F.pack(s, 0n, X.shl(d, e1)), FR.bits(s, Nat.add(SW.value(X.shl(d, e1)), C.shift(52n, 0n))), SF.round(s, D, Nat.add(1926n, e1)), i1, Equal.trans(F.F64, FR.bits(s, Nat.add(SW.value(X.shl(d, e1)), C.shift(52n, 0n))), FR.bits(s, Nat.add(C.shift(e1, D), C.shift(52n, 0n))), SF.round(s, D, Nat.add(1926n, e1)), i2, Equal.trans(F.F64, FR.bits(s, Nat.add(C.shift(e1, D), C.shift(52n, 0n))), SF.round(s, C.shift(e1, D), 1926n), SF.round(s, D, Nat.add(1926n, e1)), Equal.sym(F.F64, SF.round(s, C.shift(e1, D), 1926n), FR.bits(s, Nat.add(C.shift(e1, D), C.shift(52n, 0n))), r1), r0)))
    case False{}:
      +hle = N.not_lt_le(e1, Nat.sub(X.clz(d), 11n), hu)
      +eEs = Equal.trans(Nat, Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)), Nat.add(Nat.sub(X.clz(d), 11n), Nat.sub(e1, Nat.sub(X.clz(d), 11n))), e1, NA.add_comm(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)), N.sub_add(e1, Nat.sub(X.clz(d), 11n), hle))
      +hEe = L.subst(Nat, z => {Nat.is_le(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), z) == True{} : Bool}, Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)), e1, eEs, N.le_add_right(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)))
      +hovE = N.le_lt_trans(Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1n), Nat.add(e1, 1n), 2047n, Equal.trans(Bool, Nat.is_le(Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1n), Nat.add(e1, 1n)), Nat.is_le(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), e1), True{}, FR.le_cancel_r(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), e1, 1n), hEe), hov)
      +fM = NM.sub_fit(d, D, hd, hD, hz)
      +nM = NM.sub_nfit(d, D, hd, hD, hz)
      +ev = NM.sub_val(d, D, hd, hD, hz)
      +hq = N.lt_le(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(53n, one), Equal.trans(Bool, Nat.is_lt(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(53n, one)), C.fits(53n, C.shift(Nat.sub(X.clz(d), 11n), D)), True{}, FR.lt_fit(53n, one, h1, C.shift(Nat.sub(X.clz(d), 11n), D)), fM))
      +hovq = L.subst(Bool, t => {Nat.is_lt(Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), SF.pick(Nat, t, 1n, 2n)), 2047n) == True{} : Bool}, True{}, C.fits(53n, C.shift(Nat.sub(X.clz(d), 11n), D)), Equal.sym(Bool, C.fits(53n, C.shift(Nat.sub(X.clz(d), 11n), D)), True{}, fM), hovE)
      +q63 = FR.qfit(one, h1, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.sub(e1, Nat.sub(X.clz(d), 11n)), hq, nM, hovq)
      +hn = L.subst(Nat, z => {C.fits(63n, Nat.add(z, C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))) == True{} : Bool}, C.shift(Nat.sub(X.clz(d), 11n), D), SW.value(X.shl(d, Nat.sub(X.clz(d), 11n))), Equal.sym(Nat, SW.value(X.shl(d, Nat.sub(X.clz(d), 11n))), C.shift(Nat.sub(X.clz(d), 11n), D), ev), q63)
      +i1 = FR.pack_v(s, Nat.sub(e1, Nat.sub(X.clz(d), 11n)), FR.ef11(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1n, hovE), X.shl(d, Nat.sub(X.clz(d), 11n)), hn)
      +i2 = Equal.cong(Nat, F.F64, z => FR.bits(s, Nat.add(z, C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), SW.value(X.shl(d, Nat.sub(X.clz(d), 11n))), C.shift(Nat.sub(X.clz(d), 11n), D), ev)
      +XQ = Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))
      +ek = Equal.trans(Nat, Nat.sub(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), 1926n), Nat.sub(Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1926n), 1926n), Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Equal.cong(Nat, Nat, z => Nat.sub(z, 1926n), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1926n), NA.add_comm(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))), FR.sub_add_l(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), 1926n))
      +hovx = L.subst(Nat, z => {Nat.is_lt(Nat.add(z, 1n), 2047n) == True{} : Bool}, Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), 1926n), Equal.sym(Nat, Nat.sub(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), 1926n), Nat.sub(e1, Nat.sub(X.clz(d), 11n)), ek), hovE)
      +r1 = NP.rq(one, h1, s, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), fM, nM, N.le_add_right(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), hovx)
      +r2 = Equal.cong(Nat, F.F64, z => FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, z))), Nat.sub(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), 1926n), Nat.sub(e1, Nat.sub(X.clz(d), 11n)), ek)
      +r0 = RT.round_shift(s, Nat.sub(X.clz(d), 11n), D, Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))
      +ex = Equal.trans(Nat, Nat.add(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), Nat.sub(X.clz(d), 11n)), Nat.add(1926n, Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n))), Nat.add(1926n, e1), NA.add_assoc(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)), Equal.cong(Nat, Nat, z => Nat.add(1926n, z), Nat.add(Nat.sub(e1, Nat.sub(X.clz(d), 11n)), Nat.sub(X.clz(d), 11n)), e1, eEs))
      +r3 = Equal.cong(Nat, F.F64, z => SF.round(s, D, z), Nat.add(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), Nat.sub(X.clz(d), 11n)), Nat.add(1926n, e1), ex)
      +lhs = Equal.trans(F.F64, F.pack(s, Nat.sub(e1, Nat.sub(X.clz(d), 11n)), X.shl(d, Nat.sub(X.clz(d), 11n))), FR.bits(s, Nat.add(SW.value(X.shl(d, Nat.sub(X.clz(d), 11n))), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), i1, i2)
      +rhs = Equal.trans(F.F64, SF.round(s, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))), FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), 1926n)))), FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), r1, r2)
      +sp = Equal.trans(F.F64, SF.round(s, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))), SF.round(s, D, Nat.add(Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))), Nat.sub(X.clz(d), 11n))), SF.round(s, D, Nat.add(1926n, e1)), r0, r3)
      Equal.trans(F.F64, F.pack(s, Nat.sub(e1, Nat.sub(X.clz(d), 11n)), X.shl(d, Nat.sub(X.clz(d), 11n))), FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), SF.round(s, D, Nat.add(1926n, e1)), lhs, Equal.trans(F.F64, FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), SF.round(s, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))), SF.round(s, D, Nat.add(1926n, e1)), Equal.sym(F.F64, SF.round(s, C.shift(Nat.sub(X.clz(d), 11n), D), Nat.add(1926n, Nat.sub(e1, Nat.sub(X.clz(d), 11n)))), FR.bits(s, Nat.add(C.shift(Nat.sub(X.clz(d), 11n), D), C.shift(52n, Nat.sub(e1, Nat.sub(X.clz(d), 11n))))), rhs), sp))

# SoftFloat's exact equal-exponent difference is the rounded difference
def smx(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e1: Nat, +d: WU.U64, +D: Nat, +hd: {SW.value(d) == D : Nat}, +hD: {C.fits(52n, D) == True{} : Bool}, +hz: {Nat.is_eq(D, 0n) == False{} : Bool}, +hov: {Nat.is_lt(Nat.add(e1, 1n), 2047n) == True{} : Bool}) -> {F.sm_exact(s, e1, d) == SF.round(s, D, Nat.add(1926n, e1)) : F.F64}:
  smx_c(one, h1, s, e1, d, D, hd, hD, hz, hov, Nat.is_lt(e1, Nat.sub(X.clz(d), 11n)), {==})
