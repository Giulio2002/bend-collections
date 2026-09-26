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
import ../../lib/u32half.bend as UH
import ../../lib/word.bend as WD
import ../natural/bits.bend as BT
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64clz.bend as CLZ
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64bl.bend as BL
import ./f64cmp.bend as FC

# SoftFloat's normSubnormalF64Sig and the hidden bit: a finite nonzero
# double's significand as a 53-bit A = m * 2^sa (m the spec's mant) at the
# offset exponent norm_e, with norm_e + sa = xexp + 2171.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def sa(+ea: Nat, +fa: WU.U64) -> Nat:
  match ea:
    case 0n:
      Nat.sub(X.clz(fa), 11n)
    case _:
      0n

# the hidden bit: f + 2^52 for a fraction below 2^52
def hid(+one: Nat, +h1: {one == 1n : Nat}, +fa: WU.U64, +hF: {C.fits(52n, SW.value(fa)) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 20n)} : U32}) -> {SW.value(X.add(fa, WU.U64{0, c})) == Nat.add(SW.value(fa), C.shift(52n, one)) : Nat}:
  a1 = WA.add_value(fa, WU.U64{0, c})
  +ec = Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(20n, one)), C.shift(52n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(20n, one), FB.pwv(20n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(52n, one), C.shift(32n, C.shift(20n, one)), WW.shift_comp(32n, 20n, one)))
  +f53 = WW.limbs_fit(52n, 1n, SW.value(fa), one, hF, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))
  +f64 = SH.fits_mono(53n, 64n, Nat.add(SW.value(fa), C.shift(52n, one)), {==}, f53)
  Equal.trans(Nat, SW.value(X.add(fa, WU.U64{0, c})), C.low(64n, Nat.add(SW.value(fa), C.shift(32n, v(c)))), Nat.add(SW.value(fa), C.shift(52n, one)), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(fa), C.shift(32n, v(c)))), C.low(64n, Nat.add(SW.value(fa), C.shift(52n, one))), Nat.add(SW.value(fa), C.shift(52n, one)), Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(SW.value(fa), z)), C.shift(32n, v(c)), C.shift(52n, one), ec), WW.low_fit(64n, Nat.add(SW.value(fa), C.shift(52n, one)), f64)))

# ---- a subnormal fraction shifted up to bit 52 ----

def clz_t(+fa: WU.U64, +Fr: Nat, +hfa: {SW.value(fa) == Fr : Nat}, +hb: {Nat.is_le(M.bit_length(Fr), 52n) == True{} : Bool}) -> {Nat.sub(X.clz(fa), 11n) == Nat.sub(53n, M.bit_length(Fr)) : Nat}:
  +ec = Equal.trans(Nat, X.clz(fa), Nat.sub(64n, M.bit_length(SW.value(fa))), Nat.sub(64n, M.bit_length(Fr)), CLZ.clz_value(fa), Equal.cong(Nat, Nat, z => Nat.sub(64n, M.bit_length(z)), SW.value(fa), Fr, hfa))
  +hb53 = N.le_trans(M.bit_length(Fr), 52n, 53n, hb, {==})
  +e1 = Equal.cong(Nat, Nat, z => Nat.sub(z, 11n), X.clz(fa), Nat.sub(64n, M.bit_length(Fr)), ec)
  +e2 = Equal.cong(Nat, Nat, z => Nat.sub(z, 11n), Nat.sub(64n, M.bit_length(Fr)), Nat.add(11n, Nat.sub(53n, M.bit_length(Fr))), FR.sub_add_a(11n, 53n, M.bit_length(Fr), hb53))
  Equal.trans(Nat, Nat.sub(X.clz(fa), 11n), Nat.sub(Nat.sub(64n, M.bit_length(Fr)), 11n), Nat.sub(53n, M.bit_length(Fr)), e1, Equal.trans(Nat, Nat.sub(Nat.sub(64n, M.bit_length(Fr)), 11n), Nat.sub(Nat.add(11n, Nat.sub(53n, M.bit_length(Fr))), 11n), Nat.sub(53n, M.bit_length(Fr)), e2, N.add_sub_cancel(11n, Nat.sub(53n, M.bit_length(Fr)))))

def sub_fit(+fa: WU.U64, +Fr: Nat, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hz: {Nat.is_eq(Fr, 0n) == False{} : Bool}) -> {C.fits(53n, C.shift(Nat.sub(X.clz(fa), 11n), Fr)) == True{} : Bool}:
  +hb = BL.bl_le(52n, Fr, hF, Nat.is_le(M.bit_length(Fr), 52n), {==})
  +et = clz_t(fa, Fr, hfa, hb)
  +k = Nat.sub(53n, M.bit_length(Fr))
  +hb53 = N.le_trans(M.bit_length(Fr), 52n, 53n, hb, {==})
  +ek = Equal.trans(Nat, Nat.add(k, M.bit_length(Fr)), Nat.add(M.bit_length(Fr), k), 53n, NA.add_comm(k, M.bit_length(Fr)), N.sub_add(53n, M.bit_length(Fr), hb53))
  +hqu = L.subst(Nat, z => {Nat.is_lt(C.shift(k, Fr), z) == True{} : Bool}, C.shift(k, C.pow2(M.bit_length(Fr))), C.pow2(Nat.add(k, M.bit_length(Fr))), WW.shift_pow2(k, M.bit_length(Fr)), WW.shift_lt(k, Fr, C.pow2(M.bit_length(Fr)), BT.bit_length_lt(Fr)))
  +f53 = L.subst(Nat, z => {C.fits(z, C.shift(k, Fr)) == True{} : Bool}, Nat.add(k, M.bit_length(Fr)), 53n, ek, WW.fits_of_lt(Nat.add(k, M.bit_length(Fr)), C.shift(k, Fr), hqu))
  L.subst(Nat, z => {C.fits(53n, C.shift(z, Fr)) == True{} : Bool}, k, Nat.sub(X.clz(fa), 11n), Equal.sym(Nat, Nat.sub(X.clz(fa), 11n), k, et), f53)

def sub_nfit(+fa: WU.U64, +Fr: Nat, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hz: {Nat.is_eq(Fr, 0n) == False{} : Bool}) -> {C.fits(52n, C.shift(Nat.sub(X.clz(fa), 11n), Fr)) == False{} : Bool}:
  +hb = BL.bl_le(52n, Fr, hF, Nat.is_le(M.bit_length(Fr), 52n), {==})
  +et = clz_t(fa, Fr, hfa, hb)
  +k = Nat.sub(53n, M.bit_length(Fr))
  +hb53 = N.le_trans(M.bit_length(Fr), 52n, 53n, hb, {==})
  +ek = Equal.trans(Nat, Nat.add(k, M.bit_length(Fr)), Nat.add(M.bit_length(Fr), k), 53n, NA.add_comm(k, M.bit_length(Fr)), N.sub_add(53n, M.bit_length(Fr), hb53))
  +pb = Nat.sub(M.bit_length(Fr), 1n)
  +epb = N.sub_add(M.bit_length(Fr), 1n, BL.bl_pos(Fr, hz, M.bit_length(Fr), {==}))
  +K2 = Nat.add(k, pb)
  +e52 = N.succ_inj(K2, 52n, Equal.trans(Nat, 1n+K2, Nat.add(k, 1n+pb), 53n, Equal.sym(Nat, Nat.add(k, 1n+pb), 1n+K2, N.add_succ(k, pb)), Equal.trans(Nat, Nat.add(k, 1n+pb), Nat.add(k, M.bit_length(Fr)), 53n, Equal.cong(Nat, Nat, z => Nat.add(k, z), 1n+pb, M.bit_length(Fr), epb), ek)))
  +hql = L.subst(Nat, z => {Nat.is_le(z, C.shift(k, Fr)) == True{} : Bool}, C.shift(k, C.pow2(pb)), C.pow2(K2), WW.shift_pow2(k, pb), WW.shift_mono(k, C.pow2(pb), Fr, BL.lower(Fr, hz)))
  +nf = Equal.trans(Bool, C.fits(K2, C.pow2(K2)), Nat.is_lt(C.pow2(K2), C.pow2(K2)), False{}, WW.fits_lt(K2, C.pow2(K2)), N.lt_irrefl(C.pow2(K2)))
  +f52 = L.subst(Nat, z => {C.fits(z, C.shift(k, Fr)) == False{} : Bool}, K2, 52n, e52, FR.nfit(K2, C.pow2(K2), C.shift(k, Fr), hql, nf))
  L.subst(Nat, z => {C.fits(52n, C.shift(z, Fr)) == False{} : Bool}, k, Nat.sub(X.clz(fa), 11n), Equal.sym(Nat, Nat.sub(X.clz(fa), 11n), k, et), f52)

def sub_val(+fa: WU.U64, +Fr: Nat, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hz: {Nat.is_eq(Fr, 0n) == False{} : Bool}) -> {SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))) == C.shift(Nat.sub(X.clz(fa), 11n), Fr) : Nat}:
  +hb = BL.bl_le(52n, Fr, hF, Nat.is_le(M.bit_length(Fr), 52n), {==})
  +et = clz_t(fa, Fr, hfa, hb)
  +hk = N.le_lt_trans(Nat.sub(X.clz(fa), 11n), 53n, 64n, L.subst(Nat, z => {Nat.is_le(z, 53n) == True{} : Bool}, Nat.sub(53n, M.bit_length(Fr)), Nat.sub(X.clz(fa), 11n), Equal.sym(Nat, Nat.sub(X.clz(fa), 11n), Nat.sub(53n, M.bit_length(Fr)), et), UH.sub_le(53n, M.bit_length(Fr))), {==})
  sv = SH.shl_value(fa, Nat.sub(X.clz(fa), 11n), hk)
  Equal.trans(Nat, SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), C.low(64n, C.shift(Nat.sub(X.clz(fa), 11n), SW.value(fa))), C.shift(Nat.sub(X.clz(fa), 11n), Fr), sv, Equal.trans(Nat, C.low(64n, C.shift(Nat.sub(X.clz(fa), 11n), SW.value(fa))), C.low(64n, C.shift(Nat.sub(X.clz(fa), 11n), Fr)), C.shift(Nat.sub(X.clz(fa), 11n), Fr), Equal.cong(Nat, Nat, z => C.low(64n, C.shift(Nat.sub(X.clz(fa), 11n), z)), SW.value(fa), Fr, hfa), WW.low_fit(64n, C.shift(Nat.sub(X.clz(fa), 11n), Fr), SH.fits_mono(53n, 64n, C.shift(Nat.sub(X.clz(fa), 11n), Fr), {==}, sub_fit(fa, Fr, hfa, hF, hz)))))

def sub_sum(+A: Nat, +t: Nat, +B: Nat, +hB: {Nat.is_le(B, t) == True{} : Bool}, +hA: {Nat.is_le(t, A) == True{} : Bool}) -> {Nat.add(Nat.sub(A, t), Nat.sub(t, B)) == Nat.sub(A, B) : Nat}:
  +r = Nat.sub(t, B)
  +q = Nat.sub(A, t)
  +et = N.sub_add(t, B, hB)
  +eA = N.sub_add(A, t, hA)
  +e1 = Equal.trans(Nat, Nat.sub(A, B), Nat.sub(Nat.add(t, q), B), Nat.add(q, r), Equal.cong(Nat, Nat, z => Nat.sub(z, B), A, Nat.add(t, q), Equal.sym(Nat, Nat.add(t, q), A, eA)), Equal.trans(Nat, Nat.sub(Nat.add(t, q), B), Nat.sub(Nat.add(Nat.add(B, r), q), B), Nat.add(q, r), Equal.cong(Nat, Nat, z => Nat.sub(Nat.add(z, q), B), t, Nat.add(B, r), Equal.sym(Nat, Nat.add(B, r), t, et)), Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(B, r), q), B), Nat.sub(Nat.add(B, Nat.add(r, q)), B), Nat.add(q, r), Equal.cong(Nat, Nat, z => Nat.sub(z, B), Nat.add(Nat.add(B, r), q), Nat.add(B, Nat.add(r, q)), NA.add_assoc(B, r, q)), Equal.trans(Nat, Nat.sub(Nat.add(B, Nat.add(r, q)), B), Nat.add(r, q), Nat.add(q, r), N.add_sub_cancel(B, Nat.add(r, q)), NA.add_comm(r, q)))))
  Equal.sym(Nat, Nat.sub(A, B), Nat.add(q, r), e1)

def ez0(+E: Nat, +hea: {0n == E : Nat}) -> {Nat.is_eq(E, 0n) == True{} : Bool}:
  Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), E, 0n, Equal.sym(Nat, 0n, E, hea))

def ezs(+p: Nat, +E: Nat, +hea: {1n+p == E : Nat}) -> {Nat.is_eq(E, 0n) == False{} : Bool}:
  Equal.sym(Bool, False{}, Nat.is_eq(E, 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+p, E, hea))

# the normalized significand
def n1(+one: Nat, +h1: {one == 1n : Nat}, +ea: Nat, +fa: WU.U64, +E: Nat, +Fr: Nat, +hea: {ea == E : Nat}, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hnz: {Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Fr, 0n)) == False{} : Bool}) -> {SW.value(F.norm_f(ea, fa)) == C.shift(sa(ea, fa), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n)))))) : Nat}:
  match ea:
    case 0n:
      +ez = ez0(E, hea)
      +hz = L.subst(Bool, t => {Bool.and(t, Nat.is_eq(Fr, 0n)) == False{} : Bool}, Nat.is_eq(E, 0n), True{}, ez, hnz)
      +em = Equal.trans(Nat, Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), Nat.add(Fr, 0n), Fr, Equal.cong(Bool, Nat, t => Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(t)))), Nat.is_eq(E, 0n), True{}, ez), N.add_zero(Fr))
      Equal.trans(Nat, SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), C.shift(Nat.sub(X.clz(fa), 11n), Fr), C.shift(Nat.sub(X.clz(fa), 11n), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n)))))), sub_val(fa, Fr, hfa, hF, hz), Equal.cong(Nat, Nat, z => C.shift(Nat.sub(X.clz(fa), 11n), z), Fr, Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), Equal.sym(Nat, Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), Fr, em)))
    case 1n+ +p:
      +ez = ezs(p, E, hea)
      +ec = Equal.trans(Nat, SF.b2n(Bool.not(Nat.is_eq(E, 0n))), 1n, one, Equal.cong(Bool, Nat, t => SF.b2n(Bool.not(t)), Nat.is_eq(E, 0n), False{}, ez), Equal.sym(Nat, one, 1n, h1))
      +em = Equal.cong(Nat, Nat, z => Nat.add(Fr, C.shift(52n, z)), SF.b2n(Bool.not(Nat.is_eq(E, 0n))), one, ec)
      +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fr, SW.value(fa), Equal.sym(Nat, SW.value(fa), Fr, hfa), hF)
      Equal.trans(Nat, SW.value(X.add(fa, WU.U64{0, 1048576})), Nat.add(SW.value(fa), C.shift(52n, one)), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), hid(one, h1, fa, hFv, 1048576, {==}), Equal.trans(Nat, Nat.add(SW.value(fa), C.shift(52n, one)), Nat.add(Fr, C.shift(52n, one)), Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(52n, one)), SW.value(fa), Fr, hfa), Equal.sym(Nat, Nat.add(Fr, C.shift(52n, SF.b2n(Bool.not(Nat.is_eq(E, 0n))))), Nat.add(Fr, C.shift(52n, one)), em)))

# the exponent: norm_e + sa = xexp + 2171
def n2(+ea: Nat, +fa: WU.U64, +E: Nat, +Fr: Nat, +hea: {ea == E : Nat}, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hnz: {Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Fr, 0n)) == False{} : Bool}) -> {Nat.add(F.norm_e(ea, fa), sa(ea, fa)) == Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n) : Nat}:
  match ea:
    case 0n:
      +ez = ez0(E, hea)
      +hz = L.subst(Bool, t => {Bool.and(t, Nat.is_eq(Fr, 0n)) == False{} : Bool}, Nat.is_eq(E, 0n), True{}, ez, hnz)
      +hb = BL.bl_le(52n, Fr, hF, Nat.is_le(M.bit_length(Fr), 52n), {==})
      +ec = Equal.trans(Nat, X.clz(fa), Nat.sub(64n, M.bit_length(SW.value(fa))), Nat.sub(64n, M.bit_length(Fr)), CLZ.clz_value(fa), Equal.cong(Nat, Nat, z => Nat.sub(64n, M.bit_length(z)), SW.value(fa), Fr, hfa))
      +h11 = L.subst(Nat, z => {Nat.is_le(11n, z) == True{} : Bool}, Nat.sub(64n, M.bit_length(Fr)), X.clz(fa), Equal.sym(Nat, X.clz(fa), Nat.sub(64n, M.bit_length(Fr)), ec), RT.le_sub(11n, M.bit_length(Fr), 64n, N.le_add_left(M.bit_length(Fr), 53n, 11n, N.le_trans(M.bit_length(Fr), 52n, 53n, hb, {==}))))
      +h4108 = L.subst(Nat, z => {Nat.is_le(z, 4108n) == True{} : Bool}, Nat.sub(64n, M.bit_length(Fr)), X.clz(fa), Equal.sym(Nat, X.clz(fa), Nat.sub(64n, M.bit_length(Fr)), ec), N.le_trans(Nat.sub(64n, M.bit_length(Fr)), 64n, 4108n, UH.sub_le(64n, M.bit_length(Fr)), {==}))
      +l1 = sub_sum(4108n, X.clz(fa), 11n, h11, h4108)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(SF.pick(Nat, t, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), Nat.is_eq(E, 0n), True{}, ez)
      Equal.trans(Nat, Nat.add(Nat.sub(4108n, X.clz(fa)), Nat.sub(X.clz(fa), 11n)), 4097n, Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), l1, Equal.sym(Nat, Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), 4097n, r1))
    case 1n+ +p:
      +ez = ezs(p, E, hea)
      +r1 = Equal.cong(Bool, Nat, t => Nat.add(SF.pick(Nat, t, Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), Nat.is_eq(E, 0n), False{}, ez)
      +r2 = Equal.cong(Nat, Nat, z => Nat.add(z, 2171n), Nat.sub(Nat.add(E, SF.zb()), 1075n), Nat.add(1925n, E), FC.esub(E))
      +r3 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1925n, z), 2171n), E, 1n+p, Equal.sym(Nat, 1n+p, E, hea))
      +r4 = Equal.cong(Nat, Nat, z => Nat.add(1926n, z), Nat.add(p, 2171n), Nat.add(2171n, p), NA.add_comm(p, 2171n))
      +rr = Equal.trans(Nat, Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), Nat.add(Nat.sub(Nat.add(E, SF.zb()), 1075n), 2171n), Nat.add(4096n, 1n+p), r1, Equal.trans(Nat, Nat.add(Nat.sub(Nat.add(E, SF.zb()), 1075n), 2171n), Nat.add(Nat.add(1925n, E), 2171n), Nat.add(4096n, 1n+p), r2, Equal.trans(Nat, Nat.add(Nat.add(1925n, E), 2171n), Nat.add(Nat.add(1925n, 1n+p), 2171n), Nat.add(4096n, 1n+p), r3, r4)))
      Equal.trans(Nat, Nat.add(Nat.add(F.off(), 1n+p), 0n), Nat.add(4096n, 1n+p), Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), N.add_zero(Nat.add(F.off(), 1n+p)), Equal.sym(Nat, Nat.add(SF.pick(Nat, Nat.is_eq(E, 0n), Nat.sub(SF.zb(), 1074n), Nat.sub(Nat.add(E, SF.zb()), 1075n)), 2171n), Nat.add(4096n, 1n+p), rr))

# the normalized significand has its top bit at 52
def n3a(+one: Nat, +h1: {one == 1n : Nat}, +ea: Nat, +fa: WU.U64, +E: Nat, +Fr: Nat, +hea: {ea == E : Nat}, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hnz: {Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Fr, 0n)) == False{} : Bool}) -> {C.fits(53n, SW.value(F.norm_f(ea, fa))) == True{} : Bool}:
  match ea:
    case 0n:
      +ez = ez0(E, hea)
      +hz = L.subst(Bool, t => {Bool.and(t, Nat.is_eq(Fr, 0n)) == False{} : Bool}, Nat.is_eq(E, 0n), True{}, ez, hnz)
      L.subst(Nat, z => {C.fits(53n, z) == True{} : Bool}, C.shift(Nat.sub(X.clz(fa), 11n), Fr), SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), Equal.sym(Nat, SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), C.shift(Nat.sub(X.clz(fa), 11n), Fr), sub_val(fa, Fr, hfa, hF, hz)), sub_fit(fa, Fr, hfa, hF, hz))
    case 1n+ +p:
      +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fr, SW.value(fa), Equal.sym(Nat, SW.value(fa), Fr, hfa), hF)
      +f = WW.limbs_fit(52n, 1n, SW.value(fa), one, hFv, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))
      L.subst(Nat, z => {C.fits(53n, z) == True{} : Bool}, Nat.add(SW.value(fa), C.shift(52n, one)), SW.value(X.add(fa, WU.U64{0, 1048576})), Equal.sym(Nat, SW.value(X.add(fa, WU.U64{0, 1048576})), Nat.add(SW.value(fa), C.shift(52n, one)), hid(one, h1, fa, hFv, 1048576, {==})), f)

def n3b(+one: Nat, +h1: {one == 1n : Nat}, +ea: Nat, +fa: WU.U64, +E: Nat, +Fr: Nat, +hea: {ea == E : Nat}, +hfa: {SW.value(fa) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hnz: {Bool.and(Nat.is_eq(E, 0n), Nat.is_eq(Fr, 0n)) == False{} : Bool}) -> {C.fits(52n, SW.value(F.norm_f(ea, fa))) == False{} : Bool}:
  match ea:
    case 0n:
      +ez = ez0(E, hea)
      +hz = L.subst(Bool, t => {Bool.and(t, Nat.is_eq(Fr, 0n)) == False{} : Bool}, Nat.is_eq(E, 0n), True{}, ez, hnz)
      L.subst(Nat, z => {C.fits(52n, z) == False{} : Bool}, C.shift(Nat.sub(X.clz(fa), 11n), Fr), SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), Equal.sym(Nat, SW.value(X.shl(fa, Nat.sub(X.clz(fa), 11n))), C.shift(Nat.sub(X.clz(fa), 11n), Fr), sub_val(fa, Fr, hfa, hF, hz)), sub_nfit(fa, Fr, hfa, hF, hz))
    case 1n+ +p:
      +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fr, SW.value(fa), Equal.sym(Nat, SW.value(fa), Fr, hfa), hF)
      +nf = Equal.trans(Bool, C.fits(52n, C.shift(52n, one)), Nat.is_lt(C.shift(52n, one), C.shift(52n, one)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(52n, one), C.shift(52n, one)), C.fits(52n, C.shift(52n, one)), FR.lt_fit(52n, one, h1, C.shift(52n, one))), N.lt_irrefl(C.shift(52n, one)))
      +hle = L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), z) == True{} : Bool}, Nat.add(C.shift(52n, one), SW.value(fa)), Nat.add(SW.value(fa), C.shift(52n, one)), NA.add_comm(C.shift(52n, one), SW.value(fa)), N.le_add_right(C.shift(52n, one), SW.value(fa)))
      L.subst(Nat, z => {C.fits(52n, z) == False{} : Bool}, Nat.add(SW.value(fa), C.shift(52n, one)), SW.value(X.add(fa, WU.U64{0, 1048576})), Equal.sym(Nat, SW.value(X.add(fa, WU.U64{0, 1048576})), Nat.add(SW.value(fa), C.shift(52n, one)), hid(one, h1, fa, hFv, 1048576, {==})), FR.nfit(52n, C.shift(52n, one), Nat.add(SW.value(fa), C.shift(52n, one)), hle, nf))
