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
import ../../lib/u32half.bend as UH
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64adda.bend as AA
import ./f64addp.bend as AP
import ./f64adds.bend as AS

# subMagsF64 for el > es, in terms of the spec's exact difference.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def c62(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {SW.value(WU.U64{0, c}) == C.shift(62n, one) : Nat}:
  Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(30n, one)), C.shift(62n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(30n, one), FB.pwv(30n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(62n, one), C.shift(32n, C.shift(30n, one)), WW.shift_comp(32n, 30n, one)))

# f << 10 plus the hidden bit at 62, with the constant on either side
def top10(+one: Nat, +h1: {one == 1n : Nat}, +f: WU.U64, +Fr: Nat, +hf: {SW.value(f) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 30n)} : U32}) -> {SW.value(X.add(X.shl(f, 10n), WU.U64{0, c})) == C.shift(10n, Nat.add(Fr, C.shift(52n, one))) : Nat}:
  +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fr, SW.value(f), Equal.sym(Nat, SW.value(f), Fr, hf), hF)
  +e10 = Equal.trans(Nat, SW.value(X.shl(f, 10n)), C.shift(10n, SW.value(f)), C.shift(10n, Fr), AA.shl_v(f, 10n, 52n, {==}, {==}, hFv), Equal.cong(Nat, Nat, z => C.shift(10n, z), SW.value(f), Fr, hf))
  a1 = WA.add_value(X.shl(f, 10n), WU.U64{0, c})
  +es = Equal.trans(Nat, Nat.add(SW.value(X.shl(f, 10n)), SW.value(WU.U64{0, c})), Nat.add(C.shift(10n, Fr), SW.value(WU.U64{0, c})), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(WU.U64{0, c})), SW.value(X.shl(f, 10n)), C.shift(10n, Fr), e10), Equal.trans(Nat, Nat.add(C.shift(10n, Fr), SW.value(WU.U64{0, c})), Nat.add(C.shift(10n, Fr), C.shift(62n, one)), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(10n, Fr), z), SW.value(WU.U64{0, c}), C.shift(62n, one), c62(one, h1, c, hc)), Equal.trans(Nat, Nat.add(C.shift(10n, Fr), C.shift(62n, one)), Nat.add(C.shift(10n, Fr), C.shift(10n, C.shift(52n, one))), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(10n, Fr), z), C.shift(62n, one), C.shift(10n, C.shift(52n, one)), WW.shift_comp(10n, 52n, one)), Equal.sym(Nat, C.shift(10n, Nat.add(Fr, C.shift(52n, one))), Nat.add(C.shift(10n, Fr), C.shift(10n, C.shift(52n, one))), WW.shift_add(10n, Fr, C.shift(52n, one))))))
  +f63 = SH.fits_mono(Nat.add(10n, 53n), 64n, C.shift(10n, Nat.add(Fr, C.shift(52n, one))), {==}, Equal.trans(Bool, C.fits(Nat.add(10n, 53n), C.shift(10n, Nat.add(Fr, C.shift(52n, one)))), C.fits(53n, Nat.add(Fr, C.shift(52n, one))), True{}, RT.fits_sh(10n, 53n, Nat.add(Fr, C.shift(52n, one))), AA.f53(one, h1, Fr, hF)))
  Equal.trans(Nat, SW.value(X.add(X.shl(f, 10n), WU.U64{0, c})), C.low(64n, Nat.add(SW.value(X.shl(f, 10n)), SW.value(WU.U64{0, c}))), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(X.shl(f, 10n)), SW.value(WU.U64{0, c}))), C.low(64n, C.shift(10n, Nat.add(Fr, C.shift(52n, one)))), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(X.shl(f, 10n)), SW.value(WU.U64{0, c})), C.shift(10n, Nat.add(Fr, C.shift(52n, one))), es), WW.low_fit(64n, C.shift(10n, Nat.add(Fr, C.shift(52n, one))), f63)))

# the value of T - jam(S >> d) as a U64 subtraction
def subv(+tw: WU.U64, +sw: WU.U64, +t: Nat, +S: Nat, +d: Nat, +ht: {SW.value(tw) == Nat.double(t) : Nat}, +hs: {SW.value(sw) == S : Nat}, +hle: {Nat.is_le(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)) == True{} : Bool}) -> {SW.value(X.sub(tw, X.shr_jam(sw, d))) == Nat.sub(Nat.double(t), SW.jam(C.high(d, S), C.low(d, S))) : Nat}:
  sj = SH.shr_jam_value(sw, d)
  +JJ = SW.jam(C.high(d, S), C.low(d, S))
  +ej = Equal.trans(Nat, SW.value(X.shr_jam(sw, d)), SW.jam(C.high(d, SW.value(sw)), C.low(d, SW.value(sw))), JJ, sj, Equal.cong(Nat, Nat, z => SW.jam(C.high(d, z), C.low(d, z)), SW.value(sw), S, hs))
  +hle2 = L.subst(Nat, z => {Nat.is_le(z, SW.value(tw)) == True{} : Bool}, JJ, SW.value(X.shr_jam(sw, d)), Equal.sym(Nat, SW.value(X.shr_jam(sw, d)), JJ, ej), L.subst(Nat, z => {Nat.is_le(JJ, z) == True{} : Bool}, Nat.double(t), SW.value(tw), Equal.sym(Nat, SW.value(tw), Nat.double(t), ht), hle))
  s1 = WA.sub_value(tw, X.shr_jam(sw, d), hle2)
  Equal.trans(Nat, SW.value(X.sub(tw, X.shr_jam(sw, d))), Nat.sub(SW.value(tw), SW.value(X.shr_jam(sw, d))), Nat.sub(Nat.double(t), JJ), s1, Equal.trans(Nat, Nat.sub(SW.value(tw), SW.value(X.shr_jam(sw, d))), Nat.sub(Nat.double(t), SW.value(X.shr_jam(sw, d))), Nat.sub(Nat.double(t), JJ), Equal.cong(Nat, Nat, z => Nat.sub(z, SW.value(X.shr_jam(sw, d))), SW.value(tw), Nat.double(t), ht), Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(t), z), SW.value(X.shr_jam(sw, d)), JJ, ej)))

def hlt2(+one: Nat, +h1: {one == 1n : Nat}, +t: Nat, +S1: Nat, +d: Nat, +hd1: {Nat.is_le(1n, d) == True{} : Bool}, +hS: {C.fits(63n, C.shift(10n, S1)) == True{} : Bool}, +hT62: {C.fits(62n, Nat.double(t)) == False{} : Bool}) -> {Nat.is_le(SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1))), Nat.double(t)) == True{} : Bool}:
  +S = C.shift(10n, S1)
  +f62 = Equal.trans(Bool, C.fits(62n, C.high(d, S)), C.fits(Nat.add(d, 62n), S), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 62n), S), C.fits(62n, C.high(d, S)), FR.fits_hc(d, 62n, S)), SH.fits_mono(63n, Nat.add(d, 62n), S, L.subst(Nat, z => {Nat.is_le(63n, z) == True{} : Bool}, Nat.add(62n, d), Nat.add(d, 62n), NA.add_comm(62n, d), N.le_add_left(1n, d, 62n, hd1)), hS))
  +P62 = C.shift(62n, one)
  +hh = N.lt_le_trans(C.high(d, S), P62, Nat.double(t), Equal.trans(Bool, Nat.is_lt(C.high(d, S), P62), C.fits(62n, C.high(d, S)), True{}, FR.lt_fit(62n, one, h1, C.high(d, S)), f62), N.not_lt_le(Nat.double(t), P62, Equal.trans(Bool, Nat.is_lt(Nat.double(t), P62), C.fits(62n, Nat.double(t)), False{}, FR.lt_fit(62n, one, h1, Nat.double(t)), hT62)))
  N.le_trans(SW.jam(C.high(d, S), C.low(d, S)), 1n+C.high(d, S), Nat.double(t), AS.jam_le(C.high(d, S), C.low(d, S)), N.lt_succ_le_succ(C.high(d, S), Nat.double(t), hh))

def f63s(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +Fr: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(k, 53n), 63n) == True{} : Bool}) -> {C.fits(63n, C.shift(k, Nat.add(Fr, C.shift(52n, one)))) == True{} : Bool}:
  SH.fits_mono(Nat.add(k, 53n), 63n, C.shift(k, Nat.add(Fr, C.shift(52n, one))), hk, Equal.trans(Bool, C.fits(Nat.add(k, 53n), C.shift(k, Nat.add(Fr, C.shift(52n, one)))), C.fits(53n, Nat.add(Fr, C.shift(52n, one))), True{}, RT.fits_sh(k, 53n, Nat.add(Fr, C.shift(52n, one))), AA.f53(one, h1, Fr, hF)))

def ms_le(+one: Nat, +h1: {one == 1n : Nat}, +Fl: Nat, +m: Nat, +d: Nat, +hm: {C.fits(53n, m) == True{} : Bool}, +hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.is_le(m, C.shift(d, Nat.add(Fl, C.shift(52n, one)))) == True{} : Bool}:
  +P53 = C.shift(53n, one)
  +h1a = N.lt_le(m, P53, Equal.trans(Bool, Nat.is_lt(m, P53), C.fits(53n, m), True{}, FR.lt_fit(53n, one, h1, m), hm))
  +h2 = L.subst(Nat, z => {Nat.is_le(z, C.shift(1n, Nat.add(Fl, C.shift(52n, one)))) == True{} : Bool}, C.shift(1n, C.shift(52n, one)), P53, Equal.sym(Nat, P53, C.shift(1n, C.shift(52n, one)), WW.shift_comp(1n, 52n, one)), WW.shift_mono(1n, C.shift(52n, one), Nat.add(Fl, C.shift(52n, one)), L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), z) == True{} : Bool}, Nat.add(C.shift(52n, one), Fl), Nat.add(Fl, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fl), N.le_add_right(C.shift(52n, one), Fl))))
  N.le_trans(m, P53, C.shift(d, Nat.add(Fl, C.shift(52n, one))), h1a, N.le_trans(P53, C.shift(1n, Nat.add(Fl, C.shift(52n, one))), C.shift(d, Nat.add(Fl, C.shift(52n, one))), h2, AS.shmk(1n, d, Nat.add(Fl, C.shift(52n, one)), hd)))

# subMags, larger exponent el, smaller exponent es = 1 + p
def smb1(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +p: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(1n+p, el) == True{} : Bool}) -> {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(1n+p, X.shl(fs, 10n)), Nat.sub(el, 1n+p)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(el, 1n+p), Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, 1n+p)) : F.F64}:
  +d = Nat.sub(el, 1n+p)
  +sw = X.add(X.shl(fs, 10n), WU.U64{0, 1073741824})
  +et = top10(one, h1, fl, Fl, hfl, hFl, 1073741824, {==})
  +es = top10(one, h1, fs, Fs, hfs, hFs, 1073741824, {==})
  +eld = N.sub_add(el, 1n+p, N.lt_le(1n+p, el, hlt))
  +hd1 = FR.lt_sub_pos(1n+p, el, hlt)
  +hS = f63s(one, h1, 10n, Fs, hFs, {==})
  +hT63 = f63s(one, h1, 10n, Fl, hFl, {==})
  +hT62 = Equal.trans(Bool, C.fits(Nat.add(10n, 52n), C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.fits(52n, Nat.add(Fl, C.shift(52n, one))), False{}, RT.fits_sh(10n, 52n, Nat.add(Fl, C.shift(52n, one))), AA.n52(one, h1, Fl))
  +hle = hlt2(one, h1, C.shift(9n, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)), d, hd1, hS, hT62)
  +hsig = subv(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), sw, C.shift(9n, Nat.add(Fl, C.shift(52n, one))), C.shift(10n, Nat.add(Fs, C.shift(52n, one))), d, et, es, hle)
  +el1 = N.sub_add(el, 1n, N.le_trans(1n, 1n+p, el, N.zero_le(p), N.lt_le(1n+p, el, hlt)))
  +he = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(1915n, 1n+p), d), 2180n), Nat.add(Nat.add(1915n, Nat.add(1n+p, d)), 2180n), Nat.add(F.off(), Nat.sub(el, 1n)), Equal.cong(Nat, Nat, z => Nat.add(z, 2180n), Nat.add(Nat.add(1915n, 1n+p), d), Nat.add(1915n, Nat.add(1n+p, d)), NA.add_assoc(1915n, 1n+p, d)), Equal.trans(Nat, Nat.add(Nat.add(1915n, Nat.add(1n+p, d)), 2180n), Nat.add(Nat.add(1915n, el), 2180n), Nat.add(F.off(), Nat.sub(el, 1n)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1915n, z), 2180n), Nat.add(1n+p, d), el, eld), Equal.trans(Nat, Nat.add(Nat.add(1915n, el), 2180n), Nat.add(Nat.add(1915n, Nat.add(1n, Nat.sub(el, 1n))), 2180n), Nat.add(F.off(), Nat.sub(el, 1n)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1915n, z), 2180n), el, Nat.add(1n, Nat.sub(el, 1n)), Equal.sym(Nat, Nat.add(1n, Nat.sub(el, 1n)), el, el1)), Equal.trans(Nat, Nat.add(Nat.add(1915n, Nat.add(1n, Nat.sub(el, 1n))), 2180n), Nat.add(1915n, Nat.add(Nat.add(1n, Nat.sub(el, 1n)), 2180n)), Nat.add(F.off(), Nat.sub(el, 1n)), NA.add_assoc(1915n, Nat.add(1n, Nat.sub(el, 1n)), 2180n), Equal.cong(Nat, Nat, z => Nat.add(1915n, z), Nat.add(Nat.add(1n, Nat.sub(el, 1n)), 2180n), Nat.add(2181n, Nat.sub(el, 1n)), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(el, 1n), 2180n), Nat.add(2180n, Nat.sub(el, 1n)), NA.add_comm(Nat.sub(el, 1n), 2180n)))))))
  +hx63 = N.le_trans(63n, Nat.add(1915n, 1n+p), Nat.add(Nat.add(1915n, 1n+p), d), {==}, N.le_add_right(Nat.add(1915n, 1n+p), d))
  +r1 = AS.smb_c(one, h1, s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(1n+p, X.shl(fs, 10n)), Nat.sub(el, 1n+p))), C.shift(9n, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)), d, Nat.add(1915n, 1n+p), hsig, he, hx63, hd1, hS, hT62, hT63, Nat.is_eq(C.low(d, C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), 0n), {==})
  +hmd = ms_le(one, h1, Fl, Nat.add(Fs, C.shift(52n, one)), d, AA.f53(one, h1, Fs, hFs), hd1)
  +eW = Equal.trans(Nat, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), Nat.sub(C.shift(10n, C.shift(d, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), C.shift(10n, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)))), Equal.cong(Nat, Nat, z => Nat.sub(z, C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, C.shift(d, Nat.add(Fl, C.shift(52n, one)))), AA.shc(d, 10n, Nat.add(Fl, C.shift(52n, one)))), AP.sub_shift(10n, C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)), hmd))
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(1915n, 1n+p)), Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), C.shift(10n, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)))), eW)
  +r3 = RT.round_shift(s, 10n, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1915n, 1n+p))
  +r4 = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), z), Nat.add(Nat.add(1915n, 1n+p), 10n), Nat.add(1925n, 1n+p), Equal.cong(Nat, Nat, z => 1916n+z, Nat.add(p, 10n), Nat.add(10n, p), NA.add_comm(p, 10n)))
  Equal.trans(F.F64, F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(1n+p, X.shl(fs, 10n)), Nat.sub(el, 1n+p)))), SF.round(s, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), Nat.add(1915n, 1n+p)), SF.round(s, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, 1n+p)), r1, Equal.trans(F.F64, SF.round(s, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, Nat.add(Fs, C.shift(52n, one)))), Nat.add(1915n, 1n+p)), SF.round(s, C.shift(10n, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)))), Nat.add(1915n, 1n+p)), SF.round(s, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, 1n+p)), r2, Equal.trans(F.F64, SF.round(s, C.shift(10n, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one)))), Nat.add(1915n, 1n+p)), SF.round(s, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(Nat.add(1915n, 1n+p), 10n)), SF.round(s, Nat.sub(C.shift(d, Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, 1n+p)), r3, r4)))

# subMags, the smaller operand subnormal (es = 0)
def smb0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(0n, el) == True{} : Bool}) -> {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(0n, X.shl(fs, 10n)), Nat.sub(el, 0n)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))), Fs), 1926n) : F.F64}:
  +d = Nat.sub(el, 0n)
  +f10 = X.shl(fs, 10n)
  +et = top10(one, h1, fl, Fl, hfl, hFl, 1073741824, {==})
  +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fs, SW.value(fs), Equal.sym(Nat, SW.value(fs), Fs, hfs), hFs)
  +e10 = Equal.trans(Nat, SW.value(f10), C.shift(10n, SW.value(fs)), C.shift(10n, Fs), AA.shl_v(fs, 10n, 52n, {==}, {==}, hFv), Equal.cong(Nat, Nat, z => C.shift(10n, z), SW.value(fs), Fs, hfs))
  +S = C.shift(10n, C.shift(1n, Fs))
  +f53s = Equal.trans(Bool, C.fits(Nat.add(1n, 52n), C.shift(1n, Fs)), C.fits(52n, Fs), True{}, RT.fits_sh(1n, 52n, Fs), hFs)
  +hS = SH.fits_mono(Nat.add(10n, 53n), 63n, S, {==}, Equal.trans(Bool, C.fits(Nat.add(10n, 53n), S), C.fits(53n, C.shift(1n, Fs)), True{}, RT.fits_sh(10n, 53n, C.shift(1n, Fs)), f53s))
  a1 = WA.add_value(f10, f10)
  +eS0 = Equal.trans(Nat, Nat.add(SW.value(f10), SW.value(f10)), Nat.add(C.shift(10n, Fs), C.shift(10n, Fs)), S, Equal.trans(Nat, Nat.add(SW.value(f10), SW.value(f10)), Nat.add(C.shift(10n, Fs), SW.value(f10)), Nat.add(C.shift(10n, Fs), C.shift(10n, Fs)), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(f10)), SW.value(f10), C.shift(10n, Fs), e10), Equal.cong(Nat, Nat, z => Nat.add(C.shift(10n, Fs), z), SW.value(f10), C.shift(10n, Fs), e10)), Equal.trans(Nat, Nat.add(C.shift(10n, Fs), C.shift(10n, Fs)), Nat.double(C.shift(10n, Fs)), S, Equal.sym(Nat, Nat.double(C.shift(10n, Fs)), Nat.add(C.shift(10n, Fs), C.shift(10n, Fs)), NA.double_self(C.shift(10n, Fs))), Equal.sym(Nat, S, Nat.double(C.shift(10n, Fs)), WW.shift_dbl(10n, Fs))))
  +es = Equal.trans(Nat, SW.value(X.add(f10, f10)), C.low(64n, Nat.add(SW.value(f10), SW.value(f10))), S, a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(f10), SW.value(f10))), C.low(64n, S), S, Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(f10), SW.value(f10)), S, eS0), WW.low_fit(64n, S, SH.fits_mono(63n, 64n, S, {==}, hS))))
  +ed = N.sub_zero(el)
  +eq1 = N.sub_add(el, 1n, N.lt_succ_le_succ(0n, el, hlt))
  +hd1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, el, d, Equal.sym(Nat, d, el, ed), N.lt_succ_le_succ(0n, el, hlt))
  +hT63 = f63s(one, h1, 10n, Fl, hFl, {==})
  +hT62 = Equal.trans(Bool, C.fits(Nat.add(10n, 52n), C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.fits(52n, Nat.add(Fl, C.shift(52n, one))), False{}, RT.fits_sh(10n, 52n, Nat.add(Fl, C.shift(52n, one))), AA.n52(one, h1, Fl))
  +hle = hlt2(one, h1, C.shift(9n, Nat.add(Fl, C.shift(52n, one))), C.shift(1n, Fs), d, hd1, hS, hT62)
  +hsig = subv(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.add(f10, f10), C.shift(9n, Nat.add(Fl, C.shift(52n, one))), S, d, et, es, hle)
  +he = Equal.trans(Nat, Nat.add(Nat.add(1915n, d), 2180n), Nat.add(Nat.add(1915n, 1n+Nat.sub(el, 1n)), 2180n), Nat.add(F.off(), Nat.sub(el, 1n)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1915n, z), 2180n), d, 1n+Nat.sub(el, 1n), Equal.trans(Nat, d, el, 1n+Nat.sub(el, 1n), ed, Equal.sym(Nat, 1n+Nat.sub(el, 1n), el, eq1))), Equal.cong(Nat, Nat, z => 1916n+z, Nat.add(Nat.sub(el, 1n), 2180n), Nat.add(2180n, Nat.sub(el, 1n)), NA.add_comm(Nat.sub(el, 1n), 2180n)))
  +hx63 = N.le_trans(63n, 1915n, Nat.add(1915n, d), {==}, N.le_add_right(1915n, d))
  +r1 = AS.smb_c(one, h1, s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(0n, X.shl(fs, 10n)), Nat.sub(el, 0n))), C.shift(9n, Nat.add(Fl, C.shift(52n, one))), C.shift(1n, Fs), d, 1915n, hsig, he, hx63, hd1, hS, hT62, hT63, Nat.is_eq(C.low(d, S), 0n), {==})
  +A = C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))
  +hFA = N.le_trans(Fs, C.shift(52n, one), A, N.lt_le(Fs, C.shift(52n, one), WW.lt_one(52n, one, h1, Fs, hFs)), N.le_trans(C.shift(52n, one), Nat.add(Fl, C.shift(52n, one)), A, L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), z) == True{} : Bool}, Nat.add(C.shift(52n, one), Fl), Nat.add(Fl, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fl), N.le_add_right(C.shift(52n, one), Fl)), WW.shift_ge(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))))
  +eW = Equal.trans(Nat, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), S), Nat.sub(Nat.double(C.shift(Nat.sub(el, 1n), C.shift(10n, Nat.add(Fl, C.shift(52n, one))))), S), C.shift(11n, Nat.sub(A, Fs)), Equal.cong(Nat, Nat, z => Nat.sub(C.shift(z, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), S), d, 1n+Nat.sub(el, 1n), Equal.trans(Nat, d, el, 1n+Nat.sub(el, 1n), ed, Equal.sym(Nat, 1n+Nat.sub(el, 1n), el, eq1))), Equal.trans(Nat, Nat.sub(Nat.double(C.shift(Nat.sub(el, 1n), C.shift(10n, Nat.add(Fl, C.shift(52n, one))))), S), Nat.sub(Nat.double(C.shift(10n, A)), S), C.shift(11n, Nat.sub(A, Fs)), Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(z), S), C.shift(Nat.sub(el, 1n), C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), C.shift(10n, A), AA.shc(Nat.sub(el, 1n), 10n, Nat.add(Fl, C.shift(52n, one)))), Equal.trans(Nat, Nat.sub(Nat.double(C.shift(10n, A)), S), Nat.sub(C.shift(10n, C.shift(1n, A)), S), C.shift(11n, Nat.sub(A, Fs)), Equal.cong(Nat, Nat, z => Nat.sub(z, S), Nat.double(C.shift(10n, A)), C.shift(10n, C.shift(1n, A)), Equal.sym(Nat, C.shift(10n, C.shift(1n, A)), Nat.double(C.shift(10n, A)), WW.shift_dbl(10n, A))), Equal.trans(Nat, Nat.sub(C.shift(10n, C.shift(1n, A)), S), C.shift(10n, Nat.sub(C.shift(1n, A), C.shift(1n, Fs))), C.shift(11n, Nat.sub(A, Fs)), AP.sub_shift(10n, C.shift(1n, A), C.shift(1n, Fs), WW.shift_mono(1n, Fs, A, hFA)), Equal.trans(Nat, C.shift(10n, Nat.sub(C.shift(1n, A), C.shift(1n, Fs))), C.shift(10n, C.shift(1n, Nat.sub(A, Fs))), C.shift(11n, Nat.sub(A, Fs)), Equal.cong(Nat, Nat, z => C.shift(10n, z), Nat.sub(C.shift(1n, A), C.shift(1n, Fs)), C.shift(1n, Nat.sub(A, Fs)), AP.sub_shift(1n, A, Fs, hFA)), Equal.sym(Nat, C.shift(Nat.add(10n, 1n), Nat.sub(A, Fs)), C.shift(10n, C.shift(1n, Nat.sub(A, Fs))), WW.shift_comp(10n, 1n, Nat.sub(A, Fs))))))))
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, 1915n), Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), S), C.shift(11n, Nat.sub(A, Fs)), eW)
  +r3 = RT.round_shift(s, 11n, Nat.sub(A, Fs), 1915n)
  Equal.trans(F.F64, F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(0n, X.shl(fs, 10n)), Nat.sub(el, 0n)))), SF.round(s, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), S), 1915n), SF.round(s, Nat.sub(A, Fs), 1926n), r1, Equal.trans(F.F64, SF.round(s, Nat.sub(C.shift(d, C.shift(10n, Nat.add(Fl, C.shift(52n, one)))), S), 1915n), SF.round(s, C.shift(11n, Nat.sub(A, Fs)), 1915n), SF.round(s, Nat.sub(A, Fs), 1926n), r2, r3))
