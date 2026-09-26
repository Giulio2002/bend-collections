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
import ../../lib/word.bend as WD
import ./width.bend as WW
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./natcmp.bend as NC
import ./f64bits.bend as FB
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64mulp.bend as MP
import ./f64addp.bend as AP
# SoftFloat's addMagsF64 with exponents el > es: the larger significand at
# bit 61, the smaller shifted right with a sticky bit by el - es, summed and
# rounded by rp62, is round of the exact sum.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def shl_v(+a: WU.U64, +k: Nat, +j: Nat, +hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(k, j), 64n) == True{} : Bool}, +ha: {C.fits(j, SW.value(a)) == True{} : Bool}) -> {SW.value(X.shl(a, k)) == C.shift(k, SW.value(a)) : Nat}:
  sv = SH.shl_value(a, k, hk)
  +f = SH.fits_mono(Nat.add(k, j), 64n, C.shift(k, SW.value(a)), hj, Equal.trans(Bool, C.fits(Nat.add(k, j), C.shift(k, SW.value(a))), C.fits(j, SW.value(a)), True{}, RT.fits_sh(k, j, SW.value(a)), ha))
  Equal.trans(Nat, SW.value(X.shl(a, k)), C.low(64n, C.shift(k, SW.value(a))), C.shift(k, SW.value(a)), sv, WW.low_fit(64n, C.shift(k, SW.value(a)), f))

def c61(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {c == U32{WD.pw(32n, 29n)} : U32}) -> {SW.value(WU.U64{0, c}) == C.shift(61n, one) : Nat}:
  Equal.trans(Nat, C.shift(32n, v(c)), C.shift(32n, C.shift(29n, one)), C.shift(61n, one), Equal.cong(Nat, Nat, z => C.shift(32n, z), v(c), C.shift(29n, one), FB.pwv(29n, {==}, one, h1, c, hc)), Equal.sym(Nat, C.shift(61n, one), C.shift(32n, C.shift(29n, one)), WW.shift_comp(32n, 29n, one)))

# f << 9 plus the hidden bit at 61: the significand at bit 61
def top9(+one: Nat, +h1: {one == 1n : Nat}, +f: WU.U64, +Fr: Nat, +hf: {SW.value(f) == Fr : Nat}, +hF: {C.fits(52n, Fr) == True{} : Bool}, +c: U32, +hc: {c == U32{WD.pw(32n, 29n)} : U32}) -> {SW.value(X.add(WU.U64{0, c}, X.shl(f, 9n))) == C.shift(9n, Nat.add(Fr, C.shift(52n, one))) : Nat}:
  +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fr, SW.value(f), Equal.sym(Nat, SW.value(f), Fr, hf), hF)
  +e9 = Equal.trans(Nat, SW.value(X.shl(f, 9n)), C.shift(9n, SW.value(f)), C.shift(9n, Fr), shl_v(f, 9n, 52n, {==}, {==}, hFv), Equal.cong(Nat, Nat, z => C.shift(9n, z), SW.value(f), Fr, hf))
  a1 = WA.add_value(WU.U64{0, c}, X.shl(f, 9n))
  +es = Equal.trans(Nat, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shl(f, 9n))), Nat.add(C.shift(61n, one), SW.value(X.shl(f, 9n))), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(X.shl(f, 9n))), SW.value(WU.U64{0, c}), C.shift(61n, one), c61(one, h1, c, hc)), Equal.trans(Nat, Nat.add(C.shift(61n, one), SW.value(X.shl(f, 9n))), Nat.add(C.shift(61n, one), C.shift(9n, Fr)), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(61n, one), z), SW.value(X.shl(f, 9n)), C.shift(9n, Fr), e9), Equal.trans(Nat, Nat.add(C.shift(61n, one), C.shift(9n, Fr)), Nat.add(C.shift(9n, Fr), C.shift(61n, one)), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), NA.add_comm(C.shift(61n, one), C.shift(9n, Fr)), Equal.trans(Nat, Nat.add(C.shift(9n, Fr), C.shift(61n, one)), Nat.add(C.shift(9n, Fr), C.shift(9n, C.shift(52n, one))), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => Nat.add(C.shift(9n, Fr), z), C.shift(61n, one), C.shift(9n, C.shift(52n, one)), WW.shift_comp(9n, 52n, one)), Equal.sym(Nat, C.shift(9n, Nat.add(Fr, C.shift(52n, one))), Nat.add(C.shift(9n, Fr), C.shift(9n, C.shift(52n, one))), WW.shift_add(9n, Fr, C.shift(52n, one)))))))
  +f53 = WW.limbs_fit(52n, 1n, Fr, one, hF, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))
  +f64 = SH.fits_mono(Nat.add(9n, 53n), 64n, C.shift(9n, Nat.add(Fr, C.shift(52n, one))), {==}, Equal.trans(Bool, C.fits(Nat.add(9n, 53n), C.shift(9n, Nat.add(Fr, C.shift(52n, one)))), C.fits(53n, Nat.add(Fr, C.shift(52n, one))), True{}, RT.fits_sh(9n, 53n, Nat.add(Fr, C.shift(52n, one))), f53))
  Equal.trans(Nat, SW.value(X.add(WU.U64{0, c}, X.shl(f, 9n))), C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shl(f, 9n)))), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shl(f, 9n)))), C.low(64n, C.shift(9n, Nat.add(Fr, C.shift(52n, one)))), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(WU.U64{0, c}), SW.value(X.shl(f, 9n))), C.shift(9n, Nat.add(Fr, C.shift(52n, one))), es), WW.low_fit(64n, C.shift(9n, Nat.add(Fr, C.shift(52n, one))), f64)))

def nlb(+s: Bool, +k: Nat, +m: Nat, +x: Nat, +hk: {C.fits(k, m) == False{} : Bool}, +c: Bool, +hc: {Nat.is_le(1n+k, M.bit_length(m)) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h1 = N.lt_succ_le(M.bit_length(m), k, N.not_le_lt(1n+k, M.bit_length(m), hc))
      NC.absurd_tf({False{} == True{} : Bool}, Equal.trans(Bool, False{}, C.fits(k, m), True{}, Equal.sym(Bool, C.fits(k, m), False{}, hk), SH.fits_mono(M.bit_length(m), k, m, h1, RT.bl_fit(m))))

def nfit_bl(+k: Nat, +m: Nat, +hk: {C.fits(k, m) == False{} : Bool}) -> {Nat.is_le(1n+k, M.bit_length(m)) == True{} : Bool}:
  nlb(False{}, k, m, 0n, hk, Nat.is_le(1n+k, M.bit_length(m)), {==})

# ---- the sum of the aligned significands, jammed, is rounded exactly ----

def amb_core(+s: Bool, +e: Nat, +sig: WU.U64, +t: Nat, +S: Nat, +d: Nat, +x0: Nat, +hsig: {SW.value(sig) == Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)) : Nat}, +he: {Nat.add(Nat.add(x0, d), 2180n) == e : Nat}, +hx1: {Nat.is_le(1n, Nat.add(x0, d)) == True{} : Bool}, +hS: {C.fits(62n, S) == True{} : Bool}, +ht62: {C.fits(62n, Nat.double(t)) == True{} : Bool}, +ht61: {C.fits(61n, Nat.double(t)) == False{} : Bool}) -> {F.rp62(s, e, sig) == SF.round(s, Nat.add(S, C.shift(d, Nat.double(t))), x0) : F.F64}:
  +h = C.high(d, S)
  +l = C.low(d, S)
  +eH = WW.high_add_shift(d, S, Nat.double(t))
  +eL = WW.low_add_shift(d, S, Nat.double(t))
  +eJ = Equal.trans(Nat, Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), SW.jam(Nat.add(h, Nat.double(t)), l), SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), Equal.sym(Nat, SW.jam(Nat.add(h, Nat.double(t)), l), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), AP.jam_add(t, h, l)), Equal.trans(Nat, SW.jam(Nat.add(h, Nat.double(t)), l), SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), l), SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), Equal.cong(Nat, Nat, z => SW.jam(z, l), Nat.add(h, Nat.double(t)), C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), Equal.sym(Nat, C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), Nat.add(h, Nat.double(t)), eH)), Equal.cong(Nat, Nat, z => SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), z), l, C.low(d, Nat.add(S, C.shift(d, Nat.double(t)))), Equal.sym(Nat, C.low(d, Nat.add(S, C.shift(d, Nat.double(t)))), l, eL))))
  +ev = Equal.trans(Nat, SW.value(sig), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), hsig, eJ)
  +fh = Equal.trans(Bool, C.fits(62n, h), C.fits(Nat.add(d, 62n), S), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 62n), S), C.fits(62n, h), FR.fits_hc(d, 62n, S)), SH.fits_mono(62n, Nat.add(d, 62n), S, L.subst(Nat, z => {Nat.is_le(62n, z) == True{} : Bool}, Nat.add(62n, d), Nat.add(d, 62n), NA.add_comm(62n, d), N.le_add_right(62n, d)), hS))
  +fJ = Equal.trans(Bool, C.fits(62n, SW.jam(C.high(d, S), C.low(d, S))), C.fits(62n, h), True{}, RT.jam_fits(61n, h, l), fh)
  +f63 = FR.fits_add1(62n, SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t), fJ, ht62)
  +hle = L.subst(Nat, z => {Nat.is_le(Nat.double(t), z) == True{} : Bool}, Nat.add(Nat.double(t), SW.jam(C.high(d, S), C.low(d, S))), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), NA.add_comm(Nat.double(t), SW.jam(C.high(d, S), C.low(d, S))), N.le_add_right(Nat.double(t), SW.jam(C.high(d, S), C.low(d, S))))
  +n61 = FR.nfit(61n, Nat.double(t), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), hle, ht61)
  +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), hsig), f63)
  +h61 = L.subst(Nat, z => {C.fits(61n, z) == False{} : Bool}, Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.add(SW.jam(C.high(d, S), C.low(d, S)), Nat.double(t)), hsig), n61)
  +r1 = MP.rp62(s, e, sig, Nat.add(x0, d), he, hx1, h61, h63)
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(x0, d)), SW.value(sig), SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), ev)
  +hsh = L.subst(Nat, z => {Nat.is_le(C.shift(d, Nat.double(t)), z) == True{} : Bool}, Nat.add(C.shift(d, Nat.double(t)), S), Nat.add(S, C.shift(d, Nat.double(t))), NA.add_comm(C.shift(d, Nat.double(t)), S), N.le_add_right(C.shift(d, Nat.double(t)), S))
  +nV = FR.nfit(Nat.add(d, 61n), C.shift(d, Nat.double(t)), Nat.add(S, C.shift(d, Nat.double(t))), hsh, Equal.trans(Bool, C.fits(Nat.add(d, 61n), C.shift(d, Nat.double(t))), C.fits(61n, Nat.double(t)), False{}, RT.fits_sh(d, 61n, Nat.double(t)), ht61))
  +hb = N.le_trans(Nat.add(d, 55n), 1n+Nat.add(d, 61n), M.bit_length(Nat.add(S, C.shift(d, Nat.double(t)))), L.subst(Nat, z => {Nat.is_le(Nat.add(d, 55n), z) == True{} : Bool}, Nat.add(d, 62n), 1n+Nat.add(d, 61n), N.add_succ(d, 61n), N.le_add_left(55n, 62n, d, {==})), nfit_bl(Nat.add(d, 61n), Nat.add(S, C.shift(d, Nat.double(t))), nV))
  +r3 = Equal.sym(F.F64, SF.round(s, Nat.add(S, C.shift(d, Nat.double(t))), x0), SF.round(s, SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), Nat.add(x0, d)), RT.round_jam(s, d, Nat.add(S, C.shift(d, Nat.double(t))), x0, hb))
  Equal.trans(F.F64, F.rp62(s, e, sig), SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, Nat.add(S, C.shift(d, Nat.double(t))), x0), r1, Equal.trans(F.F64, SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, SW.jam(C.high(d, Nat.add(S, C.shift(d, Nat.double(t)))), C.low(d, Nat.add(S, C.shift(d, Nat.double(t))))), Nat.add(x0, d)), SF.round(s, Nat.add(S, C.shift(d, Nat.double(t))), x0), r2, r3))

def addc(+a: WU.U64, +b: WU.U64) -> {SW.value(X.add(a, b)) == SW.value(X.add(b, a)) : Nat}:
  a1 = WA.add_value(a, b)
  a2 = WA.add_value(b, a)
  Equal.trans(Nat, SW.value(X.add(a, b)), C.low(64n, Nat.add(SW.value(a), SW.value(b))), SW.value(X.add(b, a)), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(a), SW.value(b))), C.low(64n, Nat.add(SW.value(b), SW.value(a))), SW.value(X.add(b, a)), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(a), SW.value(b)), Nat.add(SW.value(b), SW.value(a)), NA.add_comm(SW.value(a), SW.value(b))), Equal.sym(Nat, SW.value(X.add(b, a)), C.low(64n, Nat.add(SW.value(b), SW.value(a))), a2)))

def n52(+one: Nat, +h1: {one == 1n : Nat}, +Fr: Nat) -> {C.fits(52n, Nat.add(Fr, C.shift(52n, one))) == False{} : Bool}:
  +nf = Equal.trans(Bool, C.fits(52n, C.shift(52n, one)), Nat.is_lt(C.shift(52n, one), C.shift(52n, one)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(52n, one), C.shift(52n, one)), C.fits(52n, C.shift(52n, one)), FR.lt_fit(52n, one, h1, C.shift(52n, one))), N.lt_irrefl(C.shift(52n, one)))
  FR.nfit(52n, C.shift(52n, one), Nat.add(Fr, C.shift(52n, one)), L.subst(Nat, z => {Nat.is_le(C.shift(52n, one), z) == True{} : Bool}, Nat.add(C.shift(52n, one), Fr), Nat.add(Fr, C.shift(52n, one)), NA.add_comm(C.shift(52n, one), Fr), N.le_add_right(C.shift(52n, one), Fr)), nf)

def f53(+one: Nat, +h1: {one == 1n : Nat}, +Fr: Nat, +hF: {C.fits(52n, Fr) == True{} : Bool}) -> {C.fits(53n, Nat.add(Fr, C.shift(52n, one))) == True{} : Bool}:
  WW.limbs_fit(52n, 1n, Fr, one, hF, L.subst(Nat, z => {C.fits(1n, z) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==}))

def sh9(+k: Nat, +m: Nat, +h: {C.fits(k, m) == True{} : Bool}) -> {C.fits(Nat.add(9n, k), C.shift(9n, m)) == True{} : Bool}:
  Equal.trans(Bool, C.fits(Nat.add(9n, k), C.shift(9n, m)), C.fits(k, m), True{}, RT.fits_sh(9n, k, m), h)

def shc(+a: Nat, +b: Nat, +m: Nat) -> {C.shift(a, C.shift(b, m)) == C.shift(b, C.shift(a, m)) : Nat}:
  Equal.trans(Nat, C.shift(a, C.shift(b, m)), C.shift(Nat.add(a, b), m), C.shift(b, C.shift(a, m)), Equal.sym(Nat, C.shift(Nat.add(a, b), m), C.shift(a, C.shift(b, m)), WW.shift_comp(a, b, m)), Equal.trans(Nat, C.shift(Nat.add(a, b), m), C.shift(Nat.add(b, a), m), C.shift(b, C.shift(a, m)), Equal.cong(Nat, Nat, z => C.shift(z, m), Nat.add(a, b), Nat.add(b, a), NA.add_comm(a, b)), WW.shift_comp(b, a, m)))

# the aligned sum value: T + jam(S >> d)
def sigv(+tw: WU.U64, +sw: WU.U64, +T: Nat, +S: Nat, +d: Nat, +ht: {SW.value(tw) == T : Nat}, +hs: {SW.value(sw) == S : Nat}, +hT: {C.fits(62n, T) == True{} : Bool}, +hS: {C.fits(62n, S) == True{} : Bool}) -> {SW.value(X.add(tw, X.shr_jam(sw, d))) == Nat.add(SW.jam(C.high(d, S), C.low(d, S)), T) : Nat}:
  sj = SH.shr_jam_value(sw, d)
  +J = SW.jam(C.high(d, S), C.low(d, S))
  +ej = Equal.trans(Nat, SW.value(X.shr_jam(sw, d)), SW.jam(C.high(d, SW.value(sw)), C.low(d, SW.value(sw))), J, sj, Equal.cong(Nat, Nat, z => SW.jam(C.high(d, z), C.low(d, z)), SW.value(sw), S, hs))
  +fh = Equal.trans(Bool, C.fits(62n, C.high(d, S)), C.fits(Nat.add(d, 62n), S), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 62n), S), C.fits(62n, C.high(d, S)), FR.fits_hc(d, 62n, S)), SH.fits_mono(62n, Nat.add(d, 62n), S, L.subst(Nat, z => {Nat.is_le(62n, z) == True{} : Bool}, Nat.add(62n, d), Nat.add(d, 62n), NA.add_comm(62n, d), N.le_add_right(62n, d)), hS))
  +fJ = Equal.trans(Bool, C.fits(62n, J), C.fits(62n, C.high(d, S)), True{}, RT.jam_fits(61n, C.high(d, S), C.low(d, S)), fh)
  +f64 = SH.fits_mono(63n, 64n, Nat.add(T, J), {==}, FR.fits_add1(62n, T, J, hT, fJ))
  a1 = WA.add_value(tw, X.shr_jam(sw, d))
  +e1 = Equal.trans(Nat, Nat.add(SW.value(tw), SW.value(X.shr_jam(sw, d))), Nat.add(T, SW.value(X.shr_jam(sw, d))), Nat.add(T, J), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(X.shr_jam(sw, d))), SW.value(tw), T, ht), Equal.cong(Nat, Nat, z => Nat.add(T, z), SW.value(X.shr_jam(sw, d)), J, ej))
  Equal.trans(Nat, SW.value(X.add(tw, X.shr_jam(sw, d))), C.low(64n, Nat.add(SW.value(tw), SW.value(X.shr_jam(sw, d)))), Nat.add(J, T), a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(tw), SW.value(X.shr_jam(sw, d)))), Nat.add(T, J), Nat.add(J, T), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(tw), SW.value(X.shr_jam(sw, d)))), C.low(64n, Nat.add(T, J)), Nat.add(T, J), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(tw), SW.value(X.shr_jam(sw, d))), Nat.add(T, J), e1), WW.low_fit(64n, Nat.add(T, J), f64)), NA.add_comm(T, J)))

# addMags, larger exponent el, smaller exponent es = 1 + p
def amb1(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +p: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(1n+p, el) == True{} : Bool}) -> {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(1n+p, X.shl(fs, 9n)), Nat.sub(el, 1n+p)))) == SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(Nat.sub(el, 1n+p), Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, 1n+p)) : F.F64}:
  +d = Nat.sub(el, 1n+p)
  +T = C.shift(9n, Nat.add(Fl, C.shift(52n, one)))
  +S = C.shift(9n, Nat.add(Fs, C.shift(52n, one)))
  +sw = X.add(X.shl(fs, 9n), WU.U64{0, 536870912})
  +et = top9(one, h1, fl, Fl, hfl, hFl, 536870912, {==})
  +es = Equal.trans(Nat, SW.value(sw), SW.value(X.add(WU.U64{0, 536870912}, X.shl(fs, 9n))), S, addc(X.shl(fs, 9n), WU.U64{0, 536870912}), top9(one, h1, fs, Fs, hfs, hFs, 536870912, {==}))
  +hT62 = SH.fits_mono(Nat.add(9n, 53n), 62n, T, {==}, sh9(53n, Nat.add(Fl, C.shift(52n, one)), f53(one, h1, Fl, hFl)))
  +hS62 = SH.fits_mono(Nat.add(9n, 53n), 62n, S, {==}, sh9(53n, Nat.add(Fs, C.shift(52n, one)), f53(one, h1, Fs, hFs)))
  +hT61 = Equal.trans(Bool, C.fits(Nat.add(9n, 52n), T), C.fits(52n, Nat.add(Fl, C.shift(52n, one))), False{}, RT.fits_sh(9n, 52n, Nat.add(Fl, C.shift(52n, one))), n52(one, h1, Fl))
  +hsig = sigv(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), sw, T, S, d, et, es, hT62, hS62)
  +eld = N.sub_add(el, 1n+p, N.lt_le(1n+p, el, hlt))
  +he = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(1916n, 1n+p), d), 2180n), Nat.add(Nat.add(1916n, Nat.add(1n+p, d)), 2180n), Nat.add(F.off(), el), Equal.cong(Nat, Nat, z => Nat.add(z, 2180n), Nat.add(Nat.add(1916n, 1n+p), d), Nat.add(1916n, Nat.add(1n+p, d)), NA.add_assoc(1916n, 1n+p, d)), Equal.trans(Nat, Nat.add(Nat.add(1916n, Nat.add(1n+p, d)), 2180n), Nat.add(Nat.add(1916n, el), 2180n), Nat.add(F.off(), el), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1916n, z), 2180n), Nat.add(1n+p, d), el, eld), Equal.trans(Nat, Nat.add(Nat.add(1916n, el), 2180n), Nat.add(1916n, Nat.add(el, 2180n)), Nat.add(F.off(), el), NA.add_assoc(1916n, el, 2180n), Equal.cong(Nat, Nat, z => Nat.add(1916n, z), Nat.add(el, 2180n), Nat.add(2180n, el), NA.add_comm(el, 2180n)))))
  +r1 = amb_core(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(1n+p, X.shl(fs, 9n)), Nat.sub(el, 1n+p))), C.shift(8n, Nat.add(Fl, C.shift(52n, one))), S, d, Nat.add(1916n, 1n+p), hsig, he, N.le_trans(1n, Nat.add(1916n, 1n+p), Nat.add(Nat.add(1916n, 1n+p), d), {==}, N.le_add_right(Nat.add(1916n, 1n+p), d)), hS62, hT62, hT61)
  +eV = Equal.trans(Nat, Nat.add(S, C.shift(d, T)), Nat.add(S, C.shift(9n, C.shift(d, Nat.add(Fl, C.shift(52n, one))))), C.shift(9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))), Equal.cong(Nat, Nat, z => Nat.add(S, z), C.shift(d, T), C.shift(9n, C.shift(d, Nat.add(Fl, C.shift(52n, one)))), shc(d, 9n, Nat.add(Fl, C.shift(52n, one)))), Equal.sym(Nat, C.shift(9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))), Nat.add(S, C.shift(9n, C.shift(d, Nat.add(Fl, C.shift(52n, one))))), WW.shift_add(9n, Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))))
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(1916n, 1n+p)), Nat.add(S, C.shift(d, T)), C.shift(9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))), eV)
  +r3 = RT.round_shift(s, 9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), Nat.add(1916n, 1n+p))
  +r4 = Equal.cong(Nat, F.F64, z => SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), z), Nat.add(Nat.add(1916n, 1n+p), 9n), Nat.add(1925n, 1n+p), Equal.cong(Nat, Nat, z => 1917n+z, Nat.add(p, 9n), Nat.add(9n, p), NA.add_comm(p, 9n)))
  Equal.trans(F.F64, F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(1n+p, X.shl(fs, 9n)), Nat.sub(el, 1n+p)))), SF.round(s, Nat.add(S, C.shift(d, T)), Nat.add(1916n, 1n+p)), SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, 1n+p)), r1, Equal.trans(F.F64, SF.round(s, Nat.add(S, C.shift(d, T)), Nat.add(1916n, 1n+p)), SF.round(s, C.shift(9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))), Nat.add(1916n, 1n+p)), SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, 1n+p)), r2, Equal.trans(F.F64, SF.round(s, C.shift(9n, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one))))), Nat.add(1916n, 1n+p)), SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), Nat.add(Nat.add(1916n, 1n+p), 9n)), SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(d, Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, 1n+p)), r3, r4)))

# addMags, larger exponent el, the smaller operand subnormal (es = 0)
def amb0(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(0n, el) == True{} : Bool}) -> {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(0n, X.shl(fs, 9n)), Nat.sub(el, 0n)))) == SF.round(s, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), 1926n) : F.F64}:
  +d = Nat.sub(el, 0n)
  +T = C.shift(9n, Nat.add(Fl, C.shift(52n, one)))
  +S = C.shift(10n, Fs)
  +f9 = X.shl(fs, 9n)
  +et = top9(one, h1, fl, Fl, hfl, hFl, 536870912, {==})
  +hFv = L.subst(Nat, z => {C.fits(52n, z) == True{} : Bool}, Fs, SW.value(fs), Equal.sym(Nat, SW.value(fs), Fs, hfs), hFs)
  +e9 = Equal.trans(Nat, SW.value(f9), C.shift(9n, SW.value(fs)), C.shift(9n, Fs), shl_v(fs, 9n, 52n, {==}, {==}, hFv), Equal.cong(Nat, Nat, z => C.shift(9n, z), SW.value(fs), Fs, hfs))
  +hS62 = SH.fits_mono(Nat.add(10n, 52n), 62n, S, {==}, Equal.trans(Bool, C.fits(Nat.add(10n, 52n), S), C.fits(52n, Fs), True{}, RT.fits_sh(10n, 52n, Fs), hFs))
  a1 = WA.add_value(f9, f9)
  +es = Equal.trans(Nat, SW.value(X.add(f9, f9)), C.low(64n, Nat.add(SW.value(f9), SW.value(f9))), S, a1, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(f9), SW.value(f9))), C.low(64n, S), S, Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(f9), SW.value(f9)), S, Equal.trans(Nat, Nat.add(SW.value(f9), SW.value(f9)), Nat.add(C.shift(9n, Fs), C.shift(9n, Fs)), S, Equal.trans(Nat, Nat.add(SW.value(f9), SW.value(f9)), Nat.add(C.shift(9n, Fs), SW.value(f9)), Nat.add(C.shift(9n, Fs), C.shift(9n, Fs)), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(f9)), SW.value(f9), C.shift(9n, Fs), e9), Equal.cong(Nat, Nat, z => Nat.add(C.shift(9n, Fs), z), SW.value(f9), C.shift(9n, Fs), e9)), Equal.sym(Nat, Nat.double(C.shift(9n, Fs)), Nat.add(C.shift(9n, Fs), C.shift(9n, Fs)), NA.double_self(C.shift(9n, Fs))))), WW.low_fit(64n, S, SH.fits_mono(62n, 64n, S, {==}, hS62))))
  +hT62 = SH.fits_mono(Nat.add(9n, 53n), 62n, T, {==}, sh9(53n, Nat.add(Fl, C.shift(52n, one)), f53(one, h1, Fl, hFl)))
  +hT61 = Equal.trans(Bool, C.fits(Nat.add(9n, 52n), T), C.fits(52n, Nat.add(Fl, C.shift(52n, one))), False{}, RT.fits_sh(9n, 52n, Nat.add(Fl, C.shift(52n, one))), n52(one, h1, Fl))
  +hsig = sigv(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.add(f9, f9), T, S, d, et, es, hT62, hS62)
  +ed = N.sub_zero(el)
  +he = Equal.trans(Nat, Nat.add(Nat.add(1916n, d), 2180n), Nat.add(Nat.add(1916n, el), 2180n), Nat.add(F.off(), el), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(1916n, z), 2180n), d, el, ed), Equal.trans(Nat, Nat.add(Nat.add(1916n, el), 2180n), Nat.add(1916n, Nat.add(el, 2180n)), Nat.add(F.off(), el), NA.add_assoc(1916n, el, 2180n), Equal.cong(Nat, Nat, z => Nat.add(1916n, z), Nat.add(el, 2180n), Nat.add(2180n, el), NA.add_comm(el, 2180n))))
  +r1 = amb_core(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(0n, X.shl(fs, 9n)), Nat.sub(el, 0n))), C.shift(8n, Nat.add(Fl, C.shift(52n, one))), S, d, 1916n, hsig, he, N.le_trans(1n, 1916n, Nat.add(1916n, d), {==}, N.le_add_right(1916n, d)), hS62, hT62, hT61)
  +eq = N.sub_add(el, 1n, N.lt_succ_le_succ(0n, el, hlt))
  +eV = Equal.trans(Nat, Nat.add(S, C.shift(d, T)), Nat.add(S, Nat.double(C.shift(Nat.sub(el, 1n), T))), C.shift(10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), Equal.cong(Nat, Nat, z => Nat.add(S, C.shift(z, T)), d, 1n+Nat.sub(el, 1n), Equal.trans(Nat, d, el, 1n+Nat.sub(el, 1n), ed, Equal.sym(Nat, 1n+Nat.sub(el, 1n), el, eq))), Equal.trans(Nat, Nat.add(S, Nat.double(C.shift(Nat.sub(el, 1n), T))), Nat.add(S, C.shift(10n, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), C.shift(10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), Equal.cong(Nat, Nat, z => Nat.add(S, Nat.double(z)), C.shift(Nat.sub(el, 1n), T), C.shift(9n, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), shc(Nat.sub(el, 1n), 9n, Nat.add(Fl, C.shift(52n, one)))), Equal.sym(Nat, C.shift(10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), Nat.add(S, C.shift(10n, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), WW.shift_add(10n, Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))))))
  +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, 1916n), Nat.add(S, C.shift(d, T)), C.shift(10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), eV)
  +r3 = RT.round_shift(s, 10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), 1916n)
  Equal.trans(F.F64, F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(0n, X.shl(fs, 9n)), Nat.sub(el, 0n)))), SF.round(s, Nat.add(S, C.shift(d, T)), 1916n), SF.round(s, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), 1926n), r1, Equal.trans(F.F64, SF.round(s, Nat.add(S, C.shift(d, T)), 1916n), SF.round(s, C.shift(10n, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))))), 1916n), SF.round(s, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), 1926n), r2, r3))
