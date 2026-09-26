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
import ./width.bend as WW
import ./u32laws.bend as LW
import ./w64sh.bend as SH
import ./natcmp.bend as NC
import ./f64round.bend as FR
import ./f64rtools.bend as RT
import ./f64addp.bend as AP
import ./f64adda.bend as AA
import ./f64nrp.bend as NP

# SoftFloat's subMagsF64 with exponents el > es: the larger significand at
# bit 62 minus the smaller one shifted right with a sticky bit, normalized
# and rounded by normRoundPackToF64, is round of the exact difference.

def jam_le(+hh: Nat, +ll: Nat) -> {Nat.is_le(SW.jam(hh, ll), 1n+hh) == True{} : Bool}:
  +tt = Nat.max(C.bit(hh), Nat.min(ll, 1n))
  +h1 = WW.le_add_r(tt, 1n, Nat.double(C.half(hh)), FR.max_le1(C.bit(hh), ll, WW.bit_le1(hh)))
  +h2 = N.le_add_left(Nat.double(C.half(hh)), hh, 1n, L.subst(Nat, z => {Nat.is_le(Nat.double(C.half(hh)), z) == True{} : Bool}, Nat.add(Nat.double(C.half(hh)), C.bit(hh)), hh, Equal.trans(Nat, Nat.add(Nat.double(C.half(hh)), C.bit(hh)), Nat.add(C.bit(hh), Nat.double(C.half(hh))), hh, NA.add_comm(Nat.double(C.half(hh)), C.bit(hh)), Equal.sym(Nat, hh, Nat.add(C.bit(hh), Nat.double(C.half(hh))), WW.hb(hh))), N.le_add_right(Nat.double(C.half(hh)), C.bit(hh))))
  L.subst(Nat, z => {Nat.is_le(z, 1n+hh) == True{} : Bool}, Nat.add(tt, Nat.double(C.half(hh))), SW.jam(hh, ll), Equal.sym(Nat, SW.jam(hh, ll), Nat.add(tt, Nat.double(C.half(hh))), FR.jam_form(hh, ll)), N.le_trans(Nat.add(tt, Nat.double(C.half(hh))), Nat.add(1n, Nat.double(C.half(hh))), 1n+hh, h1, h2))

def low_sh(+d: Nat, +k: Nat, +m: Nat, +hd: {Nat.is_le(d, k) == True{} : Bool}) -> {C.low(d, C.shift(k, m)) == 0n : Nat}:
  +es = NC.sh_split(k, d, m, hd)
  Equal.trans(Nat, C.low(d, C.shift(k, m)), C.low(d, Nat.add(0n, C.shift(d, C.shift(Nat.sub(k, d), m)))), 0n, Equal.cong(Nat, Nat, z => C.low(d, z), C.shift(k, m), C.shift(d, C.shift(Nat.sub(k, d), m)), es), WW.low_u(d, 0n, C.shift(Nat.sub(k, d), m), FR.fz(d)))

def d11_c(+d: Nat, +S1: Nat, +c: Bool, +hc: {Nat.is_le(d, 10n) == c : Bool}, +hl: {Nat.is_eq(C.low(d, C.shift(10n, S1)), 0n) == False{} : Bool}) -> {Nat.is_le(11n, d) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_le(11n, d) == True{} : Bool}, LW.true_ne_false(Equal.trans(Bool, True{}, Nat.is_eq(C.low(d, C.shift(10n, S1)), 0n), False{}, Equal.sym(Bool, Nat.is_eq(C.low(d, C.shift(10n, S1)), 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), C.low(d, C.shift(10n, S1)), 0n, low_sh(d, 10n, S1, hc))), hl)))
    case False{}:
      Equal.trans(Bool, Nat.is_le(11n, d), Nat.is_lt(10n, d), True{}, FR.le_succ_lt(10n, d), N.not_le_lt(d, 10n, hc))

def shmk(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(C.shift(a, x), C.shift(b, x)) == True{} : Bool}:
  +h0 = WW.shift_mono(a, x, C.shift(Nat.sub(b, a), x), WW.shift_ge(Nat.sub(b, a), x))
  L.subst(Nat, z => {Nat.is_le(C.shift(a, x), z) == True{} : Bool}, C.shift(a, C.shift(Nat.sub(b, a), x)), C.shift(b, x), Equal.sym(Nat, C.shift(b, x), C.shift(a, C.shift(Nat.sub(b, a), x)), NC.sh_split(b, a, x, h)), h0)

# W = 2^d T - S is at least 2^d * 2^61 when d >= 2, T >= 2^62, S < 2^63
def wbig(+one: Nat, +h1: {one == 1n : Nat}, +t: Nat, +S: Nat, +d: Nat, +hd: {Nat.is_le(2n, d) == True{} : Bool}, +hT: {C.fits(62n, Nat.double(t)) == False{} : Bool}, +hS: {C.fits(63n, S) == True{} : Bool}) -> {C.fits(Nat.add(d, 61n), Nat.sub(C.shift(d, Nat.double(t)), S)) == False{} : Bool}:
  +A = C.shift(d, C.shift(61n, one))
  +hTge = N.not_lt_le(Nat.double(t), C.shift(62n, one), Equal.trans(Bool, Nat.is_lt(Nat.double(t), C.shift(62n, one)), C.fits(62n, Nat.double(t)), False{}, FR.lt_fit(62n, one, h1, Nat.double(t)), hT))
  +h2A = L.subst(Nat, z => {Nat.is_le(z, C.shift(d, Nat.double(t))) == True{} : Bool}, C.shift(d, Nat.double(C.shift(61n, one))), Nat.add(A, A), Equal.trans(Nat, C.shift(d, Nat.double(C.shift(61n, one))), Nat.double(A), Nat.add(A, A), WW.shift_dbl(d, C.shift(61n, one)), NA.double_self(A)), WW.shift_mono(d, Nat.double(C.shift(61n, one)), Nat.double(t), hTge))
  +ed = N.sub_add(d, 2n, hd)
  +hSA0 = N.lt_le_trans(S, C.shift(63n, one), C.shift(2n, C.shift(61n, one)), Equal.trans(Bool, Nat.is_lt(S, C.shift(63n, one)), C.fits(63n, S), True{}, FR.lt_fit(63n, one, h1, S), hS), L.subst(Nat, z => {Nat.is_le(C.shift(63n, one), z) == True{} : Bool}, C.shift(Nat.add(2n, 61n), one), C.shift(2n, C.shift(61n, one)), WW.shift_comp(2n, 61n, one), N.le_refl(C.shift(63n, one))))
  +hSA = N.lt_le(S, A, N.lt_le_trans(S, C.shift(2n, C.shift(61n, one)), A, hSA0, shmk(2n, d, C.shift(61n, one), hd)))
  +hWA = RT.le_sub(A, S, C.shift(d, Nat.double(t)), N.le_trans(Nat.add(A, S), Nat.add(A, A), C.shift(d, Nat.double(t)), N.le_add_left(S, A, A, hSA), h2A))
  +nfA = Equal.trans(Bool, C.fits(Nat.add(d, 61n), A), C.fits(61n, C.shift(61n, one)), False{}, RT.fits_sh(d, 61n, C.shift(61n, one)), Equal.trans(Bool, C.fits(61n, C.shift(61n, one)), Nat.is_lt(C.shift(61n, one), C.shift(61n, one)), False{}, Equal.sym(Bool, Nat.is_lt(C.shift(61n, one), C.shift(61n, one)), C.fits(61n, C.shift(61n, one)), FR.lt_fit(61n, one, h1, C.shift(61n, one))), N.lt_irrefl(C.shift(61n, one))))
  FR.nfit(Nat.add(d, 61n), A, Nat.sub(C.shift(d, Nat.double(t)), S), hWA, nfA)

def posz(+n: Nat, +h: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_eq(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      NC.absurd_tf({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+ +np:
      {==}

def sub_odd(+t: Nat, +k: Nat, +hk: {Nat.is_lt(k, t) == True{} : Bool}) -> {Nat.is_eq(Nat.sub(Nat.double(t), 1n+Nat.double(k)), 0n) == False{} : Bool}:
  match t k:
    case 0n _:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 1n+Nat.double(k)), 0n) == False{} : Bool}, N.lt_zero_absurd(k, hk))
    case 1n+ +tp 0n:
      {==}
    case 1n+ +tp 1n+ +kp:
      sub_odd(tp, kp, hk)

def hlt(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +t: Nat, +S1: Nat, +d: Nat, +x0: Nat, +hsig: {SW.value(sig) == Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))) : Nat}, +he: {Nat.add(Nat.add(x0, d), 2180n) == e : Nat}, +hx63: {Nat.is_le(63n, Nat.add(x0, d)) == True{} : Bool}, +hd1: {Nat.is_le(1n, d) == True{} : Bool}, +hS: {C.fits(63n, C.shift(10n, S1)) == True{} : Bool}, +hT62: {C.fits(62n, Nat.double(t)) == False{} : Bool}, +hT63: {C.fits(63n, Nat.double(t)) == True{} : Bool}) -> {Nat.is_lt(C.high(d, C.shift(10n, S1)), Nat.double(t)) == True{} : Bool}:
  +f62 = Equal.trans(Bool, C.fits(62n, C.high(d, C.shift(10n, S1))), C.fits(Nat.add(d, 62n), C.shift(10n, S1)), True{}, Equal.sym(Bool, C.fits(Nat.add(d, 62n), C.shift(10n, S1)), C.fits(62n, C.high(d, C.shift(10n, S1))), FR.fits_hc(d, 62n, C.shift(10n, S1))), SH.fits_mono(63n, Nat.add(d, 62n), C.shift(10n, S1), L.subst(Nat, z => {Nat.is_le(63n, z) == True{} : Bool}, Nat.add(62n, d), Nat.add(d, 62n), NA.add_comm(62n, d), N.le_add_left(1n, d, 62n, hd1)), hS))
  +P62 = C.shift(62n, one)
  N.lt_le_trans(C.high(d, C.shift(10n, S1)), P62, Nat.double(t), Equal.trans(Bool, Nat.is_lt(C.high(d, C.shift(10n, S1)), P62), C.fits(62n, C.high(d, C.shift(10n, S1))), True{}, FR.lt_fit(62n, one, h1, C.high(d, C.shift(10n, S1))), f62), N.not_lt_le(Nat.double(t), P62, Equal.trans(Bool, Nat.is_lt(Nat.double(t), P62), C.fits(62n, Nat.double(t)), False{}, FR.lt_fit(62n, one, h1, Nat.double(t)), hT62)))

def smb_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +e: Nat, +sig: WU.U64, +t: Nat, +S1: Nat, +d: Nat, +x0: Nat, +hsig: {SW.value(sig) == Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))) : Nat}, +he: {Nat.add(Nat.add(x0, d), 2180n) == e : Nat}, +hx63: {Nat.is_le(63n, Nat.add(x0, d)) == True{} : Bool}, +hd1: {Nat.is_le(1n, d) == True{} : Bool}, +hS: {C.fits(63n, C.shift(10n, S1)) == True{} : Bool}, +hT62: {C.fits(62n, Nat.double(t)) == False{} : Bool}, +hT63: {C.fits(63n, Nat.double(t)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(C.low(d, C.shift(10n, S1)), 0n) == c : Bool}) -> {F.norm_round_pack(s, e, sig) == SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0) : F.F64}:
  match c:
    case True{}:
      +el0 = N.eq_from_is_eq(C.low(d, C.shift(10n, S1)), 0n, hc)
      +hh = hlt(one, h1, s, e, sig, t, S1, d, x0, hsig, he, hx63, hd1, hS, hT62, hT63)
      +eS = Equal.trans(Nat, C.shift(10n, S1), Nat.add(C.low(d, C.shift(10n, S1)), C.shift(d, C.high(d, C.shift(10n, S1)))), C.shift(d, C.high(d, C.shift(10n, S1))), WW.low_high(d, C.shift(10n, S1)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(d, C.high(d, C.shift(10n, S1)))), C.low(d, C.shift(10n, S1)), 0n, el0))
      +ev = Equal.trans(Nat, SW.value(sig), Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), hsig, Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(t), z), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1))), C.high(d, C.shift(10n, S1)), Equal.trans(Nat, SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1))), SW.jam(C.high(d, C.shift(10n, S1)), 0n), C.high(d, C.shift(10n, S1)), Equal.cong(Nat, Nat, z => SW.jam(C.high(d, C.shift(10n, S1)), z), C.low(d, C.shift(10n, S1)), 0n, el0), AP.jam_z(C.high(d, C.shift(10n, S1))))))
      +pos = FR.lt_sub_pos(C.high(d, C.shift(10n, S1)), Nat.double(t), hh)
      +hz = L.subst(Nat, z => {Nat.is_eq(z, 0n) == False{} : Bool}, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), ev), posz(Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), pos))
      +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), ev), SH.fits_lek(63n, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), Nat.double(t), UH.sub_le(Nat.double(t), C.high(d, C.shift(10n, S1))), hT63))
      +r1 = NP.nrp(one, h1, s, e, sig, Nat.add(x0, d), he, hz, h63, hx63)
      +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(x0, d)), SW.value(sig), Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), ev)
      +r3 = Equal.sym(F.F64, SF.round(s, C.shift(d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1)))), x0), SF.round(s, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), Nat.add(x0, d)), RT.round_shift(s, d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), x0))
      +r4 = Equal.cong(Nat, F.F64, z => SF.round(s, z, x0), C.shift(d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1)))), Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), Equal.trans(Nat, C.shift(d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1)))), Nat.sub(C.shift(d, Nat.double(t)), C.shift(d, C.high(d, C.shift(10n, S1)))), Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), Equal.sym(Nat, Nat.sub(C.shift(d, Nat.double(t)), C.shift(d, C.high(d, C.shift(10n, S1)))), C.shift(d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1)))), AP.sub_shift(d, Nat.double(t), C.high(d, C.shift(10n, S1)), N.lt_le(C.high(d, C.shift(10n, S1)), Nat.double(t), hh))), Equal.cong(Nat, Nat, z => Nat.sub(C.shift(d, Nat.double(t)), z), C.shift(d, C.high(d, C.shift(10n, S1))), C.shift(10n, S1), Equal.sym(Nat, C.shift(10n, S1), C.shift(d, C.high(d, C.shift(10n, S1))), eS))))
      Equal.trans(F.F64, F.norm_round_pack(s, e, sig), SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), r1, Equal.trans(F.F64, SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), Nat.add(x0, d)), SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), r2, Equal.trans(F.F64, SF.round(s, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1))), Nat.add(x0, d)), SF.round(s, C.shift(d, Nat.sub(Nat.double(t), C.high(d, C.shift(10n, S1)))), x0), SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), r3, r4)))
    case False{}:
      +hh = hlt(one, h1, s, e, sig, t, S1, d, x0, hsig, he, hx63, hd1, hS, hT62, hT63)
      +W2 = Nat.sub(C.shift(d, Nat.double(t)), Nat.add(C.low(d, C.shift(10n, S1)), C.shift(d, C.high(d, C.shift(10n, S1)))))
      +eW = Equal.cong(Nat, Nat, z => Nat.sub(C.shift(d, Nat.double(t)), z), Nat.add(C.low(d, C.shift(10n, S1)), C.shift(d, C.high(d, C.shift(10n, S1)))), C.shift(10n, S1), Equal.sym(Nat, C.shift(10n, S1), Nat.add(C.low(d, C.shift(10n, S1)), C.shift(d, C.high(d, C.shift(10n, S1)))), WW.low_high(d, C.shift(10n, S1))))
      +ej = AP.jsub(t, d, C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)), hc, WW.low_fits(d, C.shift(10n, S1)), hh)
      +ev = Equal.trans(Nat, SW.value(sig), Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)))), hsig, Equal.trans(Nat, Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), SW.jam(C.high(d, W2), C.low(d, W2)), SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)))), ej, Equal.cong(Nat, Nat, z => SW.jam(C.high(d, z), C.low(d, z)), W2, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), eW)))
      +hd11 = d11_c(d, S1, Nat.is_le(d, 10n), {==}, hc)
      +nW = wbig(one, h1, t, C.shift(10n, S1), d, N.le_trans(2n, 11n, d, {==}, hd11), hT62, hS)
      +hb = N.le_trans(Nat.add(d, 55n), 1n+Nat.add(d, 61n), M.bit_length(Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1))), L.subst(Nat, z => {Nat.is_le(Nat.add(d, 55n), z) == True{} : Bool}, Nat.add(d, 62n), 1n+Nat.add(d, 61n), N.add_succ(d, 61n), N.le_add_left(55n, 62n, d, {==})), AA.nfit_bl(Nat.add(d, 61n), Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), nW))
      +JW = SW.jam(C.high(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1))), C.low(d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1))))
      +kh = C.half(C.high(d, C.shift(10n, S1)))
      +hk = AP.half_lt(kh, t, N.le_lt_trans(Nat.double(kh), C.high(d, C.shift(10n, S1)), Nat.double(t), L.subst(Nat, z => {Nat.is_le(Nat.double(kh), z) == True{} : Bool}, Nat.add(Nat.double(kh), C.bit(C.high(d, C.shift(10n, S1)))), C.high(d, C.shift(10n, S1)), Equal.trans(Nat, Nat.add(Nat.double(kh), C.bit(C.high(d, C.shift(10n, S1)))), Nat.add(C.bit(C.high(d, C.shift(10n, S1))), Nat.double(kh)), C.high(d, C.shift(10n, S1)), NA.add_comm(Nat.double(kh), C.bit(C.high(d, C.shift(10n, S1)))), Equal.sym(Nat, C.high(d, C.shift(10n, S1)), Nat.add(C.bit(C.high(d, C.shift(10n, S1))), Nat.double(kh)), WW.hb(C.high(d, C.shift(10n, S1))))), N.le_add_right(Nat.double(kh), C.bit(C.high(d, C.shift(10n, S1))))), hh))
      +ev2 = Equal.trans(Nat, SW.value(sig), Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), Nat.sub(Nat.double(t), 1n+Nat.double(kh)), hsig, Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(t), z), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1))), 1n+Nat.double(kh), AP.jam_nz(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)), hc)))
      +hz = L.subst(Nat, z => {Nat.is_eq(z, 0n) == False{} : Bool}, Nat.sub(Nat.double(t), 1n+Nat.double(kh)), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.sub(Nat.double(t), 1n+Nat.double(kh)), ev2), sub_odd(t, kh, hk))
      +h63 = L.subst(Nat, z => {C.fits(63n, z) == True{} : Bool}, Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), SW.value(sig), Equal.sym(Nat, SW.value(sig), Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), hsig), SH.fits_lek(63n, Nat.sub(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), Nat.double(t), UH.sub_le(Nat.double(t), SW.jam(C.high(d, C.shift(10n, S1)), C.low(d, C.shift(10n, S1)))), hT63))
      +r1 = NP.nrp(one, h1, s, e, sig, Nat.add(x0, d), he, hz, h63, hx63)
      +r2 = Equal.cong(Nat, F.F64, z => SF.round(s, z, Nat.add(x0, d)), SW.value(sig), JW, ev)
      +r3 = Equal.sym(F.F64, SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), SF.round(s, JW, Nat.add(x0, d)), RT.round_jam(s, d, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0, hb))
      Equal.trans(F.F64, F.norm_round_pack(s, e, sig), SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), r1, Equal.trans(F.F64, SF.round(s, SW.value(sig), Nat.add(x0, d)), SF.round(s, JW, Nat.add(x0, d)), SF.round(s, Nat.sub(C.shift(d, Nat.double(t)), C.shift(10n, S1)), x0), r2, r3))
