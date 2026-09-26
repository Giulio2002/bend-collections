import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/f64.bend as SF
import ../../../spec/math/w64.bend as SW
import ../../../src/math/f64.bend as F
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ./f64adda.bend as AA
import ./f64addb.bend as AB
import ./f64addg.bend as AG

# addMagsF64 and subMagsF64 with different exponents, restated at the
# spec's common scale (the smaller exponent es).

def bigA_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +es: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(es, 0n) == z : Bool}) -> {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(es, X.shl(fs, 9n)), Nat.sub(el, es)))) == SF.round(s, Nat.add(AG.mt(es, Fs), C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl))), AG.xe(es)) : F.F64}:
  match z:
    case True{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = AG.posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +xl = AG.xe_n(el, hel)
      +ml = AG.mt_n(one, h1, el, Fl, hel)
      +e0 = N.eq_from_is_eq(es, 0n, hz)
      +h0 = L.subst(Nat, w => {Nat.is_lt(w, el) == True{} : Bool}, es, 0n, e0, hlt)
      +r0 = AA.amb0(one, h1, s, el, fl, fs, Fl, Fs, hfl, hfs, hFl, hFs, h0)
      +ek = Equal.trans(Nat, Nat.sub(el, 1n), Nat.sub(Nat.add(1925n, el), 1926n), Nat.sub(AG.xe(el), 1926n), Equal.sym(Nat, Nat.sub(Nat.add(1925n, el), 1926n), Nat.sub(el, 1n), AG.sub_kk(1925n, el, 1n)), Equal.cong(Nat, Nat, w => Nat.sub(w, 1926n), Nat.add(1925n, el), AG.xe(el), Equal.sym(Nat, AG.xe(el), Nat.add(1925n, el), xl)))
      +b0 = AG.rca(s, Fs, Nat.add(Fs, 0n), Equal.sym(Nat, Nat.add(Fs, 0n), Fs, N.add_zero(Fs)), Nat.sub(el, 1n), Nat.sub(AG.xe(el), 1926n), ek, Nat.add(Fl, C.shift(52n, one)), AG.mt(el, Fl), Equal.sym(Nat, AG.mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), 1926n, 1926n, {==})
      +p0 = Equal.trans(F.F64, F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(0n, X.shl(fs, 9n)), Nat.sub(el, 0n)))), SF.round(s, Nat.add(Fs, C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one)))), 1926n), SF.round(s, Nat.add(AG.mt(0n, Fs), C.shift(Nat.sub(AG.xe(el), AG.xe(0n)), AG.mt(el, Fl))), AG.xe(0n)), r0, b0)
      L.subst(Nat, w => {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(w, X.shl(fs, 9n)), Nat.sub(el, w)))) == SF.round(s, Nat.add(AG.mt(w, Fs), C.shift(Nat.sub(AG.xe(el), AG.xe(w)), AG.mt(el, Fl))), AG.xe(w)) : F.F64}, 0n, es, Equal.sym(Nat, es, 0n, e0), p0)
    case False{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = AG.posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +xl = AG.xe_n(el, hel)
      +ml = AG.mt_n(one, h1, el, Fl, hel)
      +ep = AG.pred_eq(es, hz)
      +hp = L.subst(Nat, w => {Nat.is_lt(w, el) == True{} : Bool}, es, 1n+N.pred(es), Equal.sym(Nat, 1n+N.pred(es), es, ep), hlt)
      +r1 = AA.amb1(one, h1, s, el, fl, N.pred(es), fs, Fl, Fs, hfl, hfs, hFl, hFs, hp)
      +q = L.subst(Nat, w => {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(w, X.shl(fs, 9n)), Nat.sub(el, w)))) == SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(Nat.sub(el, w), Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, w)) : F.F64}, 1n+N.pred(es), es, ep, r1)
      +xs = AG.xe_n(es, hz)
      +ms = AG.mt_n(one, h1, es, Fs, hz)
      +ek = Equal.trans(Nat, Nat.sub(el, es), Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), AG.xe(es)), Equal.sym(Nat, Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(el, es), AG.sub_kk(1925n, el, es)), Equal.trans(Nat, Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), AG.xe(es)), Equal.cong(Nat, Nat, w => Nat.sub(w, Nat.add(1925n, es)), Nat.add(1925n, el), AG.xe(el), Equal.sym(Nat, AG.xe(el), Nat.add(1925n, el), xl)), Equal.cong(Nat, Nat, w => Nat.sub(AG.xe(el), w), Nat.add(1925n, es), AG.xe(es), Equal.sym(Nat, AG.xe(es), Nat.add(1925n, es), xs))))
      +b1 = AG.rca(s, Nat.add(Fs, C.shift(52n, one)), AG.mt(es, Fs), Equal.sym(Nat, AG.mt(es, Fs), Nat.add(Fs, C.shift(52n, one)), ms), Nat.sub(el, es), Nat.sub(AG.xe(el), AG.xe(es)), ek, Nat.add(Fl, C.shift(52n, one)), AG.mt(el, Fl), Equal.sym(Nat, AG.mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), Nat.add(1925n, es), AG.xe(es), Equal.sym(Nat, AG.xe(es), Nat.add(1925n, es), xs))
      Equal.trans(F.F64, F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(es, X.shl(fs, 9n)), Nat.sub(el, es)))), SF.round(s, Nat.add(Nat.add(Fs, C.shift(52n, one)), C.shift(Nat.sub(el, es), Nat.add(Fl, C.shift(52n, one)))), Nat.add(1925n, es)), SF.round(s, Nat.add(AG.mt(es, Fs), C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl))), AG.xe(es)), q, b1)

def bigA(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +es: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}) -> {F.rp62(s, Nat.add(F.off(), el), X.add(X.add(WU.U64{0, 536870912}, X.shl(fl, 9n)), X.shr_jam(F.am_small(es, X.shl(fs, 9n)), Nat.sub(el, es)))) == SF.round(s, Nat.add(AG.mt(es, Fs), C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl))), AG.xe(es)) : F.F64}:
  bigA_c(one, h1, s, el, fl, es, fs, Fl, Fs, hfl, hfs, hFl, hFs, hlt, Nat.is_eq(es, 0n), {==})

def bigS_c(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +es: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}, +z: Bool, +hz: {Nat.is_eq(es, 0n) == z : Bool}) -> {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(es, X.shl(fs, 10n)), Nat.sub(el, es)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl)), AG.mt(es, Fs)), AG.xe(es)) : F.F64}:
  match z:
    case True{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = AG.posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +xl = AG.xe_n(el, hel)
      +ml = AG.mt_n(one, h1, el, Fl, hel)
      +e0 = N.eq_from_is_eq(es, 0n, hz)
      +h0 = L.subst(Nat, w => {Nat.is_lt(w, el) == True{} : Bool}, es, 0n, e0, hlt)
      +r0 = AB.smb0(one, h1, s, el, fl, fs, Fl, Fs, hfl, hfs, hFl, hFs, h0)
      +ek = Equal.trans(Nat, Nat.sub(el, 1n), Nat.sub(Nat.add(1925n, el), 1926n), Nat.sub(AG.xe(el), 1926n), Equal.sym(Nat, Nat.sub(Nat.add(1925n, el), 1926n), Nat.sub(el, 1n), AG.sub_kk(1925n, el, 1n)), Equal.cong(Nat, Nat, w => Nat.sub(w, 1926n), Nat.add(1925n, el), AG.xe(el), Equal.sym(Nat, AG.xe(el), Nat.add(1925n, el), xl)))
      +b0 = AG.rcs(s, Fs, Nat.add(Fs, 0n), Equal.sym(Nat, Nat.add(Fs, 0n), Fs, N.add_zero(Fs)), Nat.sub(el, 1n), Nat.sub(AG.xe(el), 1926n), ek, Nat.add(Fl, C.shift(52n, one)), AG.mt(el, Fl), Equal.sym(Nat, AG.mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), 1926n, 1926n, {==})
      +p0 = Equal.trans(F.F64, F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(0n, X.shl(fs, 10n)), Nat.sub(el, 0n)))), SF.round(s, Nat.sub(C.shift(Nat.sub(el, 1n), Nat.add(Fl, C.shift(52n, one))), Fs), 1926n), SF.round(s, Nat.sub(C.shift(Nat.sub(AG.xe(el), AG.xe(0n)), AG.mt(el, Fl)), AG.mt(0n, Fs)), AG.xe(0n)), r0, b0)
      L.subst(Nat, w => {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(w, X.shl(fs, 10n)), Nat.sub(el, w)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(AG.xe(el), AG.xe(w)), AG.mt(el, Fl)), AG.mt(w, Fs)), AG.xe(w)) : F.F64}, 0n, es, Equal.sym(Nat, es, 0n, e0), p0)
    case False{}:
      +hl1 = N.lt_succ_le_succ(es, el, hlt)
      +hel = AG.posz(el, N.le_trans(1n, 1n+es, el, N.zero_le(es), hl1))
      +xl = AG.xe_n(el, hel)
      +ml = AG.mt_n(one, h1, el, Fl, hel)
      +ep = AG.pred_eq(es, hz)
      +hp = L.subst(Nat, w => {Nat.is_lt(w, el) == True{} : Bool}, es, 1n+N.pred(es), Equal.sym(Nat, 1n+N.pred(es), es, ep), hlt)
      +r1 = AB.smb1(one, h1, s, el, fl, N.pred(es), fs, Fl, Fs, hfl, hfs, hFl, hFs, hp)
      +q = L.subst(Nat, w => {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(w, X.shl(fs, 10n)), Nat.sub(el, w)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(el, w), Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, w)) : F.F64}, 1n+N.pred(es), es, ep, r1)
      +xs = AG.xe_n(es, hz)
      +ms = AG.mt_n(one, h1, es, Fs, hz)
      +ek = Equal.trans(Nat, Nat.sub(el, es), Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), AG.xe(es)), Equal.sym(Nat, Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(el, es), AG.sub_kk(1925n, el, es)), Equal.trans(Nat, Nat.sub(Nat.add(1925n, el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), Nat.add(1925n, es)), Nat.sub(AG.xe(el), AG.xe(es)), Equal.cong(Nat, Nat, w => Nat.sub(w, Nat.add(1925n, es)), Nat.add(1925n, el), AG.xe(el), Equal.sym(Nat, AG.xe(el), Nat.add(1925n, el), xl)), Equal.cong(Nat, Nat, w => Nat.sub(AG.xe(el), w), Nat.add(1925n, es), AG.xe(es), Equal.sym(Nat, AG.xe(es), Nat.add(1925n, es), xs))))
      +b1 = AG.rcs(s, Nat.add(Fs, C.shift(52n, one)), AG.mt(es, Fs), Equal.sym(Nat, AG.mt(es, Fs), Nat.add(Fs, C.shift(52n, one)), ms), Nat.sub(el, es), Nat.sub(AG.xe(el), AG.xe(es)), ek, Nat.add(Fl, C.shift(52n, one)), AG.mt(el, Fl), Equal.sym(Nat, AG.mt(el, Fl), Nat.add(Fl, C.shift(52n, one)), ml), Nat.add(1925n, es), AG.xe(es), Equal.sym(Nat, AG.xe(es), Nat.add(1925n, es), xs))
      Equal.trans(F.F64, F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(es, X.shl(fs, 10n)), Nat.sub(el, es)))), SF.round(s, Nat.sub(C.shift(Nat.sub(el, es), Nat.add(Fl, C.shift(52n, one))), Nat.add(Fs, C.shift(52n, one))), Nat.add(1925n, es)), SF.round(s, Nat.sub(C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl)), AG.mt(es, Fs)), AG.xe(es)), q, b1)

def bigS(+one: Nat, +h1: {one == 1n : Nat}, +s: Bool, +el: Nat, +fl: WU.U64, +es: Nat, +fs: WU.U64, +Fl: Nat, +Fs: Nat, +hfl: {SW.value(fl) == Fl : Nat}, +hfs: {SW.value(fs) == Fs : Nat}, +hFl: {C.fits(52n, Fl) == True{} : Bool}, +hFs: {C.fits(52n, Fs) == True{} : Bool}, +hlt: {Nat.is_lt(es, el) == True{} : Bool}) -> {F.norm_round_pack(s, Nat.add(F.off(), Nat.sub(el, 1n)), X.sub(X.add(X.shl(fl, 10n), WU.U64{0, 1073741824}), X.shr_jam(F.sm_small(es, X.shl(fs, 10n)), Nat.sub(el, es)))) == SF.round(s, Nat.sub(C.shift(Nat.sub(AG.xe(el), AG.xe(es)), AG.mt(el, Fl)), AG.mt(es, Fs)), AG.xe(es)) : F.F64}:
  bigS_c(one, h1, s, el, fl, es, fs, Fl, Fs, hfl, hfs, hFl, hFs, hlt, Nat.is_eq(es, 0n), {==})

