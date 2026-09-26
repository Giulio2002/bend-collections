import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../natural/arith.bend as NR
import ../natural/bits.bend as BT
import ./w64dm.bend as DM
import ./w64div.bend as W64D
import ./w64mul.bend as W64M
import ./w64sqrt.bend as W64S
import ./w64add.bend as WA
import ./w64sh.bend as SH
import ./w64clz.bend as CLZ
import ./f64bl.bend as BL
import ./width.bend as WW
import ./u32laws.bend as LW

# The quotient estimate of src/math/w64.bend's q96 is never below the
# quotient: for x = xh 2^64 + xl < b 2^32, b >= 2^32 and t = bits(hi(b)),
# Y = x >> t and B = b >> t (B >= 1, B 2^t <= b), x < (floor(Y / B) + 1) b.
# This is the easy half of Knuth's Theorem B (TAOCP vol. 2, 4.3.1): the
# normalised trial quotient is at least the true one, so q96's down loop
# alone reaches floor(x / b) (the loop invariant of w64dm.bend's qs_pair).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- on naturals ----

# x < (high(t, x) + 1) 2^t
def up_x(+t: Nat, +x: Nat) -> {Nat.is_lt(x, C.shift(t, 1n+C.high(t, x))) == True{} : Bool}:
  +h = C.high(t, x)
  +l0 = C.low(t, x)
  +s = C.shift(t, h)
  +p = C.pow2(t)
  +a1 = Equal.trans(Bool, Nat.is_lt(Nat.add(l0, s), Nat.add(p, s)), Nat.is_lt(l0, p), True{}, WW.lt_cancel_r(l0, p, s), WW.low_lt(t, x))
  +e1 = Equal.trans(Nat, Nat.add(p, s), Nat.add(C.shift(t, 1n), s), C.shift(t, 1n+h), Equal.cong(Nat, Nat, z => Nat.add(z, s), p, C.shift(t, 1n), Equal.sym(Nat, C.shift(t, 1n), p, WW.shift_one(t))), Equal.sym(Nat, C.shift(t, Nat.add(1n, h)), Nat.add(C.shift(t, 1n), s), WW.shift_add(t, 1n, h)))
  +a2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(l0, s), z) == True{} : Bool}, Nat.add(p, s), C.shift(t, 1n+h), e1, a1)
  L.subst(Nat, z => {Nat.is_lt(z, C.shift(t, 1n+h)) == True{} : Bool}, Nat.add(l0, s), x, Equal.sym(Nat, x, Nat.add(l0, s), WW.low_high(t, x)), a2)

# high(t, b) 2^t <= b
def shb_le(+t: Nat, +bv: Nat) -> {Nat.is_le(C.shift(t, C.high(t, bv)), bv) == True{} : Bool}:
  +s = C.shift(t, C.high(t, bv))
  +l0 = C.low(t, bv)
  +eq = Equal.trans(Nat, Nat.add(s, l0), Nat.add(l0, s), bv, N.add_comm(s, l0), Equal.sym(Nat, bv, Nat.add(l0, s), WW.low_high(t, bv)))
  L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, Nat.add(s, l0), bv, eq, N.le_add_right(s, l0))

# y + 1 <= (y / B + 1) B
def succ_le(+bp: Nat, +y: Nat) -> {Nat.is_le(1n+y, Nat.mul(1n+Nat.div(y, 1n+bp), 1n+bp)) == True{} : Bool}:
  +q = Nat.div(y, 1n+bp)
  +r = Nat.mod(y, 1n+bp)
  +mq = Nat.mul(q, 1n+bp)
  +ey = Equal.trans(Nat, y, Nat.add(mq, r), Nat.add(r, mq), NR.dm_eq(bp, y), N.add_comm(mq, r))
  +e1 = Equal.cong(Nat, Nat, z => 1n+z, y, Nat.add(r, mq), ey)
  +hle = WW.le_add_r(1n+r, 1n+bp, mq, N.lt_succ_le_succ(r, 1n+bp, NR.dm_lt(bp, y)))
  L.subst(Nat, z => {Nat.is_le(z, Nat.mul(1n+q, 1n+bp)) == True{} : Bool}, Nat.add(1n+r, mq), 1n+y, Equal.sym(Nat, 1n+y, Nat.add(1n+r, mq), e1), hle)

# x < (high(t, x) / high(t, b) + 1) b for high(t, b) >= 1
def core(+t: Nat, +x: Nat, +bv: Nat, +bp: Nat, +hb: {C.high(t, bv) == 1n+bp : Nat}) -> {Nat.is_lt(x, Nat.mul(1n+Nat.div(C.high(t, x), 1n+bp), bv)) == True{} : Bool}:
  +y = C.high(t, x)
  +q = Nat.div(y, 1n+bp)
  +a1 = up_x(t, x)
  +a2 = WW.shift_mono(t, 1n+y, Nat.mul(1n+q, 1n+bp), succ_le(bp, y))
  +a4 = W64M.le_mul_r(1n+q, C.shift(t, 1n+bp), bv, L.subst(Nat, z => {Nat.is_le(C.shift(t, z), bv) == True{} : Bool}, C.high(t, bv), 1n+bp, hb, shb_le(t, bv)))
  +a5 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(1n+q, bv)) == True{} : Bool}, Nat.mul(1n+q, C.shift(t, 1n+bp)), C.shift(t, Nat.mul(1n+q, 1n+bp)), WW.shift_mul_r(t, 1n+q, 1n+bp), a4)
  N.lt_le_trans(x, C.shift(t, 1n+y), Nat.mul(1n+q, bv), a1, N.le_trans(C.shift(t, 1n+y), C.shift(t, Nat.mul(1n+q, 1n+bp)), Nat.mul(1n+q, bv), a2, a5))

# high(t, b) != 0 when 2^t <= b
def hpos(+t: Nat, +bv: Nat, +c: Bool, +hc: {Nat.is_eq(C.high(t, bv), 0n) == c : Bool}, +hle: {Nat.is_le(C.pow2(t), bv) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +p = C.pow2(t)
      +lt = N.le_lt_trans(p, bv, p, hle, WW.lt_of_fits(t, bv, hc))
      Empty.absurd({True{} == False{} : Bool}, LW.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(p, p), False{}, Equal.sym(Bool, Nat.is_lt(p, p), True{}, lt), N.lt_irrefl(p))))

# ---- on words ----

def lo_fit(+w: WU.U64, +hf: {C.fits(32n, SW.value(w)) == True{} : Bool}) -> {v(X.lo(w)) == SW.value(w) : Nat}:
  match w:
    case WU.U64{+l, +h}:
      Equal.trans(Nat, v(l), C.low(32n, SW.value(WU.U64{l, h})), SW.value(WU.U64{l, h}), Equal.sym(Nat, C.low(32n, Nat.add(v(l), C.shift(32n, v(h)))), v(l), WW.low_u(32n, v(l), v(h), LW.vb(l))), WW.low_fit(32n, SW.value(WU.U64{l, h}), hf))

def lo_hi0(+w: WU.U64, +hz: {U32.is_zero(X.hi(w)) == True{} : Bool}) -> {v(X.lo(w)) == SW.value(w) : Nat}:
  match w:
    case WU.U64{+l, +h}:
      +eh = N.eq_from_is_eq(v(h), 0n, Equal.trans(Bool, Nat.is_eq(v(h), 0n), U32.is_zero(h), True{}, Equal.sym(Bool, U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h)), hz))
      +e2 = Equal.trans(Nat, Nat.add(v(l), C.shift(32n, v(h))), Nat.add(v(l), C.shift(32n, 0n)), v(l), Equal.cong(Nat, Nat, z => Nat.add(v(l), C.shift(32n, z)), v(h), 0n, eh), Equal.trans(Nat, Nat.add(v(l), C.shift(32n, 0n)), Nat.add(v(l), 0n), v(l), Equal.cong(Nat, Nat, z => Nat.add(v(l), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(l))))
      Equal.sym(Nat, SW.value(WU.U64{l, h}), v(l), e2)

# 1 + v(m) == 2^32 for the all-ones word
def m32(+one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {1n+v(m) == C.shift(32n, one) : Nat}:
  Equal.trans(Nat, 1n+v(m), WD.sc(32n, one), C.shift(32n, one), W64S.mask_v(32n, {==}, one, h1, m, pm), Equal.sym(Nat, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one)))

# the clamp to 2^32 - 1 keeps x < (q + 1) b, as x < 2^32 b
def cl(+one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +hm: {4294967295 == m : U32}, +x: Nat, +bv: Nat, +q: WU.U64, +c: Bool, +hc: {U32.is_zero(X.hi(q)) == c : Bool}, +hq: {Nat.is_lt(x, Nat.mul(1n+SW.value(q), bv)) == True{} : Bool}, +hX: {Nat.is_lt(x, Nat.mul(C.shift(32n, one), bv)) == True{} : Bool}) -> {Nat.is_lt(x, Nat.mul(1n+v(X.q_clamp_z(X.lo(q), c)), bv)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Nat.is_lt(x, Nat.mul(1n+z, bv)) == True{} : Bool}, SW.value(q), v(X.lo(q)), Equal.sym(Nat, v(X.lo(q)), SW.value(q), lo_hi0(q, hc)), hq)
    case False{}:
      +hm1 = L.subst(Nat, z => {Nat.is_lt(x, Nat.mul(z, bv)) == True{} : Bool}, C.shift(32n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), C.shift(32n, one), m32(one, h1, m, pm)), hX)
      L.subst(U32, z => {Nat.is_lt(x, Nat.mul(1n+v(z), bv)) == True{} : Bool}, m, 4294967295, Equal.sym(U32, 4294967295, m, hm), hm1)

# x >> t as the sum of xl >> t and xh << (64 - t), below 2^64
def yv(+xl: WU.U64, +xh: U32, +t: Nat, +t1: {Nat.is_le(1n, t) == True{} : Bool}, +t32: {Nat.is_le(t, 32n) == True{} : Bool}, +hx: {C.fits(Nat.add(64n, t), DM.X96(xl, xh)) == True{} : Bool}) -> {SW.value(X.add(X.shr(xl, t), X.shl(WU.U64{xh, 0}, Nat.sub(64n, t)))) == C.high(t, DM.X96(xl, xh)) : Nat}:
  +k = Nat.sub(64n, t)
  +x9 = DM.X96(xl, xh)
  +t64 = N.le_trans(t, 32n, 64n, t32, {==})
  +ek = N.sub_add(64n, t, t64)
  +h64 = Equal.trans(Bool, Nat.is_lt(Nat.add(64n, 0n), Nat.add(64n, t)), Nat.is_lt(0n, t), True{}, WW.lt_cancel_l(64n, 0n, t), N.succ_le_lt(0n, t, t1))
  +hk = N.sub_lt(64n, t, 64n, t64, L.subst(Nat, z => {Nat.is_lt(64n, z) == True{} : Bool}, Nat.add(64n, t), Nat.add(t, 64n), N.add_comm(64n, t), h64))
  +exh = WW.high_u(64n, SW.value(xl), v(xh), DM.fit64(xl))
  +fxh = L.subst(Nat, z => {C.fits(t, z) == True{} : Bool}, C.high(64n, x9), v(xh), exh, SH.fits_high(64n, t, x9, hx))
  +s = C.shift(k, v(xh))
  +eka = Equal.trans(Nat, Nat.add(k, t), Nat.add(t, k), 64n, N.add_comm(k, t), ek)
  +hs0 = WW.shift_lt(k, v(xh), C.pow2(t), WW.lt_of_fits(t, v(xh), fxh))
  +hs = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, C.shift(k, C.pow2(t)), C.pow2(64n), Equal.trans(Nat, C.shift(k, C.pow2(t)), C.pow2(Nat.add(k, t)), C.pow2(64n), WW.shift_pow2(k, t), Equal.cong(Nat, Nat, z => C.pow2(z), Nat.add(k, t), 64n, eka)), hs0)
  +els = WW.low_fit(64n, s, WW.fits_of_lt(64n, s, hs))
  +esh = Equal.trans(Nat, C.shift(64n, v(xh)), C.shift(Nat.add(t, k), v(xh)), C.shift(t, s), Equal.cong(Nat, Nat, z => C.shift(z, v(xh)), 64n, Nat.add(t, k), Equal.sym(Nat, Nat.add(t, k), 64n, ek)), WW.shift_comp(t, k, v(xh)))
  +ex = Equal.cong(Nat, Nat, z => Nat.add(SW.value(xl), z), C.shift(64n, v(xh)), C.shift(t, s), esh)
  +ehx = Equal.trans(Nat, C.high(t, x9), C.high(t, Nat.add(SW.value(xl), C.shift(t, s))), Nat.add(C.high(t, SW.value(xl)), s), Equal.cong(Nat, Nat, z => C.high(t, z), x9, Nat.add(SW.value(xl), C.shift(t, s)), ex), WW.high_add_shift(t, SW.value(xl), s))
  +hx2 = L.subst(Nat, z => {C.fits(z, x9) == True{} : Bool}, Nat.add(64n, t), Nat.add(t, 64n), N.add_comm(64n, t), hx)
  +fy = SH.fits_high(t, 64n, x9, hx2)
  +a = X.shr(xl, t)
  +bw = X.shl(WU.U64{xh, 0}, k)
  +eb = Equal.trans(Nat, SW.value(bw), C.low(64n, C.shift(k, SW.value(WU.U64{xh, 0}))), s, SH.shl_value(WU.U64{xh, 0}, k, hk), Equal.trans(Nat, C.low(64n, C.shift(k, SW.value(WU.U64{xh, 0}))), C.low(64n, s), s, Equal.cong(Nat, Nat, z => C.low(64n, C.shift(k, z)), SW.value(WU.U64{xh, 0}), v(xh), DM.u32_0(xh)), els))
  +esum = Equal.trans(Nat, Nat.add(SW.value(a), SW.value(bw)), Nat.add(C.high(t, SW.value(xl)), s), C.high(t, x9), Equal.trans(Nat, Nat.add(SW.value(a), SW.value(bw)), Nat.add(C.high(t, SW.value(xl)), SW.value(bw)), Nat.add(C.high(t, SW.value(xl)), s), Equal.cong(Nat, Nat, z => Nat.add(z, SW.value(bw)), SW.value(a), C.high(t, SW.value(xl)), SH.shr_value(xl, t)), Equal.cong(Nat, Nat, z => Nat.add(C.high(t, SW.value(xl)), z), SW.value(bw), s, eb)), Equal.sym(Nat, C.high(t, x9), Nat.add(C.high(t, SW.value(xl)), s), ehx))
  Equal.trans(Nat, SW.value(X.add(a, bw)), C.low(64n, Nat.add(SW.value(a), SW.value(bw))), C.high(t, x9), WA.add_value(a, bw), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(a), SW.value(bw))), C.low(64n, C.high(t, x9)), C.high(t, x9), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.add(SW.value(a), SW.value(bw)), C.high(t, x9), esum), WW.low_fit(64n, C.high(t, x9), fy)))

# 1 <= high(t, b) for t <= 32 and b >= 2^32
def hpos_le(+one: Nat, +h1: {one == 1n : Nat}, +bl: U32, +bh: U32, +t: Nat, +t32: {Nat.is_le(t, 32n) == True{} : Bool}, +hz: {U32.is_zero(bh) == False{} : Bool}) -> {Nat.is_le(1n, C.high(t, SW.value(WU.U64{bl, bh}))) == True{} : Bool}:
  +bv = SW.value(WU.U64{bl, bh})
  +hH0 = Equal.trans(Bool, Nat.is_eq(v(bh), 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(v(bh), 0n), LW.zero_nat(bh)), hz)
  +a1 = WW.shift_mono(32n, 1n, v(bh), WA.pos_ne(v(bh), hH0))
  +a2 = L.subst(Nat, z => {Nat.is_le(C.shift(32n, v(bh)), z) == True{} : Bool}, Nat.add(C.shift(32n, v(bh)), v(bl)), bv, N.add_comm(C.shift(32n, v(bh)), v(bl)), N.le_add_right(C.shift(32n, v(bh)), v(bl)))
  +a3 = L.subst(Nat, z => {Nat.is_le(z, bv) == True{} : Bool}, C.shift(32n, 1n), C.pow2(32n), WW.shift_one(32n), N.le_trans(C.shift(32n, 1n), C.shift(32n, v(bh)), bv, a1, a2))
  +hle = N.le_trans(C.pow2(t), C.pow2(32n), bv, N.pow2_mono(t, 32n, t32), a3)
  WA.pos_ne(C.high(t, bv), hpos(t, bv, Nat.is_eq(C.high(t, bv), 0n), {==}, hle))

# the estimate for B = high(t, b) = 1 + bp
def est_m(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +bl: U32, +bh: U32, +hz: {U32.is_zero(bh) == False{} : Bool}, +t: Nat, +t1: {Nat.is_le(1n, t) == True{} : Bool}, +t32: {Nat.is_le(t, 32n) == True{} : Bool}, +hx: {C.fits(Nat.add(64n, t), DM.X96(xl, xh)) == True{} : Bool}, +fb: {C.fits(32n, C.high(t, SW.value(WU.U64{bl, bh}))) == True{} : Bool}, +hX: {Nat.is_lt(DM.X96(xl, xh), Nat.mul(C.shift(32n, one), SW.value(WU.U64{bl, bh}))) == True{} : Bool}, +nb: Nat, +hnb: {C.high(t, SW.value(WU.U64{bl, bh})) == nb : Nat}) -> {Nat.is_lt(DM.X96(xl, xh), Nat.mul(1n+v(X.q_est(xl, xh, WU.U64{bl, bh}, t)), SW.value(WU.U64{bl, bh}))) == True{} : Bool}:
  match nb:
    case 0n:
      Empty.absurd({Nat.is_lt(DM.X96(xl, xh), Nat.mul(1n+v(X.q_est(xl, xh, WU.U64{bl, bh}, t)), SW.value(WU.U64{bl, bh}))) == True{} : Bool}, LW.true_ne_false(Equal.sym(Bool, False{}, True{}, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, C.high(t, SW.value(WU.U64{bl, bh})), 0n, hnb, hpos_le(one, h1, bl, bh, t, t32, hz)))))
    case 1n+ +bp:
      +b : WU.U64 = WU.U64{bl, bh}
      +bv = SW.value(b)
      +x9 = DM.X96(xl, xh)
      +yw = X.add(X.shr(xl, t), X.shl(WU.U64{xh, 0}, Nat.sub(64n, t)))
      +sw = X.shr(b, t)
      +bw = X.lo(sw)
      +ebw = Equal.trans(Nat, v(bw), SW.value(sw), 1n+bp, lo_fit(sw, L.subst(Nat, z => {C.fits(32n, z) == True{} : Bool}, C.high(t, bv), SW.value(sw), Equal.sym(Nat, SW.value(sw), C.high(t, bv), SH.shr_value(b, t)), fb)), Equal.trans(Nat, SW.value(sw), C.high(t, bv), 1n+bp, SH.shr_value(b, t), hnb))
      +hd = Equal.trans(Bool, U32.is_zero(bw), Nat.is_eq(v(bw), 0n), False{}, LW.zero_nat(bw), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), v(bw), 1n+bp, ebw))
      +qw = X.fst_q(X.div32(yw, bw))
      +eq = Equal.trans(Nat, SW.value(qw), Nat.div(SW.value(yw), v(bw)), Nat.div(C.high(t, x9), 1n+bp), W64D.div32_quot(yw, bw, hd), Equal.trans(Nat, Nat.div(SW.value(yw), v(bw)), Nat.div(C.high(t, x9), v(bw)), Nat.div(C.high(t, x9), 1n+bp), Equal.cong(Nat, Nat, z => Nat.div(z, v(bw)), SW.value(yw), C.high(t, x9), yv(xl, xh, t, t1, t32, hx)), Equal.cong(Nat, Nat, z => Nat.div(C.high(t, x9), z), v(bw), 1n+bp, ebw)))
      +hq = L.subst(Nat, z => {Nat.is_lt(x9, Nat.mul(1n+z, bv)) == True{} : Bool}, Nat.div(C.high(t, x9), 1n+bp), SW.value(qw), Equal.sym(Nat, SW.value(qw), Nat.div(C.high(t, x9), 1n+bp), eq), core(t, x9, bv, bp, hnb))
      cl(one, h1, 4294967295, {==}, {==}, x9, bv, qw, U32.is_zero(X.hi(qw)), {==}, hq, hX)


def est_t(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +bl: U32, +bh: U32, +hz: {U32.is_zero(bh) == False{} : Bool}, +hX: {Nat.is_lt(DM.X96(xl, xh), Nat.mul(C.shift(32n, one), SW.value(WU.U64{bl, bh}))) == True{} : Bool}, +t: Nat, +ht: {X.bitlen(bh) == t : Nat}) -> {Nat.is_lt(DM.X96(xl, xh), Nat.mul(1n+v(X.q_est(xl, xh, WU.U64{bl, bh}, t)), SW.value(WU.U64{bl, bh}))) == True{} : Bool}:
  +hh = v(bh)
  +bv = SW.value(WU.U64{bl, bh})
  +x9 = DM.X96(xl, xh)
  +et = Equal.trans(Nat, M.bit_length(hh), X.bitlen(bh), t, Equal.sym(Nat, X.bitlen(bh), M.bit_length(hh), CLZ.bitlen_v(bh)), ht)
  +hH0 = Equal.trans(Bool, Nat.is_eq(hh, 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(hh, 0n), LW.zero_nat(bh)), hz)
  +t1 = BL.bl_pos(hh, hH0, t, et)
  +t32 = L.subst(Nat, z => {Nat.is_le(z, 32n) == True{} : Bool}, M.bit_length(hh), t, et, BL.bl_le(32n, hh, LW.vb(bh), Nat.is_le(M.bit_length(hh), 32n), {==}))
  +hht = L.subst(Nat, z => {Nat.is_lt(hh, C.pow2(z)) == True{} : Bool}, M.bit_length(hh), t, et, BT.bit_length_lt(hh))
  +hbv = WW.two_limb_lt(32n, t, v(bl), hh, WW.lt_of_fits(32n, v(bl), LW.vb(bl)), hht)
  +fb = SH.fits_high(t, 32n, bv, WW.fits_of_lt(Nat.add(t, 32n), bv, L.subst(Nat, z => {Nat.is_lt(bv, C.pow2(z)) == True{} : Bool}, Nat.add(32n, t), Nat.add(t, 32n), N.add_comm(32n, t), hbv)))
  +s32 = C.shift(32n, one)
  +em = Equal.trans(Nat, Nat.mul(s32, bv), Nat.mul(bv, s32), C.shift(32n, bv), NA.mul_comm(s32, bv), Equal.sym(Nat, C.shift(32n, bv), Nat.mul(bv, s32), WW.shift_mul_one(32n, one, h1, bv)))
  +hx1 = L.subst(Nat, z => {Nat.is_lt(x9, z) == True{} : Bool}, Nat.mul(s32, bv), C.shift(32n, bv), em, hX)
  +hs = L.subst(Nat, z => {Nat.is_lt(C.shift(32n, bv), z) == True{} : Bool}, C.shift(32n, C.pow2(Nat.add(32n, t))), C.pow2(Nat.add(32n, Nat.add(32n, t))), WW.shift_pow2(32n, Nat.add(32n, t)), WW.shift_lt(32n, bv, C.pow2(Nat.add(32n, t)), hbv))
  +hx = WW.fits_of_lt(Nat.add(64n, t), x9, N.lt_le_trans(x9, C.shift(32n, bv), C.pow2(Nat.add(64n, t)), hx1, N.lt_le(C.shift(32n, bv), C.pow2(Nat.add(64n, t)), hs)))
  est_m(one, h1, xl, xh, bl, bh, hz, t, t1, t32, hx, fb, hX, C.high(t, bv), {==})

# the estimate is never below the quotient: x < (q_est + 1) b
def est_up(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +bl: U32, +bh: U32, +hz: {U32.is_zero(bh) == False{} : Bool}, +hX: {Nat.is_lt(DM.X96(xl, xh), Nat.mul(C.shift(32n, one), SW.value(WU.U64{bl, bh}))) == True{} : Bool}) -> {Nat.is_lt(DM.X96(xl, xh), Nat.mul(1n+v(X.q_est(xl, xh, WU.U64{bl, bh}, X.bitlen(bh))), SW.value(WU.U64{bl, bh}))) == True{} : Bool}:
  est_t(one, h1, xl, xh, bl, bh, hz, hX, X.bitlen(bh), {==})
