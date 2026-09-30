import Base
import ../../../spec/lib/common.bend as C
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64add.bend as WA
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/shrn.bend as SHN
import ../../math/typed/f64bits.bend as FB
import ./arith.bend as A
import ./value.bend as V

# One Poly1305 block on limbs: (h + c) r == block(r, h, c) + K p exactly, for
# an explicit K, and the block keeps the limb invariant (17 limbs, limbs
# 0..15 of 8 bits, limb 16 at most 4, so the value is below 5 * 2^128 < 2p).
# 2^k is C.shift(k, one) for a variable one = 1 (the checker would expand a
# closed 2^130), and p is pm(one) = 2^130 - 5.

def pm(+one: Nat) -> Nat:
  Nat.sub(C.shift(130n, one), 5n)

law p5:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {Nat.add(pm(one), 5n) == C.shift(130n, one) : Nat}

def p5(one, h1):
  +s = C.shift(130n, one)
  +h5 = N.le_trans(5n, C.shift(3n, one), s, L.subst(Nat, z => {Nat.is_le(5n, C.shift(3n, z)) == True{} : Bool}, 1n, one, A.sy(one, 1n, h1), {==}), WW.shift_ge(127n, C.shift(3n, one)))
  A.tr(Nat.add(Nat.sub(s, 5n), 5n), Nat.add(5n, Nat.sub(s, 5n)), s, N.add_comm(Nat.sub(s, 5n), 5n), N.sub_add(s, 5n, h5))

# 2^130 x = x p + 5 x
law big130:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +x: Nat
  {C.shift(130n, x) == Nat.add(Nat.mul(x, pm(one)), Nat.mul(x, 5n)) : Nat}

def big130(one, h1, x):
  A.tr(C.shift(130n, x), Nat.mul(x, C.shift(130n, one)), Nat.add(Nat.mul(x, pm(one)), Nat.mul(x, 5n)), WW.shift_mul_one(130n, one, h1, x),
    A.tr(Nat.mul(x, C.shift(130n, one)), Nat.mul(x, Nat.add(pm(one), 5n)), Nat.add(Nat.mul(x, pm(one)), Nat.mul(x, 5n)),
      Equal.cong(Nat, Nat, t => Nat.mul(x, t), C.shift(130n, one), Nat.add(pm(one), 5n), A.sy(Nat.add(pm(one), 5n), C.shift(130n, one), p5(one, h1))),
      NA.mul_add_left(x, pm(one), 5n)))

# a + (b + c) == (a + c) + b
def rot(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, c), b) : Nat}:
  A.tr(Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), WM.cong_r(a, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)), A.sy(Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), N.add_assoc(a, c, b)))

# ---- the fold 2^136 = 64 p + 320 ----

def s21(+one: Nat) -> Nat:
  C.shift(21n, one)

# the fold's limb bound: 321 * 2^21 < 2^30
def dbound(+one: Nat) -> Nat:
  Nat.add(s21(one), Nat.mul(s21(one), 320n))

law dbound_lt:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {Nat.is_lt(dbound(one), C.shift(30n, one)) == True{} : Bool}

def dbound_lt(one, h1):
  +s = s21(one)
  +l1 = A.lt_mul_l(s, 321n, 512n, A.one_le_shift(21n, one, h1), {==})
  +l2 = A.lt_subst(Nat.mul(s, 321n), Nat.mul(s, 512n), C.shift(9n, s), A.mul_pow(9n, s), l1)
  A.lt_substl(Nat.mul(s, 321n), dbound(one), C.shift(9n, s), NA.mul_succ(s, 320n), l2)

law dbound_fits:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {C.fits(32n, dbound(one)) == True{} : Bool}

def dbound_fits(one, h1):
  SH.fits_mono(30n, 32n, dbound(one), {==}, WW.fits_one(30n, one, h1, dbound(one), dbound_lt(one, h1)))

law fold_ev:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +z: List<&2, U32>
  for +hz: {V.le_all(z, s21(one)) == True{} : Bool}
  {V.ev(z) == Nat.add(V.ev(Li.fold(z)), Nat.mul(C.shift(6n, V.ev(Li.skip(17n, z))), pm(one))) : Nat}

def fold_ev(one, h1, z, hz):
  +s = s21(one)
  +tk = V.ev(Li.take(17n, z))
  +e = V.ev(Li.skip(17n, z))
  +f = C.shift(6n, e)
  +hs = V.le_skip(17n, z, s, hz)
  +hf4 = dbound_fits(one, h1)
  +hf3 = A.fits_add_r(32n, s, Nat.mul(s, 320n), hf4)
  +esc = V.scale_ev(320, Li.skip(17n, z), s, 320n, hs, {==}, hf3)
  +ed = V.add_ev(Li.take(17n, z), Li.scale(320, Li.skip(17n, z)), s, Nat.mul(s, 320n), V.le_take(17n, z, s, hz), V.scale_le(320, Li.skip(17n, z), s, 320n, hs, {==}, hf3), hf4)
  # e * 320 == 2^6 (e * 5)
  +e320 = A.tr(Nat.mul(e, 320n), Nat.mul(Nat.mul(e, 5n), 64n), Nat.mul(f, 5n), A.sy(Nat.mul(Nat.mul(e, 5n), 64n), Nat.mul(e, 320n), NA.mul_assoc(e, 5n, 64n)),
    A.tr(Nat.mul(Nat.mul(e, 5n), 64n), C.shift(6n, Nat.mul(e, 5n)), Nat.mul(f, 5n), A.mul_pow(6n, Nat.mul(e, 5n)), A.sy(Nat.mul(f, 5n), C.shift(6n, Nat.mul(e, 5n)), WW.shift_mul_l(6n, e, 5n))))
  +efold = A.tr(V.ev(Li.fold(z)), Nat.add(tk, V.ev(Li.scale(320, Li.skip(17n, z)))), Nat.add(tk, Nat.mul(f, 5n)), ed, WM.cong_r(tk, V.ev(Li.scale(320, Li.skip(17n, z))), Nat.mul(f, 5n), A.tr(V.ev(Li.scale(320, Li.skip(17n, z))), Nat.mul(e, 320n), Nat.mul(f, 5n), esc, e320)))
  A.tr(V.ev(z), Nat.add(tk, V.pos(17n, e)), Nat.add(V.ev(Li.fold(z)), Nat.mul(f, pm(one))), V.ts_ev(17n, z),
    A.tr(Nat.add(tk, V.pos(17n, e)), Nat.add(tk, Nat.add(Nat.mul(f, pm(one)), Nat.mul(f, 5n))), Nat.add(V.ev(Li.fold(z)), Nat.mul(f, pm(one))),
      WM.cong_r(tk, V.pos(17n, e), Nat.add(Nat.mul(f, pm(one)), Nat.mul(f, 5n)), big130(one, h1, f)),
      A.tr(Nat.add(tk, Nat.add(Nat.mul(f, pm(one)), Nat.mul(f, 5n))), Nat.add(Nat.add(tk, Nat.mul(f, 5n)), Nat.mul(f, pm(one))), Nat.add(V.ev(Li.fold(z)), Nat.mul(f, pm(one))),
        rot(tk, Nat.mul(f, pm(one)), Nat.mul(f, 5n)),
        WM.cong_l(Nat.add(tk, Nat.mul(f, 5n)), V.ev(Li.fold(z)), Nat.mul(f, pm(one)), A.sy(V.ev(Li.fold(z)), Nat.add(tk, Nat.mul(f, 5n)), efold)))))

law fold_fit:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +z: List<&2, U32>
  for +hz: {V.le_all(z, s21(one)) == True{} : Bool}
  {V.fit_all(Li.fold(z), 30n) == True{} : Bool}

def fold_fit(one, h1, z, hz):
  +s = s21(one)
  +hs = V.le_skip(17n, z, s, hz)
  +hf4 = dbound_fits(one, h1)
  +hf3 = A.fits_add_r(32n, s, Nat.mul(s, 320n), hf4)
  V.le_fit(Li.fold(z), dbound(one), 30n, one, h1, dbound_lt(one, h1),
    V.add_le(Li.take(17n, z), Li.scale(320, Li.skip(17n, z)), s, Nat.mul(s, 320n), V.le_take(17n, z, s, hz), V.scale_le(320, Li.skip(17n, z), s, 320n, hs, {==}, hf3), hf4))

law fold_len:
  for +z: List<&2, U32>
  for +hl: {Nat.is_le(V.len(z), 33n) == True{} : Bool}
  {Nat.is_le(V.len(Li.fold(z)), 17n) == True{} : Bool}

def fold_len(z, hl):
  V.len_add(Li.take(17n, z), Li.scale(320, Li.skip(17n, z)), 17n, V.len_take(17n, z),
    A.le_substl(V.len(Li.skip(17n, z)), V.len(Li.scale(320, Li.skip(17n, z))), 17n, A.sy(V.len(Li.scale(320, Li.skip(17n, z))), V.len(Li.skip(17n, z)), V.len_scale(320, Li.skip(17n, z))),
      N.le_trans(V.len(Li.skip(17n, z)), 16n, 17n, V.len_skip(17n, z, 16n, hl), {==})))

# ---- the partial reduction ----

def pv(+d: List<&2, U32>) -> Nat:
  V.v(Li.quot(16n, Li.carry(16n, d, 0)))

# the limb invariant: 17 limbs, all of 8 bits, limb 16 at most 4
def inv(+h: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(V.len(h), 17n), Bool.and(V.fit_all(h, 8n), Nat.is_le(V.v(Li.hd0(Li.skip(16n, h))), 4n)))

# v(quot) fits 29 bits: the pass-1 top limb fits 31
law q29:
  for +d: List<&2, U32>
  for +hd: {V.fit_all(d, 30n) == True{} : Bool}
  {C.fits(29n, pv(d)) == True{} : Bool}

def q29(d, hd):
  +t = Li.carry(16n, d, 0)
  +top = Li.hd0(Li.skip(16n, t))
  +ftop = V.carry_top(16n, d, 0, 22n, {==}, hd, {==})
  +eq = A.tr(pv(d), V.v(U32.shrn(top, 2n)), C.high(2n, V.v(top)), Equal.cong(U32, Nat, w => V.v(w), Li.quot(16n, t), U32.shrn(top, 2n), V.quot_top(16n, t)), SHN.shrn_high(top, 2n))
  A.fits_subst(29n, C.high(2n, V.v(top)), pv(d), A.sy(pv(d), C.high(2n, V.v(top)), eq), SH.fits_high(2n, 29n, V.v(top), ftop))

# pass 2 on the split: its value is 5 q + the split
law pass2_ev:
  for +d: List<&2, U32>
  for +hd: {V.fit_all(d, 30n) == True{} : Bool}
  {V.ev(Li.reduce(d)) == Nat.add(Nat.mul(pv(d), 5n), V.ev(Li.split(16n, Li.carry(16n, d, 0)))) : Nat}

def pass2_ev(d, hd):
  +t = Li.carry(16n, d, 0)
  +q = Li.quot(16n, t)
  +vq = V.v(q)
  +a5 = U32.mul(q, 5)
  +t0 = Li.hd0(t)
  +y0 = U32.add(a5, t0)
  +s0 = U32.add(0, y0)
  +u1 = U32.shrn(s0, 8n)
  +rr = Li.split(15n, Li.tl(t))
  +hlo = V.carry_lo(16n, d, 0)
  +hq = q29(d, hd)
  +ea5 = A.tr(V.v(a5), C.low(32n, Nat.mul(vq, 5n)), Nat.mul(vq, 5n), SH.mul_low(q, 5), WW.low_fit(32n, Nat.mul(vq, 5n), A.fits_mul(29n, 3n, vq, 5n, hq, {==})))
  +ht0 = L.and_left(C.fits(8n, V.v(t0)), V.fit_all(Li.take(15n, Li.tl(t)), 8n), hlo)
  +hy0a = A.fits_5q(29n, vq, V.v(t0), hq, SH.fits_mono(8n, 29n, V.v(t0), {==}, ht0))
  +hy0 = A.fits_subst(32n, Nat.add(Nat.mul(vq, 5n), V.v(t0)), Nat.add(V.v(a5), V.v(t0)), WM.cong_l(Nat.mul(vq, 5n), V.v(a5), V.v(t0), A.sy(V.v(a5), Nat.mul(vq, 5n), ea5)), hy0a)
  +ey0 = WA.add_exact(1n, {==}, a5, t0, hy0)
  +hy = A.fits_subst(32n, Nat.add(V.v(a5), V.v(t0)), V.v(y0), A.sy(V.v(y0), Nat.add(V.v(a5), V.v(t0)), ey0), hy0)
  +es0 = WA.add_exact(1n, {==}, 0, y0, hy)
  +hs0 = A.fits_subst(32n, V.v(y0), V.v(s0), A.sy(V.v(s0), V.v(y0), es0), hy)
  +eu1 = SHN.shrn_high(s0, 8n)
  +hu1 = A.fits_subst(24n, C.high(8n, V.v(s0)), V.v(u1), A.sy(V.v(u1), C.high(8n, V.v(s0)), eu1), SH.fits_high(8n, 24n, V.v(s0), hs0))
  +hr = V.fit_mono(rr, 8n, 24n, {==}, V.split_fit(15n, Li.tl(t), L.and_right(C.fits(8n, V.v(t0)), V.fit_all(Li.take(15n, Li.tl(t)), 8n), hlo)))
  +c15 = V.ev(Li.carry(15n, rr, u1))
  +ce = V.carry_ev(15n, rr, u1, 16n, {==}, hr, hu1)
  +ec = A.tr(c15, Nat.add(c15, 0n), Nat.add(V.v(u1), V.ev(rr)), A.sy(Nat.add(c15, 0n), c15, N.add_zero(c15)), ce)
  +lo = V.v(U32.and(s0, 255))
  +elo = FB.andm(s0, 8n, 255, {==})
  +e4 = A.tr(Nat.add(lo, C.shift(8n, V.v(u1))), Nat.add(C.low(8n, V.v(s0)), C.shift(8n, C.high(8n, V.v(s0)))), V.v(s0),
    A.cadd(lo, C.low(8n, V.v(s0)), C.shift(8n, V.v(u1)), C.shift(8n, C.high(8n, V.v(s0))), elo, A.csh(8n, V.v(u1), C.high(8n, V.v(s0)), eu1)),
    A.sy(V.v(s0), Nat.add(C.low(8n, V.v(s0)), C.shift(8n, C.high(8n, V.v(s0)))), WW.low_high(8n, V.v(s0))))
  +er = C.shift(8n, V.ev(rr))
  A.tr(Nat.add(lo, C.shift(8n, c15)), Nat.add(lo, C.shift(8n, Nat.add(V.v(u1), V.ev(rr)))), Nat.add(Nat.mul(vq, 5n), Nat.add(V.v(t0), er)),
    WM.cong_r(lo, C.shift(8n, c15), C.shift(8n, Nat.add(V.v(u1), V.ev(rr))), A.csh(8n, c15, Nat.add(V.v(u1), V.ev(rr)), ec)),
    A.tr(Nat.add(lo, C.shift(8n, Nat.add(V.v(u1), V.ev(rr)))), Nat.add(Nat.add(lo, C.shift(8n, V.v(u1))), er), Nat.add(Nat.mul(vq, 5n), Nat.add(V.v(t0), er)),
      A.sy(Nat.add(Nat.add(lo, C.shift(8n, V.v(u1))), er), Nat.add(lo, C.shift(8n, Nat.add(V.v(u1), V.ev(rr)))), V.sh3(lo, V.v(u1), V.ev(rr))),
      A.tr(Nat.add(Nat.add(lo, C.shift(8n, V.v(u1))), er), Nat.add(V.v(s0), er), Nat.add(Nat.mul(vq, 5n), Nat.add(V.v(t0), er)),
        WM.cong_l(Nat.add(lo, C.shift(8n, V.v(u1))), V.v(s0), er, e4),
        A.tr(Nat.add(V.v(s0), er), Nat.add(Nat.add(V.v(a5), V.v(t0)), er), Nat.add(Nat.mul(vq, 5n), Nat.add(V.v(t0), er)),
          WM.cong_l(V.v(s0), Nat.add(V.v(a5), V.v(t0)), er, A.tr(V.v(s0), V.v(y0), Nat.add(V.v(a5), V.v(t0)), es0, ey0)),
          A.tr(Nat.add(Nat.add(V.v(a5), V.v(t0)), er), Nat.add(V.v(a5), Nat.add(V.v(t0), er)), Nat.add(Nat.mul(vq, 5n), Nat.add(V.v(t0), er)),
            N.add_assoc(V.v(a5), V.v(t0), er),
            WM.cong_l(V.v(a5), Nat.mul(vq, 5n), Nat.add(V.v(t0), er), ea5))))))

law reduce_ev:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +d: List<&2, U32>
  for +hd: {V.fit_all(d, 30n) == True{} : Bool}
  for +hl: {Nat.is_le(V.len(d), 17n) == True{} : Bool}
  {V.ev(d) == Nat.add(V.ev(Li.reduce(d)), Nat.mul(pv(d), pm(one))) : Nat}

def reduce_ev(one, h1, d, hd, hl):
  +t = Li.carry(16n, d, 0)
  +vq = pv(d)
  +esp = V.ev(Li.split(16n, t))
  +c = V.carry_ev(16n, d, 0, 22n, {==}, hd, {==})
  +sk = V.skip_long(17n, d, hl)
  +et = A.tr(V.ev(t), Nat.add(V.ev(t), 0n), V.ev(d), A.sy(Nat.add(V.ev(t), 0n), V.ev(t), N.add_zero(V.ev(t))),
    A.tr(Nat.add(V.ev(t), 0n), Nat.add(V.ev(t), V.pos(17n, V.ev(Li.skip(17n, d)))), V.ev(d), Equal.cong(List<&2, U32>, Nat, l => Nat.add(V.ev(t), V.pos(17n, V.ev(l))), [], Li.skip(17n, d), Equal.sym(List<&2, U32>, Li.skip(17n, d), [], sk)), c))
  +sq = V.sq_ev(16n, t)
  +et2 = A.tr(V.ev(t), Nat.add(Nat.add(esp, C.shift(130n, vq)), 0n), Nat.add(esp, C.shift(130n, vq)), A.sy(Nat.add(Nat.add(esp, C.shift(130n, vq)), 0n), V.ev(t), sq), N.add_zero(Nat.add(esp, C.shift(130n, vq))))
  +e2 = pass2_ev(d, hd)
  A.tr(V.ev(d), Nat.add(esp, C.shift(130n, vq)), Nat.add(V.ev(Li.reduce(d)), Nat.mul(vq, pm(one))), A.tr(V.ev(d), V.ev(t), Nat.add(esp, C.shift(130n, vq)), A.sy(V.ev(t), V.ev(d), et), et2),
    A.tr(Nat.add(esp, C.shift(130n, vq)), Nat.add(esp, Nat.add(Nat.mul(vq, pm(one)), Nat.mul(vq, 5n))), Nat.add(V.ev(Li.reduce(d)), Nat.mul(vq, pm(one))),
      WM.cong_r(esp, C.shift(130n, vq), Nat.add(Nat.mul(vq, pm(one)), Nat.mul(vq, 5n)), big130(one, h1, vq)),
      A.tr(Nat.add(esp, Nat.add(Nat.mul(vq, pm(one)), Nat.mul(vq, 5n))), Nat.add(Nat.add(esp, Nat.mul(vq, 5n)), Nat.mul(vq, pm(one))), Nat.add(V.ev(Li.reduce(d)), Nat.mul(vq, pm(one))),
        rot(esp, Nat.mul(vq, pm(one)), Nat.mul(vq, 5n)),
        WM.cong_l(Nat.add(esp, Nat.mul(vq, 5n)), V.ev(Li.reduce(d)), Nat.mul(vq, pm(one)),
          A.tr(Nat.add(esp, Nat.mul(vq, 5n)), Nat.add(Nat.mul(vq, 5n), esp), V.ev(Li.reduce(d)), N.add_comm(esp, Nat.mul(vq, 5n)), A.sy(V.ev(Li.reduce(d)), Nat.add(Nat.mul(vq, 5n), esp), e2))))))

# the top limb after the reduction is at most 4 (its value is below 5 * 2^128)
law reduce_top:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +d: List<&2, U32>
  for +hd: {V.fit_all(d, 30n) == True{} : Bool}
  {Nat.is_le(V.v(Li.hd0(Li.skip(16n, Li.reduce(d)))), 4n) == True{} : Bool}

def reduce_top(one, h1, d, hd):
  +h2 = Li.reduce(d)
  +t = Li.carry(16n, d, 0)
  +sp = Li.split(16n, t)
  +vq5 = Nat.mul(pv(d), 5n)
  +tp = V.v(Li.hd0(Li.skip(16n, h2)))
  +tt = Nat.add(tp, 0n)
  +x16 = V.ev(Li.take(16n, h2))
  +e16 = V.ev(Li.take(16n, t))
  +a3 = Nat.add(V.v(U32.and(Li.hd0(Li.skip(16n, t)), 3)), 0n)
  +p1 = V.pos(16n, one)
  +ts1 = V.ts_ev(16n, h2)
  +ts2 = V.ts_ev(16n, sp)
  +e2 = pass2_ev(d, hd)
  # ev(h2) = 5q + ev(take16 t) + 2^128 a3
  +ev2 = A.tr(V.ev(h2), Nat.add(vq5, V.ev(sp)), Nat.add(vq5, Nat.add(e16, V.pos(16n, a3))), e2, WM.cong_r(vq5, V.ev(sp), Nat.add(e16, V.pos(16n, a3)), ts2))
  +l1 = N.lt_le_trans(vq5, C.shift(32n, one), p1, WW.lt_one(32n, one, h1, vq5, A.fits_mul(29n, 3n, pv(d), 5n, q29(d, hd), {==})), WW.shift_ge(96n, C.shift(32n, one)))
  +l2 = V.ev_lt(Li.take(16n, t), one, h1, V.carry_lo(16n, d, 0))
  +b2 = A.lt_add2(vq5, Nat.add(e16, V.pos(16n, a3)), p1, Nat.add(p1, V.pos(16n, a3)), l1, A.lt_le_add(e16, V.pos(16n, a3), p1, V.pos(16n, a3), l2, N.le_refl(V.pos(16n, a3))))
  +e3 = A.tr(Nat.add(p1, Nat.add(p1, V.pos(16n, a3))), Nat.add(p1, V.pos(16n, Nat.add(one, a3))), V.pos(16n, Nat.add(one, Nat.add(one, a3))),
    WM.cong_r(p1, Nat.add(p1, V.pos(16n, a3)), V.pos(16n, Nat.add(one, a3)), A.sy(V.pos(16n, Nat.add(one, a3)), Nat.add(p1, V.pos(16n, a3)), V.pos_add(16n, one, a3))),
    A.sy(V.pos(16n, Nat.add(one, Nat.add(one, a3))), Nat.add(p1, V.pos(16n, Nat.add(one, a3))), V.pos_add(16n, one, Nat.add(one, a3))))
  +b1 = A.le_subst(V.pos(16n, tt), Nat.add(x16, V.pos(16n, tt)), V.ev(h2), A.sy(V.ev(h2), Nat.add(x16, V.pos(16n, tt)), ts1), A.le_add_l(x16, V.pos(16n, tt)))
  +b1b = A.le_subst(V.pos(16n, tt), V.ev(h2), Nat.add(vq5, Nat.add(e16, V.pos(16n, a3))), ev2, b1)
  +lt1 = N.le_lt_trans(V.pos(16n, tt), Nat.add(vq5, Nat.add(e16, V.pos(16n, a3))), V.pos(16n, Nat.add(one, Nat.add(one, a3))), b1b, A.lt_subst(Nat.add(vq5, Nat.add(e16, V.pos(16n, a3))), Nat.add(p1, Nat.add(p1, V.pos(16n, a3))), V.pos(16n, Nat.add(one, Nat.add(one, a3))), e3, b2))
  +lt2 = A.shift_cancel(128n, tt, Nat.add(one, Nat.add(one, a3)), lt1)
  +lt3 = L.subst(Nat, z => {Nat.is_lt(tt, Nat.add(z, Nat.add(z, a3))) == True{} : Bool}, one, 1n, h1, lt2)
  +a3v = V.v(U32.and(Li.hd0(Li.skip(16n, t)), 3))
  +xt = V.v(Li.hd0(Li.skip(16n, t)))
  +la = A.lt_substl(C.low(2n, xt), a3v, 4n, A.sy(a3v, C.low(2n, xt), FB.andm(Li.hd0(Li.skip(16n, t)), 2n, 3, {==})), WW.low_lt(2n, xt))
  +la3 = A.le_substl(a3v, a3, 3n, A.sy(a3, a3v, N.add_zero(a3v)), N.lt_succ_le(a3v, 3n, la))
  +lt5 = N.lt_le_trans(tt, Nat.add(1n, Nat.add(1n, a3)), 5n, lt3, la3)
  A.le_substl(tt, tp, 4n, N.add_zero(tp), N.lt_succ_le(tt, 4n, lt5))

law reduce_inv:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +d: List<&2, U32>
  for +hd: {V.fit_all(d, 30n) == True{} : Bool}
  {inv(Li.reduce(d)) == True{} : Bool}

def reduce_inv(one, h1, d, hd):
  +h2 = Li.reduce(d)
  +t = Li.carry(16n, d, 0)
  +y = Li.add([U32.mul(Li.quot(16n, t), 5)], Li.split(16n, t))
  +tp = V.v(Li.hd0(Li.skip(16n, h2)))
  +htop = reduce_top(one, h1, d, hd)
  +f8 = WW.fits_of_lt(8n, tp, N.le_lt_trans(tp, 4n, C.pow2(8n), htop, {==}))
  +hf = V.fit_split(16n, h2, 8n, V.carry_lo(16n, y, 0), L.and_intro(C.fits(8n, tp), True{}, f8, {==}))
  L.and_intro(Nat.is_eq(V.len(h2), 17n), Bool.and(V.fit_all(h2, 8n), Nat.is_le(tp, 4n)), {==}, L.and_intro(V.fit_all(h2, 8n), Nat.is_le(tp, 4n), hf, htop))

# ---- one block ----

def zz(+r: List<&2, U32>, +h: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  Li.mul(Li.add(h, c), r)

# the multiple of p dropped by one block
def bk(+r: List<&2, U32>, +h: List<&2, U32>, +c: List<&2, U32>) -> Nat:
  Nat.add(C.shift(6n, V.ev(Li.skip(17n, zz(r, h, c)))), pv(Li.fold(zz(r, h, c))))

# the product's limbs are at most 2^21, its length at most 33
law z_le:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +r: List<&2, U32>
  for +h: List<&2, U32>
  for +c: List<&2, U32>
  for +hh: {V.fit_all(h, 8n) == True{} : Bool}
  for +hcf: {V.fit_all(c, 8n) == True{} : Bool}
  for +hrl: {V.len(r) == 16n : Nat}
  for +hrf: {V.fit_all(r, 8n) == True{} : Bool}
  {V.le_all(zz(r, h, c), s21(one)) == True{} : Bool}

def s8fit(+one: Nat, +h1: {one == 1n : Nat}) -> {C.fits(32n, Nat.add(C.shift(8n, one), C.shift(8n, one))) == True{} : Bool}:
  +s8 = C.shift(8n, one)
  +f9 = A.fits_le_one(8n, one, h1, s8, N.le_refl(s8))
  SH.fits_mono(10n, 32n, Nat.add(s8, s8), {==}, A.fits_add(9n, s8, s8, f9, f9))

# len(r) * (2^9 * 2^8) == 2^21
def mbound(+one: Nat, +h1: {one == 1n : Nat}, +r: List<&2, U32>, +hrl: {V.len(r) == 16n : Nat}) -> {Nat.mul(V.len(r), Nat.mul(Nat.add(C.shift(8n, one), C.shift(8n, one)), C.shift(8n, one))) == s21(one) : Nat}:
  +s8 = C.shift(8n, one)
  +m = Nat.mul(Nat.add(s8, s8), s8)
  +em = A.tr(m, Nat.mul(C.shift(9n, one), s8), C.shift(17n, one), A.cmul(Nat.add(s8, s8), C.shift(9n, one), s8, s8, A.sy(Nat.double(s8), Nat.add(s8, s8), NA.double_self(s8)), {==}), A.shmul(9n, 8n, one, h1))
  A.tr(Nat.mul(V.len(r), m), Nat.mul(16n, m), s21(one), Equal.cong(Nat, Nat, t => Nat.mul(t, m), V.len(r), 16n, hrl),
    A.tr(Nat.mul(16n, m), Nat.mul(m, 16n), s21(one), NA.mul_comm(16n, m),
      A.tr(Nat.mul(m, 16n), C.shift(4n, m), s21(one), A.mul_pow(4n, m), A.csh(4n, m, C.shift(17n, one), em))))

def z_le(one, h1, r, h, c, hh, hcf, hrl, hrf):
  +s8 = C.shift(8n, one)
  +x = Li.add(h, c)
  +hf1 = s8fit(one, h1)
  +hx = V.add_le(h, c, s8, s8, V.fit_le(h, 8n, one, h1, hh), V.fit_le(c, 8n, one, h1, hcf), hf1)
  +eb = mbound(one, h1, r, hrl)
  +b = Nat.mul(V.len(r), Nat.mul(Nat.add(s8, s8), s8))
  +hf2 = A.fits_subst(32n, s21(one), b, A.sy(b, s21(one), eb), SH.fits_mono(22n, 32n, s21(one), {==}, A.fits_le_one(21n, one, h1, s21(one), N.le_refl(s21(one)))))
  V.le_mono(zz(r, h, c), b, s21(one), N.eq_le(b, s21(one), eb), V.mul_le(x, r, Nat.add(s8, s8), s8, hx, V.fit_le(r, 8n, one, h1, hrf), hf2))

