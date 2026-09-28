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
