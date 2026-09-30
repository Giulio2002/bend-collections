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

