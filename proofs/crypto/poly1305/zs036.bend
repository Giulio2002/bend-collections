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
