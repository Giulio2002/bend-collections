import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../lib/word.bend as WD
import ../../lib/u32.bend as U3
import ../../lib/lemmas/spec/numeric.bend as S
import ../u64/u64.bend as P64
import ./w64mul.bend as W64M
import ./w64sqrt.bend as W64S
import ./width.bend as WW
import ./u32laws.bend as LW
import ../../lib/u32half.bend as UH
import ../u64/u64div.bend as PD
import ../../lib/u32alg.bend as A
import ../natural/arith.bend as NR
import ../../lib/arith.bend as AR2

# The two-limb U64 arithmetic of src/math/w64.bend against the value model
# of spec/math/w64.bend: value(lo, hi) = lo + 2^32 hi. Every clause is the
# limb-by-limb carry/borrow argument of HACL*'s Hacl.Spec.Bignum.Addition
# (bn_add_lemma / bn_sub_lemma: the limb sum with its carry chain equals the
# full sum minus carry * 2^(64)), closed by the uniqueness of
# n == low(k, n) + 2^k high(k, n) (Mathlib Nat.mod_add_div,
# proofs/math/typed/width.bend). No 2^32 or 2^64 is ever formed.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def val(+l: U32, +h: U32) -> Nat:
  Nat.add(v(l), C.shift(32n, v(h)))

def bv(c: Bool) -> Nat:
  S.bit_value(c)

def vb(+x: U32) -> {C.fits(32n, v(x)) == True{} : Bool}:
  LW.vb(x)

# x + y == (x + y mod 2^32) + 2^32 carry
def acons(+x: U32, +y: U32) -> {Nat.add(v(U32.add(x, y)), C.shift(32n, bv(P64.carry32(x, y)))) == Nat.add(v(x), v(y)) : Nat}:
  +c = bv(P64.carry32(x, y))
  Equal.trans(Nat, Nat.add(v(U32.add(x, y)), C.shift(32n, c)), Nat.add(v(U32.add(x, y)), WD.sc(32n, c)), Nat.add(v(x), v(y)), Equal.cong(Nat, Nat, t => Nat.add(v(U32.add(x, y)), t), C.shift(32n, c), WD.sc(32n, c), W64M.shift_sc(32n, c)), P64.add_cons(x, y))

# the limb sums: al + bl == l + 2^32 c1, ah + bh == s + 2^32 c2, s + c1 == h + 2^32 c3
def add_alg(+al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +l: Nat, +c1: Nat, +s: Nat, +c2: Nat, +h: Nat, +c3: Nat, +e1: {Nat.add(l, C.shift(32n, c1)) == Nat.add(al, bl) : Nat}, +e2: {Nat.add(s, C.shift(32n, c2)) == Nat.add(ah, bh) : Nat}, +e3: {Nat.add(h, C.shift(32n, c3)) == Nat.add(s, c1) : Nat}) -> {Nat.add(Nat.add(al, C.shift(32n, ah)), Nat.add(bl, C.shift(32n, bh))) == Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, C.shift(32n, Nat.add(c3, c2)))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(al, C.shift(32n, ah)), Nat.add(bl, C.shift(32n, bh))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, C.shift(32n, Nat.add(c3, c2)))), Equal.trans(Nat, Nat.add(Nat.add(al, C.shift(32n, ah)), Nat.add(bl, C.shift(32n, bh))), Nat.add(Nat.add(al, bl), Nat.add(C.shift(32n, ah), C.shift(32n, bh))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), W64M.add4(al, C.shift(32n, ah), bl, C.shift(32n, bh)), Equal.trans(Nat, Nat.add(Nat.add(al, bl), Nat.add(C.shift(32n, ah), C.shift(32n, bh))), Nat.add(Nat.add(al, bl), C.shift(32n, Nat.add(ah, bh))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(al, bl), t), Nat.add(C.shift(32n, ah), C.shift(32n, bh)), C.shift(32n, Nat.add(ah, bh)), Equal.sym(Nat, C.shift(32n, Nat.add(ah, bh)), Nat.add(C.shift(32n, ah), C.shift(32n, bh)), WW.shift_add(32n, ah, bh))), Equal.trans(Nat, Nat.add(Nat.add(al, bl), C.shift(32n, Nat.add(ah, bh))), Nat.add(Nat.add(l, C.shift(32n, c1)), C.shift(32n, Nat.add(ah, bh))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(32n, Nat.add(ah, bh))), Nat.add(al, bl), Nat.add(l, C.shift(32n, c1)), Equal.sym(Nat, Nat.add(l, C.shift(32n, c1)), Nat.add(al, bl), e1)), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, c1)), C.shift(32n, Nat.add(ah, bh))), Nat.add(Nat.add(l, C.shift(32n, c1)), C.shift(32n, Nat.add(s, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(l, C.shift(32n, c1)), C.shift(32n, t)), Nat.add(ah, bh), Nat.add(s, C.shift(32n, c2)), Equal.sym(Nat, Nat.add(s, C.shift(32n, c2)), Nat.add(ah, bh), e2)), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, c1)), C.shift(32n, Nat.add(s, C.shift(32n, c2)))), Nat.add(Nat.add(l, C.shift(32n, c1)), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(l, C.shift(32n, c1)), t), C.shift(32n, Nat.add(s, C.shift(32n, c2))), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2))), WW.shift_add(32n, s, C.shift(32n, c2))), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, c1)), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, c1), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2))))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), NA.add_assoc(l, C.shift(32n, c1), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2)))), Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.add(C.shift(32n, c1), Nat.add(C.shift(32n, s), C.shift(32n, C.shift(32n, c2)))), Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2)))), NA.add_swap(C.shift(32n, c1), C.shift(32n, s), C.shift(32n, C.shift(32n, c2)))))))))), Equal.sym(Nat, Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, C.shift(32n, Nat.add(c3, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, C.shift(32n, Nat.add(c3, c2)))), Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, Nat.add(C.shift(32n, c3), C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, t)), C.shift(32n, Nat.add(c3, c2)), Nat.add(C.shift(32n, c3), C.shift(32n, c2)), WW.shift_add(32n, c3, c2)), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, h)), C.shift(32n, Nat.add(C.shift(32n, c3), C.shift(32n, c2)))), Nat.add(Nat.add(l, C.shift(32n, h)), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(l, C.shift(32n, h)), t), C.shift(32n, Nat.add(C.shift(32n, c3), C.shift(32n, c2))), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2))), WW.shift_add(32n, C.shift(32n, c3), C.shift(32n, c2))), Equal.trans(Nat, Nat.add(Nat.add(l, C.shift(32n, h)), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, h), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2))))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), NA.add_assoc(l, C.shift(32n, h), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2)))), Equal.trans(Nat, Nat.add(l, Nat.add(C.shift(32n, h), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2))))), Nat.add(l, Nat.add(Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.add(C.shift(32n, h), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2)))), Nat.add(Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2))), Nat.add(C.shift(32n, h), Nat.add(C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2)))), NA.add_assoc(C.shift(32n, h), C.shift(32n, C.shift(32n, c3)), C.shift(32n, C.shift(32n, c2))))), Equal.trans(Nat, Nat.add(l, Nat.add(Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, Nat.add(h, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(l, Nat.add(t, C.shift(32n, C.shift(32n, c2)))), Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), C.shift(32n, Nat.add(h, C.shift(32n, c3))), Equal.sym(Nat, C.shift(32n, Nat.add(h, C.shift(32n, c3))), Nat.add(C.shift(32n, h), C.shift(32n, C.shift(32n, c3))), WW.shift_add(32n, h, C.shift(32n, c3)))), Equal.trans(Nat, Nat.add(l, Nat.add(C.shift(32n, Nat.add(h, C.shift(32n, c3))), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, Nat.add(s, c1)), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(l, Nat.add(C.shift(32n, t), C.shift(32n, C.shift(32n, c2)))), Nat.add(h, C.shift(32n, c3)), Nat.add(s, c1), e3), Equal.trans(Nat, Nat.add(l, Nat.add(C.shift(32n, Nat.add(s, c1)), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(Nat.add(C.shift(32n, s), C.shift(32n, c1)), C.shift(32n, C.shift(32n, c2)))), Nat.add(l, Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2))))), Equal.cong(Nat, Nat, t => Nat.add(l, Nat.add(t, C.shift(32n, C.shift(32n, c2)))), C.shift(32n, Nat.add(s, c1)), Nat.add(C.shift(32n, s), C.shift(32n, c1)), WW.shift_add(32n, s, c1)), Equal.cong(Nat, Nat, t => Nat.add(l, t), Nat.add(Nat.add(C.shift(32n, s), C.shift(32n, c1)), C.shift(32n, C.shift(32n, c2))), Nat.add(C.shift(32n, s), Nat.add(C.shift(32n, c1), C.shift(32n, C.shift(32n, c2)))), NA.add_assoc(C.shift(32n, s), C.shift(32n, c1), C.shift(32n, C.shift(32n, c2)))))))))))))

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

# the full sum: the two limbs of the wrapped sum plus 2^64 (c3 + c2)
def add_eq(+al: U32, +ah: U32, +bl: U32, +bh: U32) -> {Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))) == Nat.add(Nat.add(v(U32.add(al, bl)), C.shift(32n, v(U32.add(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))))), C.shift(64n, Nat.add(bv(P64.carry32(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))), bv(P64.carry32(ah, bh))))) : Nat}:
  +l = U32.add(al, bl)
  +c1b = U32.is_lt(l, al)
  +s = U32.add(ah, bh)
  +cb = X.b32(c1b)
  +h = U32.add(s, cb)
  +q1 = P64.carry32(al, bl)
  +q2 = P64.carry32(ah, bh)
  +q3 = P64.carry32(s, cb)
  +e1 = acons(al, bl)
  +e2 = acons(ah, bh)
  +ecb = Equal.trans(Nat, v(cb), bv(c1b), bv(q1), W64M.b32_v(c1b), Equal.cong(Bool, Nat, t => bv(t), c1b, q1, P64.add_lt(al, bl)))
  +e3 = Equal.trans(Nat, Nat.add(v(h), C.shift(32n, bv(q3))), Nat.add(v(s), v(cb)), Nat.add(v(s), bv(q1)), acons(s, cb), Equal.cong(Nat, Nat, t => Nat.add(v(s), t), v(cb), bv(q1), ecb))
  +q = Nat.add(bv(q3), bv(q2))
  +eq = add_alg(v(al), v(ah), v(bl), v(bh), v(l), bv(q1), v(s), bv(q2), v(h), bv(q3), e1, e2, e3)
  +e64 = WW.shift_comp(32n, 32n, q)
  Equal.trans(Nat, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(Nat.add(v(l), C.shift(32n, v(h))), C.shift(32n, C.shift(32n, q))), Nat.add(Nat.add(v(l), C.shift(32n, v(h))), C.shift(64n, q)), eq, Equal.cong(Nat, Nat, t => Nat.add(Nat.add(v(l), C.shift(32n, v(h))), t), C.shift(32n, C.shift(32n, q)), C.shift(64n, q), Equal.sym(Nat, C.shift(64n, q), C.shift(32n, C.shift(32n, q)), e64)))

def add_value(+a: WU.U64, +b: WU.U64) -> SW.Add.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +R = Nat.add(v(U32.add(al, bl)), C.shift(32n, v(U32.add(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al))))))
      +q = Nat.add(bv(P64.carry32(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))), bv(P64.carry32(ah, bh)))
      +hR = WW.limbs_fit(32n, 32n, v(U32.add(al, bl)), v(U32.add(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))), vb(U32.add(al, bl)), vb(U32.add(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))))
      +lq = Equal.trans(Nat, C.low(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh))))), C.low(64n, Nat.add(R, C.shift(64n, q))), R, Equal.cong(Nat, Nat, t => C.low(64n, t), Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(R, C.shift(64n, q)), add_eq(al, ah, bl, bh)), WW.low_u(64n, R, q, hR))
      Equal.sym(Nat, C.low(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh))))), R, lq)

def plus1(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  Equal.trans(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), 1n+x, NA.add_succ(x, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(x, 0n), x, N.add_zero(x)))

# x + y == (x + y mod 2^32) + 2^32 carry, the carry a bit worth one
def acons_o(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32) -> {Nat.add(v(U32.add(x, y)), C.shift(32n, WD.bo(P64.carry32(x, y), one))) == Nat.add(v(x), v(y)) : Nat}:
  +c = P64.carry32(x, y)
  Equal.trans(Nat, Nat.add(v(U32.add(x, y)), C.shift(32n, WD.bo(c, one))), Nat.add(v(U32.add(x, y)), C.shift(32n, bv(c))), Nat.add(v(x), v(y)), Equal.cong(Nat, Nat, t => Nat.add(v(U32.add(x, y)), C.shift(32n, t)), WD.bo(c, one), bv(c), WD.bo_bit(c, one, h1)), acons(x, y))

# no carry out of a sum that fits
def no_carry(+one: Nat, +h1: {one == 1n : Nat}, +r: Nat, +c: Bool, +t: Nat, +e: {Nat.add(r, C.shift(32n, WD.bo(c, one))) == t : Nat}, +ht: {C.fits(32n, t) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.trans(Bool, True{}, C.fits(32n, t), False{}, Equal.sym(Bool, C.fits(32n, t), True{}, ht), Equal.trans(Bool, C.fits(32n, t), C.fits(32n, Nat.add(r, C.shift(32n, one))), False{}, Equal.cong(Nat, Bool, z => C.fits(32n, z), t, Nat.add(r, C.shift(32n, one)), Equal.sym(Nat, Nat.add(r, C.shift(32n, one)), t, e)), WW.unfit_one(32n, one, h1, r)))))

# s + 1 carries exactly when s is all ones (1 + vm == 2^32)
def c_one(+one: Nat, +h1: {one == 1n : Nat}, +r: Nat, +vs: Nat, +vm: Nat, +cc: Bool, +e: {Nat.add(r, C.shift(32n, WD.bo(cc, one))) == Nat.add(vs, 1n) : Nat}, +em: {1n+vm == C.shift(32n, one) : Nat}, +hr: {C.fits(32n, r) == True{} : Bool}, +hs: {C.fits(32n, vs) == True{} : Bool}) -> {cc == Nat.is_eq(vs, vm) : Bool}:
  match cc:
    case True{}:
      +hs1 = L.subst(Nat, z => {Nat.is_lt(vs, z) == True{} : Bool}, C.shift(32n, one), 1n+vm, Equal.sym(Nat, 1n+vm, C.shift(32n, one), em), WW.lt_one(32n, one, h1, vs, hs))
      +hle = N.lt_succ_le(vs, vm, hs1)
      +e2 = Equal.trans(Nat, Nat.add(r, 1n+vm), Nat.add(r, C.shift(32n, one)), 1n+vs, Equal.cong(Nat, Nat, z => Nat.add(r, z), 1n+vm, C.shift(32n, one), em), Equal.trans(Nat, Nat.add(r, C.shift(32n, one)), Nat.add(vs, 1n), 1n+vs, e, plus1(vs)))
      +hge0 = L.subst(Nat, z => {Nat.is_le(1n+vm, z) == True{} : Bool}, Nat.add(r, 1n+vm), 1n+vs, e2, L.subst(Nat, z => {Nat.is_le(1n+vm, z) == True{} : Bool}, Nat.add(1n+vm, r), Nat.add(r, 1n+vm), N.add_comm(1n+vm, r), N.le_add_right(1n+vm, r)))
      +eqv = N.le_antisym(vs, vm, hle, hge0)
      Equal.sym(Bool, Nat.is_eq(vs, vm), True{}, L.subst(Nat, z => {Nat.is_eq(z, vm) == True{} : Bool}, vm, vs, Equal.sym(Nat, vs, vm, eqv), N.is_eq_refl(vm)))
    case False{}:
      +e0 = Equal.trans(Nat, r, Nat.add(r, 0n), 1n+vs, Equal.sym(Nat, Nat.add(r, 0n), r, N.add_zero(r)), Equal.trans(Nat, Nat.add(r, 0n), Nat.add(r, C.shift(32n, 0n)), 1n+vs, Equal.cong(Nat, Nat, z => Nat.add(r, z), 0n, C.shift(32n, 0n), Equal.sym(Nat, C.shift(32n, 0n), 0n, WW.shift_zero(32n))), Equal.trans(Nat, Nat.add(r, C.shift(32n, 0n)), Nat.add(vs, 1n), 1n+vs, e, plus1(vs))))
      +hr1 = L.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, C.shift(32n, one), 1n+vm, Equal.sym(Nat, 1n+vm, C.shift(32n, one), em), WW.lt_one(32n, one, h1, r, hr))
      +hlt = L.subst(Nat, z => {Nat.is_lt(z, 1n+vm) == True{} : Bool}, r, 1n+vs, e0, hr1)
      Equal.sym(Bool, Nat.is_eq(vs, vm), False{}, N.is_eq_lt(vs, vm, hlt))

# the carry of s + b32(c) is c and s all ones
def c3_eq(+one: Nat, +h1: {one == 1n : Nat}, +s: U32, +c: Bool, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {P64.carry32(s, X.b32(c)) == Bool.and(c, U32.is_eq(s, m)) : Bool}:
  match c:
    case False{}:
      +ht = L.subst(Nat, z => {C.fits(32n, z) == True{} : Bool}, v(s), Nat.add(v(s), 0n), Equal.sym(Nat, Nat.add(v(s), 0n), v(s), N.add_zero(v(s))), vb(s))
      no_carry(one, h1, v(U32.add(s, 0)), P64.carry32(s, 0), Nat.add(v(s), 0n), acons_o(one, h1, s, 0), ht)
    case True{}:
      +em = Equal.trans(Nat, 1n+v(m), WD.sc(32n, one), C.shift(32n, one), W64S.mask_v(32n, {==}, one, h1, m, pm), Equal.sym(Nat, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one)))
      +c1 = c_one(one, h1, v(U32.add(s, 1)), v(s), v(m), P64.carry32(s, 1), acons_o(one, h1, s, 1), em, vb(U32.add(s, 1)), vb(s))
      Equal.trans(Bool, P64.carry32(s, 1), Nat.is_eq(v(s), v(m)), U32.is_eq(s, m), c1, Equal.sym(Bool, U32.is_eq(s, m), Nat.is_eq(v(s), v(m)), LW.eq_nat(s, m)))

def aog(+s: U32, +ah: U32, c: Bool, +m: U32) -> Bool:
  Bool.or(U32.is_lt(s, ah), Bool.and(c, U32.is_eq(s, m)))

def or_bits(+c2: Bool, +c3: Bool) -> {Bool.or(c2, c3) == Bool.not(Nat.is_eq(Nat.add(bv(c3), bv(c2)), 0n)) : Bool}:
  match c2 c3:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def over_g(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {aog(U32.add(ah, bh), ah, U32.is_lt(U32.add(al, bl), al), m) == Bool.not(C.fits(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))))) : Bool}:
  +s = U32.add(ah, bh)
  +c1b = U32.is_lt(U32.add(al, bl), al)
  +q2 = P64.carry32(ah, bh)
  +q3 = P64.carry32(s, X.b32(c1b))
  +R = Nat.add(v(U32.add(al, bl)), C.shift(32n, v(U32.add(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al))))))
  +q = Nat.add(bv(P64.carry32(U32.add(ah, bh), X.b32(U32.is_lt(U32.add(al, bl), al)))), bv(P64.carry32(ah, bh)))
  +hR = WW.limbs_fit(32n, 32n, v(U32.add(al, bl)), v(U32.add(s, X.b32(c1b))), vb(U32.add(al, bl)), vb(U32.add(s, X.b32(c1b))))
  +ea = Equal.trans(Bool, aog(s, ah, c1b, m), Bool.or(q2, Bool.and(c1b, U32.is_eq(s, m))), Bool.or(q2, q3), Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(c1b, U32.is_eq(s, m))), U32.is_lt(s, ah), q2, P64.add_lt(ah, bh)), Equal.cong(Bool, Bool, t => Bool.or(q2, t), Bool.and(c1b, U32.is_eq(s, m)), q3, Equal.sym(Bool, q3, Bool.and(c1b, U32.is_eq(s, m)), c3_eq(one, h1, s, c1b, m, pm))))
  +eb = Equal.trans(Nat, C.high(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh))))), C.high(64n, Nat.add(R, C.shift(64n, q))), q, Equal.cong(Nat, Nat, t => C.high(64n, t), Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(R, C.shift(64n, q)), add_eq(al, ah, bl, bh)), WW.high_u(64n, R, q, hR))
  +ec = Equal.cong(Nat, Bool, t => Bool.not(Nat.is_eq(t, 0n)), C.high(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh))))), q, eb)
  Equal.trans(Bool, aog(s, ah, c1b, m), Bool.or(q2, q3), Bool.not(C.fits(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))))), ea, Equal.trans(Bool, Bool.or(q2, q3), Bool.not(Nat.is_eq(q, 0n)), Bool.not(C.fits(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))))), or_bits(q2, q3), Equal.sym(Bool, Bool.not(C.fits(64n, Nat.add(Nat.add(v(al), C.shift(32n, v(ah))), Nat.add(v(bl), C.shift(32n, v(bh)))))), Bool.not(Nat.is_eq(q, 0n)), ec)))

def add_over_value(+a: WU.U64, +b: WU.U64) -> SW.AddOver.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      over_g(1n, {==}, al, ah, bl, bh, 4294967295, {==})

# ---- zero ----

def iz_n(+x: Nat, +y: Nat) -> {Bool.and(Nat.is_eq(x, 0n), Nat.is_eq(y, 0n)) == Nat.is_eq(Nat.add(x, C.shift(32n, y)), 0n) : Bool}:
  match x:
    case 0n:
      Equal.sym(Bool, Nat.is_eq(C.shift(32n, y), 0n), Nat.is_eq(y, 0n), WW.shift_eq0(32n, y))
    case 1n+xp:
      {==}

def is_zero_value(+a: WU.U64) -> SW.IsZero.value(a):
  match a:
    case WU.U64{+l, +h}:
      Equal.trans(Bool, Bool.and(U32.is_zero(l), U32.is_zero(h)), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(v(h), 0n)), Nat.is_eq(val(l, h), 0n), Equal.trans(Bool, Bool.and(U32.is_zero(l), U32.is_zero(h)), Bool.and(Nat.is_eq(v(l), 0n), U32.is_zero(h)), Bool.and(Nat.is_eq(v(l), 0n), Nat.is_eq(v(h), 0n)), Equal.cong(Bool, Bool, t => Bool.and(t, U32.is_zero(h)), U32.is_zero(l), Nat.is_eq(v(l), 0n), LW.zero_nat(l)), Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(v(l), 0n), t), U32.is_zero(h), Nat.is_eq(v(h), 0n), LW.zero_nat(h))), iz_n(v(l), v(h)))

# ---- comparisons and parity ----

def eq_value(+a: WU.U64, +b: WU.U64) -> SW.Eq.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +e1 = Equal.trans(Bool, Bool.and(U32.is_eq(al, bl), U32.is_eq(ah, bh)), Bool.and(Nat.is_eq(v(al), v(bl)), U32.is_eq(ah, bh)), Bool.and(Nat.is_eq(v(al), v(bl)), Nat.is_eq(v(ah), v(bh))), Equal.cong(Bool, Bool, t => Bool.and(t, U32.is_eq(ah, bh)), U32.is_eq(al, bl), Nat.is_eq(v(al), v(bl)), LW.eq_nat(al, bl)), Equal.cong(Bool, Bool, t => Bool.and(Nat.is_eq(v(al), v(bl)), t), U32.is_eq(ah, bh), Nat.is_eq(v(ah), v(bh)), LW.eq_nat(ah, bh)))
      Equal.trans(Bool, Bool.and(U32.is_eq(al, bl), U32.is_eq(ah, bh)), Bool.and(Nat.is_eq(v(al), v(bl)), Nat.is_eq(v(ah), v(bh))), Nat.is_eq(val(al, ah), val(bl, bh)), e1, WW.eq_limbs(32n, v(al), v(ah), v(bl), v(bh), vb(al), vb(bl)))

def lt_value(+a: WU.U64, +b: WU.U64) -> SW.Lt.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +x = Bool.or(U32.is_lt(ah, bh), Bool.and(U32.is_eq(ah, bh), U32.is_lt(al, bl)))
      +y1 = Bool.or(Nat.is_lt(v(ah), v(bh)), Bool.and(U32.is_eq(ah, bh), U32.is_lt(al, bl)))
      +y2 = Bool.or(Nat.is_lt(v(ah), v(bh)), Bool.and(Nat.is_eq(v(ah), v(bh)), U32.is_lt(al, bl)))
      +y3 = Bool.or(Nat.is_lt(v(ah), v(bh)), Bool.and(Nat.is_eq(v(ah), v(bh)), Nat.is_lt(v(al), v(bl))))
      +e1 = Equal.cong(Bool, Bool, t => Bool.or(t, Bool.and(U32.is_eq(ah, bh), U32.is_lt(al, bl))), U32.is_lt(ah, bh), Nat.is_lt(v(ah), v(bh)), U3.is_lt_nat(ah, bh))
      +e2 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(v(ah), v(bh)), Bool.and(t, U32.is_lt(al, bl))), U32.is_eq(ah, bh), Nat.is_eq(v(ah), v(bh)), LW.eq_nat(ah, bh))
      +e3 = Equal.cong(Bool, Bool, t => Bool.or(Nat.is_lt(v(ah), v(bh)), Bool.and(Nat.is_eq(v(ah), v(bh)), t)), U32.is_lt(al, bl), Nat.is_lt(v(al), v(bl)), U3.is_lt_nat(al, bl))
      Equal.trans(Bool, x, y1, Nat.is_lt(val(al, ah), val(bl, bh)), e1, Equal.trans(Bool, y1, y2, Nat.is_lt(val(al, ah), val(bl, bh)), e2, Equal.trans(Bool, y2, y3, Nat.is_lt(val(al, ah), val(bl, bh)), e3, WW.lt_limbs(32n, v(al), v(ah), v(bl), v(bh), vb(al), vb(bl)))))

def nle(+a: Nat, +b: Nat, +c: Bool, +hc: {Nat.is_lt(a, b) == c : Bool}) -> {Bool.not(c) == Nat.is_le(b, a) : Bool}:
  match c:
    case True{}:
      Equal.sym(Bool, Nat.is_le(b, a), False{}, N.lt_not_le(a, b, hc))
    case False{}:
      Equal.sym(Bool, Nat.is_le(b, a), True{}, N.not_lt_le(a, b, hc))

def le_value(+a: WU.U64, +b: WU.U64) -> SW.Le.value(a, b):
  Equal.trans(Bool, Bool.not(X.lt(b, a)), Bool.not(Nat.is_lt(SW.value(b), SW.value(a))), Nat.is_le(SW.value(a), SW.value(b)), Equal.cong(Bool, Bool, t => Bool.not(t), X.lt(b, a), Nat.is_lt(SW.value(b), SW.value(a)), lt_value(b, a)), nle(SW.value(b), SW.value(a), Nat.is_lt(SW.value(b), SW.value(a)), {==}))

def odd_value(+a: WU.U64) -> SW.Odd.value(a):
  match a:
    case WU.U64{+l, +h}:
      Equal.trans(Bool, U32.is_eq(U32.and(l, 1), 1), Nat.is_eq(Nat.mod(v(l), 2n), 1n), Nat.is_eq(Nat.mod(val(l, h), 2n), 1n), LW.tests_odd(l), Equal.cong(Nat, Bool, t => Nat.is_eq(t, 1n), Nat.mod(v(l), 2n), Nat.mod(val(l, h), 2n), Equal.sym(Nat, Nat.mod(val(l, h), 2n), Nat.mod(v(l), 2n), WW.odd_limb(31n, v(l), v(h)))))

# ---- half ----

def chh(+n: Nat) -> {C.half(n) == UH.hlf(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+ +q:
      Equal.cong(Nat, Nat, t => 1n+t, C.half(q), UH.hlf(q), chh(q))

def half_div(+n: Nat) -> {C.half(n) == Nat.div(n, 2n) : Nat}:
  Equal.trans(Nat, C.half(n), UH.hlf(n), Nat.div(n, 2n), chh(n), LW.hlf_div2(n))

# a sum that fits 32 bits: no wrap
def add_exact(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +hf: {C.fits(32n, Nat.add(v(x), v(y))) == True{} : Bool}) -> {v(U32.add(x, y)) == Nat.add(v(x), v(y)) : Nat}:
  +cc = P64.carry32(x, y)
  +e = acons_o(one, h1, x, y)
  +nc = no_carry(one, h1, v(U32.add(x, y)), cc, Nat.add(v(x), v(y)), e, hf)
  +e0 = L.subst(Bool, t => {Nat.add(v(U32.add(x, y)), C.shift(32n, WD.bo(t, one))) == Nat.add(v(x), v(y)) : Nat}, cc, False{}, nc, e)
  Equal.trans(Nat, v(U32.add(x, y)), Nat.add(v(U32.add(x, y)), C.shift(32n, 0n)), Nat.add(v(x), v(y)), Equal.sym(Nat, Nat.add(v(U32.add(x, y)), C.shift(32n, 0n)), v(U32.add(x, y)), Equal.trans(Nat, Nat.add(v(U32.add(x, y)), C.shift(32n, 0n)), Nat.add(v(U32.add(x, y)), 0n), v(U32.add(x, y)), Equal.cong(Nat, Nat, t => Nat.add(v(U32.add(x, y)), t), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(U32.add(x, y))))), e0)

def mul_le1(+b: Nat, +x: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.is_le(Nat.mul(b, x), x) == True{} : Bool}:
  match b:
    case 0n:
      N.zero_le(x)
    case 1n:
      L.subst(Nat, z => {Nat.is_le(z, x) == True{} : Bool}, x, Nat.add(x, 0n), Equal.sym(Nat, Nat.add(x, 0n), x, N.add_zero(x)), N.le_refl(x))
    case 2n+c:
      Empty.absurd({Nat.is_le(Nat.mul(2n+c, x), x) == True{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, hb)))

def half_g(+l: U32, +h: U32, +c: U32) -> WU.U64:
  WU.U64{U32.add(U32.shr(l), U32.mul(U32.and(h, 1), c)), U32.shr(h)}

def halfval(+one: Nat, +h1: {one == 1n : Nat}, +l: U32, +h: U32, +c: U32, +pc: {c == U32{WD.pw(32n, 31n)} : U32}) -> {SW.value(half_g(l, h, c)) == Nat.div(val(l, h), 2n) : Nat}:
  +b = U32.and(h, 1)
  +s31 = C.shift(31n, one)
  +bt = C.bit(v(h))
  +evb = Equal.trans(Nat, v(b), Nat.mod(v(h), 2n), bt, LW.odd_val(h), Equal.sym(Nat, bt, Nat.mod(v(h), 2n), WW.bit_mod(v(h))))
  +evc = Equal.trans(Nat, v(c), WD.sc(31n, one), s31, PD.pow32(31n, {==}, one, h1, c, pc), Equal.sym(Nat, s31, WD.sc(31n, one), W64M.shift_sc(31n, one)))
  +hb1 = WW.bit_le1(v(h))
  +epr = Equal.trans(Nat, Nat.mul(v(b), v(c)), Nat.mul(bt, v(c)), Nat.mul(bt, s31), Equal.cong(Nat, Nat, t => Nat.mul(t, v(c)), v(b), bt, evb), Equal.cong(Nat, Nat, t => Nat.mul(bt, t), v(c), s31, evc))
  +hs1 = L.subst(Nat, z => {Nat.is_le(z, s31) == True{} : Bool}, one, 1n, h1, WW.shift_ge(31n, one))
  +hsd = N.succ_le_lt(s31, Nat.double(s31), N.double_succ_le(s31, hs1))
  +hple = L.subst(Nat, z => {Nat.is_le(z, s31) == True{} : Bool}, Nat.mul(bt, s31), Nat.mul(v(b), v(c)), Equal.sym(Nat, Nat.mul(v(b), v(c)), Nat.mul(bt, s31), epr), mul_le1(bt, s31, hb1))
  +hplt = L.subst(Nat, z => {Nat.is_lt(Nat.mul(v(b), v(c)), z) == True{} : Bool}, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one), N.le_lt_trans(Nat.mul(v(b), v(c)), s31, Nat.double(s31), hple, hsd))
  +m = U32.mul(b, c)
  +evm = Equal.trans(Nat, v(m), Nat.mul(v(b), v(c)), Nat.mul(bt, s31), PD.mul32(one, h1, b, c, hplt), epr)
  +hl = C.half(v(l))
  +evs = Equal.trans(Nat, v(U32.shr(l)), Nat.div(v(l), 2n), hl, LW.ops_half(l), Equal.sym(Nat, hl, Nat.div(v(l), 2n), half_div(v(l))))
  +hlt = Equal.trans(Bool, Nat.is_lt(hl, s31), Nat.is_lt(v(l), Nat.double(s31)), True{}, WW.lt_half(v(l), s31), WW.lt_one(32n, one, h1, v(l), vb(l)))
  +hsum = N.lt_le_trans(Nat.add(hl, Nat.mul(bt, s31)), Nat.add(s31, Nat.mul(bt, s31)), Nat.double(s31), N.lt_add_r2(hl, s31, Nat.mul(bt, s31), hlt), L.subst(Nat, z => {Nat.is_le(Nat.add(s31, Nat.mul(bt, s31)), z) == True{} : Bool}, Nat.add(s31, s31), Nat.double(s31), Equal.sym(Nat, Nat.double(s31), Nat.add(s31, s31), NA.double_self(s31)), N.le_add_left(Nat.mul(bt, s31), s31, s31, mul_le1(bt, s31, hb1))))
  +es = Equal.trans(Nat, Nat.add(v(U32.shr(l)), v(m)), Nat.add(hl, v(m)), Nat.add(hl, Nat.mul(bt, s31)), Equal.cong(Nat, Nat, t => Nat.add(t, v(m)), v(U32.shr(l)), hl, evs), Equal.cong(Nat, Nat, t => Nat.add(hl, t), v(m), Nat.mul(bt, s31), evm))
  +hfit = WW.fits_one(32n, one, h1, Nat.add(v(U32.shr(l)), v(m)), L.subst(Nat, z => {Nat.is_lt(z, C.shift(32n, one)) == True{} : Bool}, Nat.add(hl, Nat.mul(bt, s31)), Nat.add(v(U32.shr(l)), v(m)), Equal.sym(Nat, Nat.add(v(U32.shr(l)), v(m)), Nat.add(hl, Nat.mul(bt, s31)), es), hsum))
  +elo = Equal.trans(Nat, v(U32.add(U32.shr(l), m)), Nat.add(v(U32.shr(l)), v(m)), Nat.add(hl, Nat.mul(bt, s31)), add_exact(one, h1, U32.shr(l), m, hfit), es)
  +ehi = Equal.trans(Nat, v(U32.shr(h)), Nat.div(v(h), 2n), C.half(v(h)), LW.ops_half(h), Equal.sym(Nat, C.half(v(h)), Nat.div(v(h), 2n), half_div(v(h))))
  +ev = Equal.trans(Nat, Nat.add(v(U32.add(U32.shr(l), m)), C.shift(32n, v(U32.shr(h)))), Nat.add(Nat.add(hl, Nat.mul(bt, s31)), C.shift(32n, v(U32.shr(h)))), Nat.add(Nat.add(hl, Nat.mul(bt, s31)), C.shift(32n, C.half(v(h)))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(32n, v(U32.shr(h)))), v(U32.add(U32.shr(l), m)), Nat.add(hl, Nat.mul(bt, s31)), elo), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(hl, Nat.mul(bt, s31)), C.shift(32n, t)), v(U32.shr(h)), C.half(v(h)), ehi))
  +eh = WW.half_limbs(31n, one, h1, v(l), v(h))
  Equal.trans(Nat, Nat.add(v(U32.add(U32.shr(l), m)), C.shift(32n, v(U32.shr(h)))), C.half(val(l, h)), Nat.div(val(l, h), 2n), Equal.trans(Nat, Nat.add(v(U32.add(U32.shr(l), m)), C.shift(32n, v(U32.shr(h)))), Nat.add(Nat.add(hl, Nat.mul(bt, s31)), C.shift(32n, C.half(v(h)))), C.half(val(l, h)), ev, Equal.sym(Nat, C.half(val(l, h)), Nat.add(Nat.add(hl, Nat.mul(bt, s31)), C.shift(32n, C.half(v(h)))), eh)), half_div(val(l, h)))

def half_value(+a: WU.U64) -> SW.Half.value(a):
  match a:
    case WU.U64{+l, +h}:
      halfval(1n, {==}, l, h, 2147483648, {==})

# ---- sub ----

# x - y mod 2^32, plus y, is x plus 2^32 when x < y
def borrow_eq(+one: Nat, +h1: {one == 1n : Nat}, +vx: Nat, +vs: Nat, +vy: Nat, +cc: Bool, +e: {Nat.add(vx, C.shift(32n, WD.bo(cc, one))) == Nat.add(vs, vy) : Nat}, +hs: {C.fits(32n, vs) == True{} : Bool}) -> {cc == Nat.is_lt(vx, vy) : Bool}:
  match cc:
    case True{}:
      +h1s = WW.lt_one(32n, one, h1, vs, hs)
      +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.add(vs, vy), z) == True{} : Bool}, Nat.add(C.shift(32n, one), vy), Nat.add(vy, C.shift(32n, one)), N.add_comm(C.shift(32n, one), vy), N.lt_add_r2(vs, C.shift(32n, one), vy, h1s))
      +h3 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(vy, C.shift(32n, one))) == True{} : Bool}, Nat.add(vs, vy), Nat.add(vx, C.shift(32n, one)), Equal.sym(Nat, Nat.add(vx, C.shift(32n, one)), Nat.add(vs, vy), e), h2)
      Equal.sym(Bool, Nat.is_lt(vx, vy), True{}, Equal.trans(Bool, Nat.is_lt(vx, vy), Nat.is_lt(Nat.add(vx, C.shift(32n, one)), Nat.add(vy, C.shift(32n, one))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(vx, C.shift(32n, one)), Nat.add(vy, C.shift(32n, one))), Nat.is_lt(vx, vy), WW.lt_cancel_r(vx, vy, C.shift(32n, one))), h3))
    case False{}:
      +e0 = Equal.trans(Nat, vx, Nat.add(vx, C.shift(32n, 0n)), Nat.add(vs, vy), Equal.sym(Nat, Nat.add(vx, C.shift(32n, 0n)), vx, Equal.trans(Nat, Nat.add(vx, C.shift(32n, 0n)), Nat.add(vx, 0n), vx, Equal.cong(Nat, Nat, t => Nat.add(vx, t), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(vx))), e)
      +hle = L.subst(Nat, z => {Nat.is_le(vy, z) == True{} : Bool}, Nat.add(vy, vs), vx, Equal.trans(Nat, Nat.add(vy, vs), Nat.add(vs, vy), vx, N.add_comm(vy, vs), Equal.sym(Nat, vx, Nat.add(vs, vy), e0)), N.le_add_right(vy, vs))
      Equal.sym(Bool, Nat.is_lt(vx, vy), False{}, N.le_not_lt(vx, vy, hle))

def sub_cons(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32) -> {Nat.add(v(U32.sub(x, y)), v(y)) == Nat.add(v(x), C.shift(32n, WD.bo(U32.is_lt(x, y), one))) : Nat}:
  +d = U32.sub(x, y)
  +cc = P64.carry32(d, y)
  +e0 = acons_o(one, h1, d, y)
  +e1 = L.subst(U32, z => {Nat.add(v(z), C.shift(32n, WD.bo(cc, one))) == Nat.add(v(d), v(y)) : Nat}, U32.add(d, y), x, A.sub_add(x, y), e0)
  +ec = Equal.trans(Bool, cc, Nat.is_lt(v(x), v(y)), U32.is_lt(x, y), borrow_eq(one, h1, v(x), v(d), v(y), cc, e1, vb(d)), Equal.sym(Bool, U32.is_lt(x, y), Nat.is_lt(v(x), v(y)), U3.is_lt_nat(x, y)))
  +e2 = L.subst(Bool, t => {Nat.add(v(x), C.shift(32n, WD.bo(t, one))) == Nat.add(v(d), v(y)) : Nat}, cc, U32.is_lt(x, y), ec, e1)
  Equal.sym(Nat, Nat.add(v(x), C.shift(32n, WD.bo(U32.is_lt(x, y), one))), Nat.add(v(d), v(y)), e2)

def sub_alg(+lo: Nat, +hi: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +s: Nat, +b1: Nat, +b2: Nat, +b3: Nat, +e1: {Nat.add(lo, bl) == Nat.add(al, C.shift(32n, b1)) : Nat}, +e2: {Nat.add(s, bh) == Nat.add(ah, C.shift(32n, b2)) : Nat}, +e3: {Nat.add(hi, b1) == Nat.add(s, C.shift(32n, b3)) : Nat}) -> {Nat.add(Nat.add(lo, C.shift(32n, hi)), Nat.add(bl, C.shift(32n, bh))) == Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(lo, C.shift(32n, hi)), Nat.add(bl, C.shift(32n, bh))), Nat.add(Nat.add(lo, bl), Nat.add(C.shift(32n, hi), C.shift(32n, bh))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), W64M.add4(lo, C.shift(32n, hi), bl, C.shift(32n, bh)), Equal.trans(Nat, Nat.add(Nat.add(lo, bl), Nat.add(C.shift(32n, hi), C.shift(32n, bh))), Nat.add(Nat.add(lo, bl), C.shift(32n, Nat.add(hi, bh))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Equal.cong(Nat, Nat, t => Nat.add(Nat.add(lo, bl), t), Nat.add(C.shift(32n, hi), C.shift(32n, bh)), C.shift(32n, Nat.add(hi, bh)), Equal.sym(Nat, C.shift(32n, Nat.add(hi, bh)), Nat.add(C.shift(32n, hi), C.shift(32n, bh)), WW.shift_add(32n, hi, bh))), Equal.trans(Nat, Nat.add(Nat.add(lo, bl), C.shift(32n, Nat.add(hi, bh))), Nat.add(Nat.add(al, C.shift(32n, b1)), C.shift(32n, Nat.add(hi, bh))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(32n, Nat.add(hi, bh))), Nat.add(lo, bl), Nat.add(al, C.shift(32n, b1)), e1), Equal.trans(Nat, Nat.add(Nat.add(al, C.shift(32n, b1)), C.shift(32n, Nat.add(hi, bh))), Nat.add(al, Nat.add(C.shift(32n, b1), C.shift(32n, Nat.add(hi, bh)))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), NA.add_assoc(al, C.shift(32n, b1), C.shift(32n, Nat.add(hi, bh))), Equal.trans(Nat, Nat.add(al, Nat.add(C.shift(32n, b1), C.shift(32n, Nat.add(hi, bh)))), Nat.add(al, C.shift(32n, Nat.add(b1, Nat.add(hi, bh)))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Equal.cong(Nat, Nat, t => Nat.add(al, t), Nat.add(C.shift(32n, b1), C.shift(32n, Nat.add(hi, bh))), C.shift(32n, Nat.add(b1, Nat.add(hi, bh))), Equal.sym(Nat, C.shift(32n, Nat.add(b1, Nat.add(hi, bh))), Nat.add(C.shift(32n, b1), C.shift(32n, Nat.add(hi, bh))), WW.shift_add(32n, b1, Nat.add(hi, bh)))), Equal.trans(Nat, Nat.add(al, C.shift(32n, Nat.add(b1, Nat.add(hi, bh)))), Nat.add(al, C.shift(32n, Nat.add(ah, C.shift(32n, Nat.add(b2, b3))))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Equal.cong(Nat, Nat, t => Nat.add(al, C.shift(32n, t)), Nat.add(b1, Nat.add(hi, bh)), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.trans(Nat, Nat.add(b1, Nat.add(hi, bh)), Nat.add(hi, Nat.add(b1, bh)), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), NA.add_swap(b1, hi, bh), Equal.trans(Nat, Nat.add(hi, Nat.add(b1, bh)), Nat.add(Nat.add(hi, b1), bh), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.sym(Nat, Nat.add(Nat.add(hi, b1), bh), Nat.add(hi, Nat.add(b1, bh)), NA.add_assoc(hi, b1, bh)), Equal.trans(Nat, Nat.add(Nat.add(hi, b1), bh), Nat.add(Nat.add(s, C.shift(32n, b3)), bh), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.cong(Nat, Nat, t => Nat.add(t, bh), Nat.add(hi, b1), Nat.add(s, C.shift(32n, b3)), e3), Equal.trans(Nat, Nat.add(Nat.add(s, C.shift(32n, b3)), bh), Nat.add(s, Nat.add(C.shift(32n, b3), bh)), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), NA.add_assoc(s, C.shift(32n, b3), bh), Equal.trans(Nat, Nat.add(s, Nat.add(C.shift(32n, b3), bh)), Nat.add(s, Nat.add(bh, C.shift(32n, b3))), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.cong(Nat, Nat, t => Nat.add(s, t), Nat.add(C.shift(32n, b3), bh), Nat.add(bh, C.shift(32n, b3)), N.add_comm(C.shift(32n, b3), bh)), Equal.trans(Nat, Nat.add(s, Nat.add(bh, C.shift(32n, b3))), Nat.add(Nat.add(s, bh), C.shift(32n, b3)), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.sym(Nat, Nat.add(Nat.add(s, bh), C.shift(32n, b3)), Nat.add(s, Nat.add(bh, C.shift(32n, b3))), NA.add_assoc(s, bh, C.shift(32n, b3))), Equal.trans(Nat, Nat.add(Nat.add(s, bh), C.shift(32n, b3)), Nat.add(Nat.add(ah, C.shift(32n, b2)), C.shift(32n, b3)), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), Equal.cong(Nat, Nat, t => Nat.add(t, C.shift(32n, b3)), Nat.add(s, bh), Nat.add(ah, C.shift(32n, b2)), e2), Equal.trans(Nat, Nat.add(Nat.add(ah, C.shift(32n, b2)), C.shift(32n, b3)), Nat.add(ah, Nat.add(C.shift(32n, b2), C.shift(32n, b3))), Nat.add(ah, C.shift(32n, Nat.add(b2, b3))), NA.add_assoc(ah, C.shift(32n, b2), C.shift(32n, b3)), Equal.cong(Nat, Nat, t => Nat.add(ah, t), Nat.add(C.shift(32n, b2), C.shift(32n, b3)), C.shift(32n, Nat.add(b2, b3)), Equal.sym(Nat, C.shift(32n, Nat.add(b2, b3)), Nat.add(C.shift(32n, b2), C.shift(32n, b3)), WW.shift_add(32n, b2, b3)))))))))))), Equal.trans(Nat, Nat.add(al, C.shift(32n, Nat.add(ah, C.shift(32n, Nat.add(b2, b3))))), Nat.add(al, Nat.add(C.shift(32n, ah), C.shift(32n, C.shift(32n, Nat.add(b2, b3))))), Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Equal.cong(Nat, Nat, t => Nat.add(al, t), C.shift(32n, Nat.add(ah, C.shift(32n, Nat.add(b2, b3)))), Nat.add(C.shift(32n, ah), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), WW.shift_add(32n, ah, C.shift(32n, Nat.add(b2, b3)))), Equal.sym(Nat, Nat.add(Nat.add(al, C.shift(32n, ah)), C.shift(32n, C.shift(32n, Nat.add(b2, b3)))), Nat.add(al, Nat.add(C.shift(32n, ah), C.shift(32n, C.shift(32n, Nat.add(b2, b3))))), NA.add_assoc(al, C.shift(32n, ah), C.shift(32n, C.shift(32n, Nat.add(b2, b3))))))))))))

def sub_fin(+vs: Nat, +d: Nat, +q: Nat, +e: {vs == Nat.add(d, C.shift(64n, q)) : Nat}, +hf: {C.fits(64n, vs) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(q, 0n) == c : Bool}) -> {vs == d : Nat}:
  match c:
    case True{}:
      +eq = N.eq_from_is_eq(q, 0n, hc)
      Equal.trans(Nat, vs, Nat.add(d, C.shift(64n, q)), d, e, Equal.trans(Nat, Nat.add(d, C.shift(64n, q)), Nat.add(d, 0n), d, Equal.cong(Nat, Nat, t => Nat.add(d, t), C.shift(64n, q), 0n, Equal.trans(Nat, C.shift(64n, q), C.shift(64n, 0n), 0n, Equal.cong(Nat, Nat, t => C.shift(64n, t), q, 0n, eq), WW.shift_zero(64n))), N.add_zero(d)))
    case False{}:
      Empty.absurd({vs == d : Nat}, true_ne_false(Equal.trans(Bool, True{}, C.fits(64n, vs), False{}, Equal.sym(Bool, C.fits(64n, vs), True{}, hf), Equal.trans(Bool, C.fits(64n, vs), C.fits(64n, Nat.add(d, C.shift(64n, q))), False{}, Equal.cong(Nat, Bool, t => C.fits(64n, t), vs, Nat.add(d, C.shift(64n, q)), e), WW.unfit_nz(64n, d, q, hc)))))

def subval(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +hle: {Nat.is_le(val(bl, bh), val(al, ah)) == True{} : Bool}) -> {SW.value(X.sub(WU.U64{al, ah}, WU.U64{bl, bh})) == Nat.sub(val(al, ah), val(bl, bh)) : Nat}:
  +lo = U32.sub(al, bl)
  +c1 = U32.is_lt(al, bl)
  +s = U32.sub(ah, bh)
  +cb = X.b32(c1)
  +hi = U32.sub(s, cb)
  +b1 = WD.bo(c1, one)
  +b2 = WD.bo(U32.is_lt(ah, bh), one)
  +b3 = WD.bo(U32.is_lt(s, cb), one)
  +ecb = Equal.trans(Nat, v(cb), S.bit_value(c1), b1, W64M.b32_v(c1), Equal.sym(Nat, b1, S.bit_value(c1), WD.bo_bit(c1, one, h1)))
  +e3 = Equal.trans(Nat, Nat.add(v(hi), b1), Nat.add(v(hi), v(cb)), Nat.add(v(s), C.shift(32n, b3)), Equal.cong(Nat, Nat, t => Nat.add(v(hi), t), b1, v(cb), Equal.sym(Nat, v(cb), b1, ecb)), sub_cons(one, h1, s, cb))
  +eq = sub_alg(v(lo), v(hi), v(al), v(ah), v(bl), v(bh), v(s), b1, b2, b3, sub_cons(one, h1, al, bl), sub_cons(one, h1, ah, bh), e3)
  +q = Nat.add(b2, b3)
  +va = val(al, ah)
  +vbb = val(bl, bh)
  +vs = val(lo, hi)
  +T = C.shift(64n, q)
  +eq2 = Equal.trans(Nat, Nat.add(vs, vbb), Nat.add(va, C.shift(32n, C.shift(32n, q))), Nat.add(va, T), eq, Equal.cong(Nat, Nat, t => Nat.add(va, t), C.shift(32n, C.shift(32n, q)), T, Equal.sym(Nat, T, C.shift(32n, C.shift(32n, q)), WW.shift_comp(32n, 32n, q))))
  +dd = Nat.sub(va, vbb)
  +ea = Equal.sym(Nat, Nat.add(vbb, dd), va, N.sub_add(va, vbb, hle))
  +e4 = Equal.trans(Nat, Nat.add(vbb, vs), Nat.add(vs, vbb), Nat.add(vbb, Nat.add(dd, T)), N.add_comm(vbb, vs), Equal.trans(Nat, Nat.add(vs, vbb), Nat.add(va, T), Nat.add(vbb, Nat.add(dd, T)), eq2, Equal.trans(Nat, Nat.add(va, T), Nat.add(Nat.add(vbb, dd), T), Nat.add(vbb, Nat.add(dd, T)), Equal.cong(Nat, Nat, t => Nat.add(t, T), va, Nat.add(vbb, dd), ea), NA.add_assoc(vbb, dd, T))))
  +e5 = NR.add_cancel(vbb, vs, Nat.add(dd, T), e4)
  +hf = WW.limbs_fit(32n, 32n, v(lo), v(hi), vb(lo), vb(hi))
  sub_fin(vs, dd, q, e5, hf, Nat.is_eq(q, 0n), {==})

def sub_value(+a: WU.U64, +b: WU.U64, +h: {Nat.is_le(SW.value(b), SW.value(a)) == True{} : Bool}) -> SW.Sub.value(a, b, h):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      subval(1n, {==}, al, ah, bl, bh, h)

# ---- mul ----

def mcons(+x: U32, +y: U32) -> {Nat.add(v(U32.mul(x, y)), C.shift(32n, W64M.mex(x, y))) == Nat.mul(v(x), v(y)) : Nat}:
  Equal.trans(Nat, Nat.add(v(U32.mul(x, y)), C.shift(32n, W64M.mex(x, y))), Nat.add(v(U32.mul(x, y)), WD.sc(32n, W64M.mex(x, y))), Nat.mul(v(x), v(y)), Equal.cong(Nat, Nat, z => Nat.add(v(U32.mul(x, y)), z), C.shift(32n, W64M.mex(x, y)), WD.sc(32n, W64M.mex(x, y)), W64M.shift_sc(32n, W64M.mex(x, y))), W64M.mul_cons(x, y))

# the cross terms: al bh + ah bl == t + 2^32 kc, t their wrapped sum
def cross_eq(+al: U32, +ah: U32, +bl: U32, +bh: U32) -> {Nat.add(v(U32.add(U32.mul(al, bh), U32.mul(ah, bl))), C.shift(32n, Nat.add(bv(P64.carry32(U32.mul(al, bh), U32.mul(ah, bl))), Nat.add(W64M.mex(al, bh), W64M.mex(ah, bl))))) == Nat.add(Nat.mul(v(al), v(bh)), Nat.mul(v(ah), v(bl))) : Nat}:
  +m1 = U32.mul(al, bh)
  +m2 = U32.mul(ah, bl)
  +t = U32.add(m1, m2)
  +c = P64.carry32(m1, m2)
  +x1 = W64M.mex(al, bh)
  +x2 = W64M.mex(ah, bl)
  +e1 = mcons(al, bh)
  +e2 = mcons(ah, bl)
  +et = acons(m1, m2)
  Equal.sym(Nat, Nat.add(Nat.mul(v(al), v(bh)), Nat.mul(v(ah), v(bl))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), Equal.trans(Nat, Nat.add(Nat.mul(v(al), v(bh)), Nat.mul(v(ah), v(bl))), Nat.add(Nat.add(v(m1), C.shift(32n, x1)), Nat.add(v(m2), C.shift(32n, x2))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), Equal.trans(Nat, Nat.add(Nat.mul(v(al), v(bh)), Nat.mul(v(ah), v(bl))), Nat.add(Nat.add(v(m1), C.shift(32n, x1)), Nat.mul(v(ah), v(bl))), Nat.add(Nat.add(v(m1), C.shift(32n, x1)), Nat.add(v(m2), C.shift(32n, x2))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(v(ah), v(bl))), Nat.mul(v(al), v(bh)), Nat.add(v(m1), C.shift(32n, x1)), Equal.sym(Nat, Nat.add(v(m1), C.shift(32n, x1)), Nat.mul(v(al), v(bh)), e1)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(m1), C.shift(32n, x1)), z), Nat.mul(v(ah), v(bl)), Nat.add(v(m2), C.shift(32n, x2)), Equal.sym(Nat, Nat.add(v(m2), C.shift(32n, x2)), Nat.mul(v(ah), v(bl)), e2))), Equal.trans(Nat, Nat.add(Nat.add(v(m1), C.shift(32n, x1)), Nat.add(v(m2), C.shift(32n, x2))), Nat.add(Nat.add(v(m1), v(m2)), Nat.add(C.shift(32n, x1), C.shift(32n, x2))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), W64M.add4(v(m1), C.shift(32n, x1), v(m2), C.shift(32n, x2)), Equal.trans(Nat, Nat.add(Nat.add(v(m1), v(m2)), Nat.add(C.shift(32n, x1), C.shift(32n, x2))), Nat.add(Nat.add(v(t), C.shift(32n, bv(c))), Nat.add(C.shift(32n, x1), C.shift(32n, x2))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(C.shift(32n, x1), C.shift(32n, x2))), Nat.add(v(m1), v(m2)), Nat.add(v(t), C.shift(32n, bv(c))), Equal.sym(Nat, Nat.add(v(t), C.shift(32n, bv(c))), Nat.add(v(m1), v(m2)), et)), Equal.trans(Nat, Nat.add(Nat.add(v(t), C.shift(32n, bv(c))), Nat.add(C.shift(32n, x1), C.shift(32n, x2))), Nat.add(Nat.add(v(t), C.shift(32n, bv(c))), C.shift(32n, Nat.add(x1, x2))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(t), C.shift(32n, bv(c))), z), Nat.add(C.shift(32n, x1), C.shift(32n, x2)), C.shift(32n, Nat.add(x1, x2)), Equal.sym(Nat, C.shift(32n, Nat.add(x1, x2)), Nat.add(C.shift(32n, x1), C.shift(32n, x2)), WW.shift_add(32n, x1, x2))), Equal.trans(Nat, Nat.add(Nat.add(v(t), C.shift(32n, bv(c))), C.shift(32n, Nat.add(x1, x2))), Nat.add(v(t), Nat.add(C.shift(32n, bv(c)), C.shift(32n, Nat.add(x1, x2)))), Nat.add(v(t), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2)))), NA.add_assoc(v(t), C.shift(32n, bv(c)), C.shift(32n, Nat.add(x1, x2))), Equal.cong(Nat, Nat, z => Nat.add(v(t), z), Nat.add(C.shift(32n, bv(c)), C.shift(32n, Nat.add(x1, x2))), C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2))), Equal.sym(Nat, C.shift(32n, Nat.add(bv(c), Nat.add(x1, x2))), Nat.add(C.shift(32n, bv(c)), C.shift(32n, Nat.add(x1, x2))), WW.shift_add(32n, bv(c), Nat.add(x1, x2))))))))))

def mul_value(+a: WU.U64, +b: WU.U64) -> SW.Mul.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      +m1 = U32.mul(al, bh)
      +m2 = U32.mul(ah, bl)
      +t = U32.add(m1, m2)
      +kc = Nat.add(bv(P64.carry32(m1, m2)), Nat.add(W64M.mex(al, bh), W64M.mex(ah, bl)))
      +A = Nat.mul(v(al), v(bl))
      +H = Nat.mul(v(ah), v(bh))
      +mk = WW.mul_k(32n, v(al), v(ah), v(bl), v(bh), v(t), kc, cross_eq(al, ah, bl, bh))
      +Y = Nat.add(kc, H)
      +p = X.mul32(al, bl)
      +q = {WU.U64{0, t} : WU.U64}
      av = add_value(p, q)
      +elp = Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, C.shift(32n, v(t)))), SW.value(p), A, W64M.mul32_value(al, bl))
      +em = Equal.trans(Nat, Nat.mul(val(al, ah), val(bl, bh)), Nat.add(Nat.add(A, C.shift(32n, v(t))), C.shift(32n, C.shift(32n, Y))), Nat.add(Nat.add(A, C.shift(32n, v(t))), C.shift(64n, Y)), mk, Equal.cong(Nat, Nat, z => Nat.add(Nat.add(A, C.shift(32n, v(t))), z), C.shift(32n, C.shift(32n, Y)), C.shift(64n, Y), Equal.sym(Nat, C.shift(64n, Y), C.shift(32n, C.shift(32n, Y)), WW.shift_comp(32n, 32n, Y))))
      +elm = Equal.trans(Nat, C.low(64n, Nat.mul(val(al, ah), val(bl, bh))), C.low(64n, Nat.add(Nat.add(A, C.shift(32n, v(t))), C.shift(64n, Y))), C.low(64n, Nat.add(A, C.shift(32n, v(t)))), Equal.cong(Nat, Nat, z => C.low(64n, z), Nat.mul(val(al, ah), val(bl, bh)), Nat.add(Nat.add(A, C.shift(32n, v(t))), C.shift(64n, Y)), em), WW.low_add_shift(64n, Nat.add(A, C.shift(32n, v(t))), Y))
      Equal.trans(Nat, SW.value(X.add(p, q)), C.low(64n, Nat.add(SW.value(p), C.shift(32n, v(t)))), C.low(64n, Nat.mul(val(al, ah), val(bl, bh))), av, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(p), C.shift(32n, v(t)))), C.low(64n, Nat.add(A, C.shift(32n, v(t)))), C.low(64n, Nat.mul(val(al, ah), val(bl, bh))), elp, Equal.sym(Nat, C.low(64n, Nat.mul(val(al, ah), val(bl, bh))), C.low(64n, Nat.add(A, C.shift(32n, v(t)))), elm)))

# ---- mul_over ----

def mo_alg(+k: Nat, +A: Nat, +t1: Nat, +t2: Nat, +hh: Nat, +pl: Nat, +ph: Nat, +cl: Nat, +ch: Nat, +s: Nat, +cr: Nat, +ea: {A == Nat.add(pl, C.shift(k, ph)) : Nat}, +ec: {Nat.add(t2, t1) == Nat.add(cl, C.shift(k, ch)) : Nat}, +es: {Nat.add(s, C.shift(k, cr)) == Nat.add(ph, cl) : Nat}, +eh: {hh == 0n : Nat}) -> {Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), C.shift(k, C.shift(k, hh)))) == Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), C.shift(k, C.shift(k, hh)))), Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), C.shift(k, C.shift(k, 0n)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), C.shift(k, C.shift(k, z)))), hh, 0n, eh), Equal.trans(Nat, Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), C.shift(k, C.shift(k, 0n)))), Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), 0n)), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), z)), C.shift(k, C.shift(k, 0n)), 0n, Equal.trans(Nat, C.shift(k, C.shift(k, 0n)), C.shift(k, 0n), 0n, Equal.cong(Nat, Nat, z => C.shift(k, z), C.shift(k, 0n), 0n, WW.shift_zero(k)), WW.shift_zero(k))), Equal.trans(Nat, Nat.add(Nat.add(A, C.shift(k, t1)), Nat.add(C.shift(k, t2), 0n)), Nat.add(Nat.add(A, C.shift(k, t1)), C.shift(k, t2)), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(A, C.shift(k, t1)), z), Nat.add(C.shift(k, t2), 0n), C.shift(k, t2), N.add_zero(C.shift(k, t2))), Equal.trans(Nat, Nat.add(Nat.add(A, C.shift(k, t1)), C.shift(k, t2)), Nat.add(A, Nat.add(C.shift(k, t1), C.shift(k, t2))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), NA.add_assoc(A, C.shift(k, t1), C.shift(k, t2)), Equal.trans(Nat, Nat.add(A, Nat.add(C.shift(k, t1), C.shift(k, t2))), Nat.add(A, Nat.add(C.shift(k, t2), C.shift(k, t1))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(C.shift(k, t1), C.shift(k, t2)), Nat.add(C.shift(k, t2), C.shift(k, t1)), N.add_comm(C.shift(k, t1), C.shift(k, t2))), Equal.trans(Nat, Nat.add(A, Nat.add(C.shift(k, t2), C.shift(k, t1))), Nat.add(A, C.shift(k, Nat.add(t2, t1))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(C.shift(k, t2), C.shift(k, t1)), C.shift(k, Nat.add(t2, t1)), Equal.sym(Nat, C.shift(k, Nat.add(t2, t1)), Nat.add(C.shift(k, t2), C.shift(k, t1)), WW.shift_add(k, t2, t1))), Equal.trans(Nat, Nat.add(A, C.shift(k, Nat.add(t2, t1))), Nat.add(A, C.shift(k, Nat.add(cl, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(A, C.shift(k, z)), Nat.add(t2, t1), Nat.add(cl, C.shift(k, ch)), ec), Equal.trans(Nat, Nat.add(A, C.shift(k, Nat.add(cl, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, ph)), C.shift(k, Nat.add(cl, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(k, Nat.add(cl, C.shift(k, ch)))), A, Nat.add(pl, C.shift(k, ph)), ea), Equal.trans(Nat, Nat.add(Nat.add(pl, C.shift(k, ph)), C.shift(k, Nat.add(cl, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, ph)), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(pl, C.shift(k, ph)), z), C.shift(k, Nat.add(cl, C.shift(k, ch))), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch))), WW.shift_add(k, cl, C.shift(k, ch))), Equal.trans(Nat, Nat.add(Nat.add(pl, C.shift(k, ph)), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch)))), Nat.add(pl, Nat.add(C.shift(k, ph), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch))))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), NA.add_assoc(pl, C.shift(k, ph), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch)))), Equal.trans(Nat, Nat.add(pl, Nat.add(C.shift(k, ph), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch))))), Nat.add(pl, Nat.add(Nat.add(C.shift(k, ph), C.shift(k, cl)), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, z), Nat.add(C.shift(k, ph), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(C.shift(k, ph), C.shift(k, cl)), C.shift(k, C.shift(k, ch))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(k, ph), C.shift(k, cl)), C.shift(k, C.shift(k, ch))), Nat.add(C.shift(k, ph), Nat.add(C.shift(k, cl), C.shift(k, C.shift(k, ch)))), NA.add_assoc(C.shift(k, ph), C.shift(k, cl), C.shift(k, C.shift(k, ch))))), Equal.trans(Nat, Nat.add(pl, Nat.add(Nat.add(C.shift(k, ph), C.shift(k, cl)), C.shift(k, C.shift(k, ch)))), Nat.add(pl, Nat.add(C.shift(k, Nat.add(ph, cl)), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, Nat.add(z, C.shift(k, C.shift(k, ch)))), Nat.add(C.shift(k, ph), C.shift(k, cl)), C.shift(k, Nat.add(ph, cl)), Equal.sym(Nat, C.shift(k, Nat.add(ph, cl)), Nat.add(C.shift(k, ph), C.shift(k, cl)), WW.shift_add(k, ph, cl))), Equal.trans(Nat, Nat.add(pl, Nat.add(C.shift(k, Nat.add(ph, cl)), C.shift(k, C.shift(k, ch)))), Nat.add(pl, Nat.add(C.shift(k, Nat.add(s, C.shift(k, cr))), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, Nat.add(C.shift(k, z), C.shift(k, C.shift(k, ch)))), Nat.add(ph, cl), Nat.add(s, C.shift(k, cr)), Equal.sym(Nat, Nat.add(s, C.shift(k, cr)), Nat.add(ph, cl), es)), Equal.trans(Nat, Nat.add(pl, Nat.add(C.shift(k, Nat.add(s, C.shift(k, cr))), C.shift(k, C.shift(k, ch)))), Nat.add(pl, Nat.add(Nat.add(C.shift(k, s), C.shift(k, C.shift(k, cr))), C.shift(k, C.shift(k, ch)))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, Nat.add(z, C.shift(k, C.shift(k, ch)))), C.shift(k, Nat.add(s, C.shift(k, cr))), Nat.add(C.shift(k, s), C.shift(k, C.shift(k, cr))), WW.shift_add(k, s, C.shift(k, cr))), Equal.trans(Nat, Nat.add(pl, Nat.add(Nat.add(C.shift(k, s), C.shift(k, C.shift(k, cr))), C.shift(k, C.shift(k, ch)))), Nat.add(pl, Nat.add(C.shift(k, s), Nat.add(C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch))))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, z), Nat.add(Nat.add(C.shift(k, s), C.shift(k, C.shift(k, cr))), C.shift(k, C.shift(k, ch))), Nat.add(C.shift(k, s), Nat.add(C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch)))), NA.add_assoc(C.shift(k, s), C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch)))), Equal.trans(Nat, Nat.add(pl, Nat.add(C.shift(k, s), Nat.add(C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch))))), Nat.add(pl, Nat.add(C.shift(k, s), C.shift(k, Nat.add(C.shift(k, cr), C.shift(k, ch))))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, Nat.add(C.shift(k, s), z)), Nat.add(C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch))), C.shift(k, Nat.add(C.shift(k, cr), C.shift(k, ch))), Equal.sym(Nat, C.shift(k, Nat.add(C.shift(k, cr), C.shift(k, ch))), Nat.add(C.shift(k, C.shift(k, cr)), C.shift(k, C.shift(k, ch))), WW.shift_add(k, C.shift(k, cr), C.shift(k, ch)))), Equal.trans(Nat, Nat.add(pl, Nat.add(C.shift(k, s), C.shift(k, Nat.add(C.shift(k, cr), C.shift(k, ch))))), Nat.add(pl, Nat.add(C.shift(k, s), C.shift(k, C.shift(k, Nat.add(cr, ch))))), Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Equal.cong(Nat, Nat, z => Nat.add(pl, Nat.add(C.shift(k, s), C.shift(k, z))), Nat.add(C.shift(k, cr), C.shift(k, ch)), C.shift(k, Nat.add(cr, ch)), Equal.sym(Nat, C.shift(k, Nat.add(cr, ch)), Nat.add(C.shift(k, cr), C.shift(k, ch)), WW.shift_add(k, cr, ch))), Equal.sym(Nat, Nat.add(Nat.add(pl, C.shift(k, s)), C.shift(k, C.shift(k, Nat.add(cr, ch)))), Nat.add(pl, Nat.add(C.shift(k, s), C.shift(k, C.shift(k, Nat.add(cr, ch))))), NA.add_assoc(pl, C.shift(k, s), C.shift(k, C.shift(k, Nat.add(cr, ch))))))))))))))))))))))

def val_eta(+p: WU.U64) -> {SW.value(p) == Nat.add(v(X.lo(p)), C.shift(32n, v(X.hi(p)))) : Nat}:
  match p:
    case WU.U64{+l, +h}:
      {==}

def prod_fits(+k: Nat, +x: Nat, +y: Nat, +hx: {C.fits(k, x) == True{} : Bool}, +hy: {C.fits(k, y) == True{} : Bool}) -> {C.fits(Nat.add(k, k), Nat.mul(x, y)) == True{} : Bool}:
  +h = W64M.mul_lt_sq(x, y, C.pow2(k), WW.lt_of_fits(k, x, hx), WW.lt_of_fits(k, y, hy))
  WW.fits_of_lt(Nat.add(k, k), Nat.mul(x, y), L.subst(Nat, z => {Nat.is_lt(Nat.mul(x, y), z) == True{} : Bool}, Nat.mul(C.pow2(k), C.pow2(k)), C.pow2(Nat.add(k, k)), WW.pow2_sq(k), h))

def le_hi(+k: Nat, +x: Nat, +y: Nat, +hy: {Nat.is_le(1n, y) == True{} : Bool}) -> {Nat.is_le(C.pow2(k), Nat.add(x, C.shift(k, y))) == True{} : Bool}:
  +h1 = L.subst(Nat, z => {Nat.is_le(z, C.shift(k, y)) == True{} : Bool}, C.shift(k, 1n), C.pow2(k), WW.shift_one(k), WW.shift_mono(k, 1n, y, hy))
  N.le_trans(C.pow2(k), C.shift(k, y), Nat.add(x, C.shift(k, y)), h1, L.subst(Nat, z => {Nat.is_le(C.shift(k, y), z) == True{} : Bool}, Nat.add(C.shift(k, y), x), Nat.add(x, C.shift(k, y)), N.add_comm(C.shift(k, y), x), N.le_add_right(C.shift(k, y), x)))

def both_hi(+k: Nat, +x1: Nat, +y1: Nat, +x2: Nat, +y2: Nat, +hy1: {Nat.is_le(1n, y1) == True{} : Bool}, +hy2: {Nat.is_le(1n, y2) == True{} : Bool}) -> {C.fits(Nat.add(k, k), Nat.mul(Nat.add(x1, C.shift(k, y1)), Nat.add(x2, C.shift(k, y2)))) == False{} : Bool}:
  +a = Nat.add(x1, C.shift(k, y1))
  +b = Nat.add(x2, C.shift(k, y2))
  +P = C.pow2(k)
  +h1 = N.le_trans(Nat.mul(P, P), Nat.mul(a, P), Nat.mul(a, b), AR2.mul_le(P, a, P, le_hi(k, x1, y1, hy1)), W64M.le_mul_r(a, P, b, le_hi(k, x2, y2, hy2)))
  +h2 = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(a, b)) == True{} : Bool}, Nat.mul(P, P), C.pow2(Nat.add(k, k)), WW.pow2_sq(k), h1)
  Equal.trans(Bool, C.fits(Nat.add(k, k), Nat.mul(a, b)), Nat.is_lt(Nat.mul(a, b), C.pow2(Nat.add(k, k))), False{}, WW.fits_lt(Nat.add(k, k), Nat.mul(a, b)), N.le_not_lt(Nat.mul(a, b), C.pow2(Nat.add(k, k)), h2))

def pos_ne(+n: Nat, +h: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.is_le(1n, n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, true_ne_false(h))
    case 1n+m:
      N.zero_le(m)

def or_cr(+x: Nat, +c: Bool) -> {Bool.or(Bool.not(Nat.is_eq(x, 0n)), c) == Bool.not(Nat.is_eq(Nat.add(bv(c), x), 0n)) : Bool}:
  match x c:
    case 0n True{}:
      {==}
    case 1n+y True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+y False{}:
      {==}

# with ah bh == 0 and the cross sum fitting 64 bits: the one-limb overflow test
def mo_core(+al: U32, +ah: U32, +bl: U32, +bh: U32, +eh: {Nat.mul(v(ah), v(bh)) == 0n : Nat}, +hT: {C.fits(64n, Nat.add(Nat.mul(v(ah), v(bl)), Nat.mul(v(al), v(bh)))) == True{} : Bool}) -> {X.mul_over_one(X.mul32(al, bl), X.add(X.mul32(ah, bl), X.mul32(al, bh))) == Bool.not(C.fits(64n, Nat.mul(val(al, ah), val(bl, bh)))) : Bool}:
  +p = X.mul32(al, bl)
  +c = X.add(X.mul32(ah, bl), X.mul32(al, bh))
  +pl = X.lo(p)
  +ph = X.hi(p)
  +cl = X.lo(c)
  +ch = X.hi(c)
  +s = U32.add(ph, cl)
  +cr = P64.carry32(ph, cl)
  +A = Nat.mul(v(al), v(bl))
  +t1 = Nat.mul(v(al), v(bh))
  +t2 = Nat.mul(v(ah), v(bl))
  +ea = Equal.trans(Nat, A, SW.value(p), Nat.add(v(pl), C.shift(32n, v(ph))), Equal.sym(Nat, SW.value(p), A, W64M.mul32_value(al, bl)), val_eta(p))
  av = add_value(X.mul32(ah, bl), X.mul32(al, bh))
  +ecv = Equal.trans(Nat, SW.value(c), C.low(64n, Nat.add(SW.value(X.mul32(ah, bl)), SW.value(X.mul32(al, bh)))), Nat.add(t2, t1), av, Equal.trans(Nat, C.low(64n, Nat.add(SW.value(X.mul32(ah, bl)), SW.value(X.mul32(al, bh)))), C.low(64n, Nat.add(t2, t1)), Nat.add(t2, t1), Equal.trans(Nat, C.low(64n, Nat.add(SW.value(X.mul32(ah, bl)), SW.value(X.mul32(al, bh)))), C.low(64n, Nat.add(t2, SW.value(X.mul32(al, bh)))), C.low(64n, Nat.add(t2, t1)), Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(z, SW.value(X.mul32(al, bh)))), SW.value(X.mul32(ah, bl)), t2, W64M.mul32_value(ah, bl)), Equal.cong(Nat, Nat, z => C.low(64n, Nat.add(t2, z)), SW.value(X.mul32(al, bh)), t1, W64M.mul32_value(al, bh))), WW.low_fit(64n, Nat.add(t2, t1), hT)))
  +ec = Equal.trans(Nat, Nat.add(t2, t1), SW.value(c), Nat.add(v(cl), C.shift(32n, v(ch))), Equal.sym(Nat, SW.value(c), Nat.add(t2, t1), ecv), val_eta(c))
  +es = acons(ph, cl)
  +ealg = mo_alg(32n, A, t1, t2, Nat.mul(v(ah), v(bh)), v(pl), v(ph), v(cl), v(ch), v(s), bv(cr), ea, ec, es, eh)
  +pr = Nat.mul(val(al, ah), val(bl, bh))
  +q = Nat.add(bv(cr), v(ch))
  +R = Nat.add(v(pl), C.shift(32n, v(s)))
  +e1 = Equal.trans(Nat, pr, Nat.add(Nat.add(Nat.mul(v(al), v(bl)), C.shift(32n, Nat.mul(v(al), v(bh)))), Nat.add(C.shift(32n, Nat.mul(v(ah), v(bl))), C.shift(32n, C.shift(32n, Nat.mul(v(ah), v(bh)))))), Nat.add(R, C.shift(64n, q)), WW.expand_k(32n, v(al), v(ah), v(bl), v(bh)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(v(al), v(bl)), C.shift(32n, Nat.mul(v(al), v(bh)))), Nat.add(C.shift(32n, Nat.mul(v(ah), v(bl))), C.shift(32n, C.shift(32n, Nat.mul(v(ah), v(bh)))))), Nat.add(R, C.shift(32n, C.shift(32n, q))), Nat.add(R, C.shift(64n, q)), ealg, Equal.cong(Nat, Nat, z => Nat.add(R, z), C.shift(32n, C.shift(32n, q)), C.shift(64n, q), Equal.sym(Nat, C.shift(64n, q), C.shift(32n, C.shift(32n, q)), WW.shift_comp(32n, 32n, q)))))
  +eh2 = Equal.trans(Nat, C.high(64n, pr), C.high(64n, Nat.add(R, C.shift(64n, q))), q, Equal.cong(Nat, Nat, z => C.high(64n, z), pr, Nat.add(R, C.shift(64n, q)), e1), WW.high_u(64n, R, q, WW.limbs_fit(32n, 32n, v(pl), v(s), vb(pl), vb(s))))
  +em1 = Equal.trans(Bool, Bool.or(Bool.not(U32.is_zero(ch)), U32.is_lt(s, ph)), Bool.or(Bool.not(Nat.is_eq(v(ch), 0n)), U32.is_lt(s, ph)), Bool.or(Bool.not(Nat.is_eq(v(ch), 0n)), cr), Equal.cong(Bool, Bool, z => Bool.or(Bool.not(z), U32.is_lt(s, ph)), U32.is_zero(ch), Nat.is_eq(v(ch), 0n), LW.zero_nat(ch)), Equal.cong(Bool, Bool, z => Bool.or(Bool.not(Nat.is_eq(v(ch), 0n)), z), U32.is_lt(s, ph), cr, P64.add_lt(ph, cl)))
  Equal.trans(Bool, Bool.or(Bool.not(U32.is_zero(ch)), U32.is_lt(s, ph)), Bool.not(Nat.is_eq(q, 0n)), Bool.not(C.fits(64n, pr)), Equal.trans(Bool, Bool.or(Bool.not(U32.is_zero(ch)), U32.is_lt(s, ph)), Bool.or(Bool.not(Nat.is_eq(v(ch), 0n)), cr), Bool.not(Nat.is_eq(q, 0n)), em1, or_cr(v(ch), cr)), Equal.sym(Bool, Bool.not(C.fits(64n, pr)), Bool.not(Nat.is_eq(q, 0n)), Equal.cong(Nat, Bool, z => Bool.not(Nat.is_eq(z, 0n)), C.high(64n, pr), q, eh2)))

def mo_top(+al: U32, +ah: U32, +bl: U32, +bh: U32, +z1: Bool, +z2: Bool, +hz1: {U32.is_zero(ah) == z1 : Bool}, +hz2: {U32.is_zero(bh) == z2 : Bool}) -> {Bool.or(Bool.and(Bool.not(z1), Bool.not(z2)), X.mul_over_one(X.mul32(al, bl), X.add(X.mul32(ah, bl), X.mul32(al, bh)))) == Bool.not(C.fits(64n, Nat.mul(val(al, ah), val(bl, bh)))) : Bool}:
  match z1 z2:
    case False{} False{}:
      +h1 = pos_ne(v(ah), Equal.trans(Bool, Nat.is_eq(v(ah), 0n), U32.is_zero(ah), False{}, Equal.sym(Bool, U32.is_zero(ah), Nat.is_eq(v(ah), 0n), LW.zero_nat(ah)), hz1))
      +h2 = pos_ne(v(bh), Equal.trans(Bool, Nat.is_eq(v(bh), 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(v(bh), 0n), LW.zero_nat(bh)), hz2))
      +hb = both_hi(32n, v(al), v(ah), v(bl), v(bh), h1, h2)
      Equal.sym(Bool, Bool.not(C.fits(64n, Nat.mul(val(al, ah), val(bl, bh)))), True{}, Equal.cong(Bool, Bool, t => Bool.not(t), C.fits(64n, Nat.mul(val(al, ah), val(bl, bh))), False{}, hb))
    case True{} _:
      +eah = N.eq_from_is_eq(v(ah), 0n, Equal.trans(Bool, Nat.is_eq(v(ah), 0n), U32.is_zero(ah), True{}, Equal.sym(Bool, U32.is_zero(ah), Nat.is_eq(v(ah), 0n), LW.zero_nat(ah)), hz1))
      +eh = L.subst(Nat, z => {Nat.mul(z, v(bh)) == 0n : Nat}, 0n, v(ah), Equal.sym(Nat, v(ah), 0n, eah), {==})
      +hT = L.subst(Nat, z => {C.fits(64n, Nat.add(Nat.mul(z, v(bl)), Nat.mul(v(al), v(bh)))) == True{} : Bool}, 0n, v(ah), Equal.sym(Nat, v(ah), 0n, eah), prod_fits(32n, v(al), v(bh), vb(al), vb(bh)))
      mo_core(al, ah, bl, bh, eh, hT)
    case False{} True{}:
      +ebh = N.eq_from_is_eq(v(bh), 0n, Equal.trans(Bool, Nat.is_eq(v(bh), 0n), U32.is_zero(bh), True{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(v(bh), 0n), LW.zero_nat(bh)), hz2))
      +eh = L.subst(Nat, z => {Nat.mul(v(ah), z) == 0n : Nat}, 0n, v(bh), Equal.sym(Nat, v(bh), 0n, ebh), NA.mul_zero(v(ah)))
      +e0 = Equal.trans(Nat, Nat.add(Nat.mul(v(ah), v(bl)), Nat.mul(v(al), 0n)), Nat.add(Nat.mul(v(ah), v(bl)), 0n), Nat.mul(v(ah), v(bl)), Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(v(ah), v(bl)), t), Nat.mul(v(al), 0n), 0n, NA.mul_zero(v(al))), N.add_zero(Nat.mul(v(ah), v(bl))))
      +hT0 = L.subst(Nat, z => {C.fits(64n, z) == True{} : Bool}, Nat.mul(v(ah), v(bl)), Nat.add(Nat.mul(v(ah), v(bl)), Nat.mul(v(al), 0n)), Equal.sym(Nat, Nat.add(Nat.mul(v(ah), v(bl)), Nat.mul(v(al), 0n)), Nat.mul(v(ah), v(bl)), e0), prod_fits(32n, v(ah), v(bl), vb(ah), vb(bl)))
      +hT = L.subst(Nat, z => {C.fits(64n, Nat.add(Nat.mul(v(ah), v(bl)), Nat.mul(v(al), z))) == True{} : Bool}, 0n, v(bh), Equal.sym(Nat, v(bh), 0n, ebh), hT0)
      mo_core(al, ah, bl, bh, eh, hT)

def mul_over_value(+a: WU.U64, +b: WU.U64) -> SW.MulOver.value(a, b):
  match a b:
    case WU.U64{+al, +ah} WU.U64{+bl, +bh}:
      mo_top(al, ah, bl, bh, U32.is_zero(ah), U32.is_zero(bh), {==}, {==})
