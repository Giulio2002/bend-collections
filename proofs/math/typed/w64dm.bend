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
import ../../lib/u32.bend as U
import ../../lib/u32div.bend as UD
import ../../lib/arith.bend as AR2
import ../../lib/lemmas/spec/numeric.bend as S
import ../natural/arith.bend as NR
import ../u64/u64.bend as P64
import ./w64mul.bend as W64M
import ./w64sqrt.bend as W64S
import ./w64div.bend as W64D
import ./w64add.bend as WA
import ./width.bend as WW
import ./u32laws.bend as LW
import ./natfuel.bend as NF

# 64 / 64 division, a * b mod m and the 64-bit square root of
# src/math/w64.bend. The quotient loops take any 32-bit estimate down while
# q b > x and up while (q + 1) b <= x, so the proofs never use the estimate's
# accuracy (Knuth's Theorem B only bounds the loops' run time); the proof is
# the loop invariant of the Why3 gallery's integer square root and division
# examples, closed by the uniqueness of floor(x / b) (Mathlib Nat.div_add_mod,
# Nat.div_eq_of_lt_le).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def true_ne_false(+h: {True{} == False{} : Bool}) -> Empty:
  LW.true_ne_false(h)

def vb(+x: U32) -> {C.fits(32n, v(x)) == True{} : Bool}:
  LW.vb(x)

def lt_add_pos(+a: Nat, +c: Nat, +h: {Nat.is_lt(0n, c) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(a, c)) == True{} : Bool}:
  +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, 0n), Nat.add(a, c)), Nat.is_lt(0n, c), True{}, WW.lt_cancel_l(a, 0n, c), h)
  L.subst(Nat, z => {Nat.is_lt(z, Nat.add(a, c)) == True{} : Bool}, Nat.add(a, 0n), a, N.add_zero(a), h1)

# q, bh < 1 + p, p >= 1, lo + hi (1 + p) == q bh: hi + 1 < 1 + p
def hi_lt(+p: Nat, +q: Nat, +bh: Nat, +lo: Nat, +hi: Nat, +hq: {Nat.is_lt(q, 1n+p) == True{} : Bool}, +hb: {Nat.is_lt(bh, 1n+p) == True{} : Bool}, +hp: {Nat.is_le(1n, p) == True{} : Bool}, +e: {Nat.add(lo, Nat.mul(hi, 1n+p)) == Nat.mul(q, bh) : Nat}) -> {Nat.is_lt(Nat.add(hi, 1n), 1n+p) == True{} : Bool}:
  +h1 = N.le_trans(Nat.mul(q, bh), Nat.mul(p, bh), Nat.mul(p, p), AR2.mul_le(q, p, bh, N.lt_succ_le(q, p, hq)), W64M.le_mul_r(p, bh, p, N.lt_succ_le(bh, p, hb)))
  +h2 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(p, p), z) == True{} : Bool}, Nat.add(p, Nat.mul(p, p)), Nat.mul(p, 1n+p), Equal.sym(Nat, Nat.mul(p, 1n+p), Nat.add(p, Nat.mul(p, p)), NA.mul_succ(p, p)), L.subst(Nat, z => {Nat.is_lt(Nat.mul(p, p), z) == True{} : Bool}, Nat.add(Nat.mul(p, p), p), Nat.add(p, Nat.mul(p, p)), N.add_comm(Nat.mul(p, p), p), lt_add_pos(Nat.mul(p, p), p, N.lt_le_trans(0n, 1n, p, {==}, hp))))
  +h3 = L.subst(Nat, z => {Nat.is_le(Nat.mul(hi, 1n+p), z) == True{} : Bool}, Nat.add(lo, Nat.mul(hi, 1n+p)), Nat.mul(q, bh), e, L.subst(Nat, z => {Nat.is_le(Nat.mul(hi, 1n+p), z) == True{} : Bool}, Nat.add(Nat.mul(hi, 1n+p), lo), Nat.add(lo, Nat.mul(hi, 1n+p)), N.add_comm(Nat.mul(hi, 1n+p), lo), N.le_add_right(Nat.mul(hi, 1n+p), lo)))
  +h4 = W64D.lt_cancel_mul(hi, p, 1n+p, N.le_lt_trans(Nat.mul(hi, 1n+p), Nat.mul(p, p), Nat.mul(p, 1n+p), N.le_trans(Nat.mul(hi, 1n+p), Nat.mul(q, bh), Nat.mul(p, p), h3, h1), h2))
  L.subst(Nat, z => {Nat.is_lt(z, 1n+p) == True{} : Bool}, 1n+hi, Nat.add(hi, 1n), Equal.sym(Nat, Nat.add(hi, 1n), 1n+hi, WA.plus1(hi)), h4)

def P2(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(2n, C.shift(32n, one)) == True{} : Bool}:
  +h = L.subst(Nat, z => {Nat.is_le(z, C.shift(31n, one)) == True{} : Bool}, one, 1n, h1, WW.shift_ge(31n, one))
  N.double_le(1n, C.shift(31n, one), h)

# the 96-bit product q b of mul_32_64: low 64 bits + 2^64 * top 32 bits
def mul3264(+one: Nat, +h1: {one == 1n : Nat}, +q: U32, +bl: U32, +bh: U32) -> {Nat.add(SW.value(X.fst_q(X.mul_32_64(q, WU.U64{bl, bh}))), C.shift(64n, v(X.snd_r(X.mul_32_64(q, WU.U64{bl, bh}))))) == Nat.mul(v(q), SW.value(WU.U64{bl, bh})) : Nat}:
  +p0 = X.mul32(q, bl)
  +p1 = X.mul32(q, bh)
  +e0 = Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), SW.value(p0), Nat.mul(v(q), v(bl)), Equal.sym(Nat, SW.value(p0), Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), WA.val_eta(p0)), W64M.mul32_value(q, bl))
  +e1 = Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), SW.value(p1), Nat.mul(v(q), v(bh)), Equal.sym(Nat, SW.value(p1), Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), WA.val_eta(p1)), W64M.mul32_value(q, bh))
  +es = WA.acons(X.hi(p0), X.lo(p1))
  +PP = C.shift(32n, one)
  +pp = Nat.sub(PP, 1n)
  +h2 = P2(one, h1)
  +eP = N.sub_add(PP, 1n, N.le_trans(1n, 2n, PP, {==}, h2))
  +hp = NF.sub_mono_l(2n, PP, 1n, h2)
  +hq = L.subst(Nat, z => {Nat.is_lt(v(q), z) == True{} : Bool}, PP, 1n+pp, Equal.sym(Nat, 1n+pp, PP, eP), WW.lt_one(32n, one, h1, v(q), vb(q)))
  +hbh = L.subst(Nat, z => {Nat.is_lt(v(bh), z) == True{} : Bool}, PP, 1n+pp, Equal.sym(Nat, 1n+pp, PP, eP), WW.lt_one(32n, one, h1, v(bh), vb(bh)))
  +e1p = Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bh))), Nat.mul(v(X.hi(X.mul32(q, bh))), 1n+pp)), Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), Nat.mul(v(q), v(bh)), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bh))), z), Nat.mul(v(X.hi(X.mul32(q, bh))), 1n+pp), C.shift(32n, v(X.hi(X.mul32(q, bh)))), Equal.sym(Nat, C.shift(32n, v(X.hi(X.mul32(q, bh)))), Nat.mul(v(X.hi(X.mul32(q, bh))), 1n+pp), Equal.trans(Nat, C.shift(32n, v(X.hi(X.mul32(q, bh)))), Nat.mul(v(X.hi(X.mul32(q, bh))), PP), Nat.mul(v(X.hi(X.mul32(q, bh))), 1n+pp), WW.shift_mul_one(32n, one, h1, v(X.hi(X.mul32(q, bh)))), Equal.cong(Nat, Nat, z => Nat.mul(v(X.hi(X.mul32(q, bh))), z), PP, 1n+pp, Equal.sym(Nat, 1n+pp, PP, eP))))), e1)
  +hh = hi_lt(pp, v(q), v(bh), v(X.lo(X.mul32(q, bh))), v(X.hi(X.mul32(q, bh))), hq, hbh, hp, e1p)
  +cb = U32.is_lt(U32.add(X.hi(p0), X.lo(p1)), X.hi(p0))
  +ecb = Equal.trans(Nat, v(X.b32(cb)), S.bit_value(cb), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), W64M.b32_v(cb), Equal.cong(Bool, Nat, z => S.bit_value(z), cb, P64.carry32(X.hi(p0), X.lo(p1)), P64.add_lt(X.hi(p0), X.lo(p1))))
  +hle = L.subst(Nat, z => {Nat.is_le(Nat.add(v(X.hi(X.mul32(q, bh))), z), Nat.add(v(X.hi(X.mul32(q, bh))), 1n)) == True{} : Bool}, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.b32(cb)), Equal.sym(Nat, v(X.b32(cb)), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), ecb), N.le_add_left(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), 1n, v(X.hi(X.mul32(q, bh))), W64M.bit_le1(P64.carry32(X.hi(p0), X.lo(p1)))))
  +hfit = WW.fits_one(32n, one, h1, Nat.add(v(X.hi(X.mul32(q, bh))), v(X.b32(cb))), L.subst(Nat, z => {Nat.is_lt(Nat.add(v(X.hi(X.mul32(q, bh))), v(X.b32(cb))), z) == True{} : Bool}, 1n+pp, PP, eP, N.le_lt_trans(Nat.add(v(X.hi(X.mul32(q, bh))), v(X.b32(cb))), Nat.add(v(X.hi(X.mul32(q, bh))), 1n), 1n+pp, hle, hh)))
  +etop = Equal.trans(Nat, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))), Nat.add(v(X.hi(X.mul32(q, bh))), v(X.b32(cb))), Nat.add(v(X.hi(X.mul32(q, bh))), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), WA.add_exact(one, h1, X.hi(p1), X.b32(cb), hfit), Equal.cong(Nat, Nat, z => Nat.add(v(X.hi(X.mul32(q, bh))), z), v(X.b32(cb)), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), ecb))
  Equal.sym(Nat, Nat.mul(v(q), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.trans(Nat, Nat.mul(v(q), Nat.add(v(bl), C.shift(32n, v(bh)))), Nat.add(Nat.mul(v(q), v(bl)), Nat.mul(v(q), C.shift(32n, v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), NA.mul_add_left(v(q), v(bl), C.shift(32n, v(bh))), Equal.trans(Nat, Nat.add(Nat.mul(v(q), v(bl)), Nat.mul(v(q), C.shift(32n, v(bh)))), Nat.add(Nat.mul(v(q), v(bl)), C.shift(32n, Nat.mul(v(q), v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(v(q), v(bl)), z), Nat.mul(v(q), C.shift(32n, v(bh))), C.shift(32n, Nat.mul(v(q), v(bh))), WW.shift_mul_r(32n, v(q), v(bh))), Equal.trans(Nat, Nat.add(Nat.mul(v(q), v(bl)), C.shift(32n, Nat.mul(v(q), v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), C.shift(32n, Nat.mul(v(q), v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, Nat.mul(v(q), v(bh)))), Nat.mul(v(q), v(bl)), Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), Equal.sym(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), Nat.mul(v(q), v(bl)), e0)), Equal.trans(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), C.shift(32n, Nat.mul(v(q), v(bh)))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), C.shift(32n, Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), C.shift(32n, z)), Nat.mul(v(q), v(bh)), Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), Equal.sym(Nat, Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), Nat.mul(v(q), v(bh)), e1)), Equal.trans(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), C.shift(32n, Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), z), C.shift(32n, Nat.add(v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), WW.shift_add(32n, v(X.lo(X.mul32(q, bh))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Equal.trans(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl))))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), NA.add_assoc(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(X.hi(X.mul32(q, bl)))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), z), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Equal.sym(Nat, Nat.add(Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), Nat.add(C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), NA.add_assoc(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh)))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(z, C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), C.shift(32n, Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh))))), Equal.sym(Nat, C.shift(32n, Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh))))), Nat.add(C.shift(32n, v(X.hi(X.mul32(q, bl)))), C.shift(32n, v(X.lo(X.mul32(q, bh))))), WW.shift_add(32n, v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh)))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, Nat.add(v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, z), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh)))), Nat.add(v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), Equal.sym(Nat, Nat.add(v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), Nat.add(v(X.hi(X.mul32(q, bl))), v(X.lo(X.mul32(q, bh)))), es)), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, Nat.add(v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(z, C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), C.shift(32n, Nat.add(v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), WW.shift_add(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), Nat.add(C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), z), Nat.add(Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), Nat.add(C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), NA.add_assoc(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), Nat.add(C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), z)), Nat.add(C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), C.shift(32n, Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Equal.sym(Nat, C.shift(32n, Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))), Nat.add(C.shift(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, v(X.hi(X.mul32(q, bh)))))), WW.shift_add(32n, C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh))))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh)))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, z))), Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))), Equal.sym(Nat, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))), Nat.add(C.shift(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, v(X.hi(X.mul32(q, bh))))), WW.shift_add(32n, WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))), Equal.trans(Nat, Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.sym(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))))), Nat.add(v(X.lo(X.mul32(q, bl))), Nat.add(C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))))), NA.add_assoc(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))))), Equal.trans(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), z), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))), C.shift(64n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))), Equal.sym(Nat, C.shift(64n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))), C.shift(32n, C.shift(32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))), WW.shift_comp(32n, 32n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))))), Equal.trans(Nat, Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, Nat.add(v(X.hi(X.mul32(q, bh))), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))))), Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, z)), Nat.add(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh)))), Nat.add(v(X.hi(X.mul32(q, bh))), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), N.add_comm(WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))), v(X.hi(X.mul32(q, bh))))), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(v(X.lo(X.mul32(q, bl))), C.shift(32n, v(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh)))))), C.shift(64n, z)), Nat.add(v(X.hi(X.mul32(q, bh))), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))), Equal.sym(Nat, v(U32.add(X.hi(X.mul32(q, bh)), X.b32(U32.is_lt(U32.add(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))), X.hi(X.mul32(q, bl)))))), Nat.add(v(X.hi(X.mul32(q, bh))), WA.bv(P64.carry32(X.hi(X.mul32(q, bl)), X.lo(X.mul32(q, bh))))), etop)))))))))))))))))))

def fit64(+a: WU.U64) -> {C.fits(64n, SW.value(a)) == True{} : Bool}:
  match a:
    case WU.U64{+l, +h}:
      WW.limbs_fit(32n, 32n, v(l), v(h), vb(l), vb(h))

# the 96-bit comparison of over96
def ov96(+xl: WU.U64, +xh: U32, +pl: WU.U64, +ph: U32) -> {X.over96(xl, xh, (pl, ph)) == Nat.is_lt(Nat.add(SW.value(xl), C.shift(64n, v(xh))), Nat.add(SW.value(pl), C.shift(64n, v(ph)))) : Bool}:
  +e1 = Equal.cong(Bool, Bool, z => Bool.or(z, Bool.and(U32.is_eq(xh, ph), X.lt(xl, pl))), U32.is_lt(xh, ph), Nat.is_lt(v(xh), v(ph)), U.is_lt_nat(xh, ph))
  +e2 = Equal.cong(Bool, Bool, z => Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(z, X.lt(xl, pl))), U32.is_eq(xh, ph), Nat.is_eq(v(xh), v(ph)), LW.eq_nat(xh, ph))
  +e3 = Equal.cong(Bool, Bool, z => Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(Nat.is_eq(v(xh), v(ph)), z)), X.lt(xl, pl), Nat.is_lt(SW.value(xl), SW.value(pl)), WA.lt_value(xl, pl))
  Equal.trans(Bool, X.over96(xl, xh, (pl, ph)), Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(U32.is_eq(xh, ph), X.lt(xl, pl))), Nat.is_lt(Nat.add(SW.value(xl), C.shift(64n, v(xh))), Nat.add(SW.value(pl), C.shift(64n, v(ph)))), e1, Equal.trans(Bool, Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(U32.is_eq(xh, ph), X.lt(xl, pl))), Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(Nat.is_eq(v(xh), v(ph)), X.lt(xl, pl))), Nat.is_lt(Nat.add(SW.value(xl), C.shift(64n, v(xh))), Nat.add(SW.value(pl), C.shift(64n, v(ph)))), e2, Equal.trans(Bool, Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(Nat.is_eq(v(xh), v(ph)), X.lt(xl, pl))), Bool.or(Nat.is_lt(v(xh), v(ph)), Bool.and(Nat.is_eq(v(xh), v(ph)), Nat.is_lt(SW.value(xl), SW.value(pl)))), Nat.is_lt(Nat.add(SW.value(xl), C.shift(64n, v(xh))), Nat.add(SW.value(pl), C.shift(64n, v(ph)))), e3, WW.lt_limbs(64n, SW.value(xl), v(xh), SW.value(pl), v(ph), fit64(xl), fit64(pl)))))

def X96(+xl: WU.U64, +xh: U32) -> Nat:
  Nat.add(SW.value(xl), C.shift(64n, v(xh)))

# q b > x
def ovq(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32) -> {X.over96(xl, xh, X.mul_32_64(q, b)) == Nat.is_lt(X96(xl, xh), Nat.mul(v(q), SW.value(b))) : Bool}:
  match b:
    case WU.U64{+bl, +bh}:
      Equal.trans(Bool, X.over96(xl, xh, (X.fst_q(X.mul_32_64(q, WU.U64{bl, bh})), X.snd_r(X.mul_32_64(q, WU.U64{bl, bh})))), Nat.is_lt(X96(xl, xh), Nat.add(SW.value(X.fst_q(X.mul_32_64(q, WU.U64{bl, bh}))), C.shift(64n, v(X.snd_r(X.mul_32_64(q, WU.U64{bl, bh})))))), Nat.is_lt(X96(xl, xh), Nat.mul(v(q), SW.value(WU.U64{bl, bh}))), ov96(xl, xh, X.fst_q(X.mul_32_64(q, WU.U64{bl, bh})), X.snd_r(X.mul_32_64(q, WU.U64{bl, bh}))), Equal.cong(Nat, Bool, z => Nat.is_lt(X96(xl, xh), z), Nat.add(SW.value(X.fst_q(X.mul_32_64(q, WU.U64{bl, bh}))), C.shift(64n, v(X.snd_r(X.mul_32_64(q, WU.U64{bl, bh}))))), Nat.mul(v(q), SW.value(WU.U64{bl, bh})), mul3264(one, h1, q, bl, bh)))

# ---- the quotient loops ----

def QB(+b: WU.U64, +q: U32) -> Nat:
  Nat.mul(v(q), SW.value(b))

# down: q - 1 while q b > x; ends with q b <= x
def qdn(+fu: Nat, +one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +cb: Bool, +nq: Nat, +hf: {Nat.is_lt(v(q), fu) == True{} : Bool}, +hc: {X.over96(xl, xh, X.mul_32_64(q, b)) == cb : Bool}, +hnq: {v(q) == nq : Nat}) -> {Nat.is_le(QB(b, X.q_fix(fu, xl, xh, b, q, cb)), X96(xl, xh)) == True{} : Bool}:
  match fu cb nq:
    case 0n _ _:
      Empty.absurd({Nat.is_le(QB(b, X.q_fix(0n, xl, xh, b, q, cb)), X96(xl, xh)) == True{} : Bool}, N.lt_zero_absurd(v(q), hf))
    case 1n+g False{} _:
      N.not_lt_le(X96(xl, xh), QB(b, q), Equal.trans(Bool, Nat.is_lt(X96(xl, xh), QB(b, q)), X.over96(xl, xh, X.mul_32_64(q, b)), False{}, Equal.sym(Bool, X.over96(xl, xh, X.mul_32_64(q, b)), Nat.is_lt(X96(xl, xh), QB(b, q)), ovq(one, h1, xl, xh, b, q)), hc))
    case 1n+g True{} 0n:
      +h0 = Equal.trans(Bool, Nat.is_lt(X96(xl, xh), QB(b, q)), X.over96(xl, xh, X.mul_32_64(q, b)), True{}, Equal.sym(Bool, X.over96(xl, xh, X.mul_32_64(q, b)), Nat.is_lt(X96(xl, xh), QB(b, q)), ovq(one, h1, xl, xh, b, q)), hc)
      +h1b = L.subst(Nat, z => {Nat.is_lt(X96(xl, xh), Nat.mul(z, SW.value(b))) == True{} : Bool}, v(q), 0n, hnq, h0)
      Empty.absurd({Nat.is_le(QB(b, X.q_fix(1n+g, xl, xh, b, q, True{})), X96(xl, xh)) == True{} : Bool}, N.lt_zero_absurd(X96(xl, xh), h1b))
    case 1n+ +g True{} 1n+ +qp:
      +q1 = U32.sub(q, 1)
      +e1 = Equal.trans(Nat, v(q1), Nat.sub(v(q), 1n), qp, U.sub_nat(q, 1, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+qp, v(q), Equal.sym(Nat, v(q), 1n+qp, hnq), N.zero_le(qp))), Equal.trans(Nat, Nat.sub(v(q), 1n), Nat.sub(1n+qp, 1n), qp, Equal.cong(Nat, Nat, t => Nat.sub(t, 1n), v(q), 1n+qp, hnq), N.sub_zero(qp)))
      +hf1 = L.subst(Nat, z => {Nat.is_lt(z, g) == True{} : Bool}, qp, v(q1), Equal.sym(Nat, v(q1), qp, e1), L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, v(q), 1n+qp, hnq, hf))
      qdn(g, one, h1, xl, xh, b, q1, X.over96(xl, xh, X.mul_32_64(q1, b)), qp, hf1, {==}, e1)

def not_not(+c: Bool) -> {Bool.not(Bool.not(c)) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def q_up_okg(+xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32) -> Bool:
  Bool.and(U32.is_lt(q, m), Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b))))

def q_upg(fuel: Nat, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, up: Bool, +m: U32) -> U32:
  match fuel up:
    case 0n _:
      q
    case 1n+f False{}:
      q
    case 1n+f True{}:
      q_upg(f, xl, xh, b, U32.add(q, 1), q_up_okg(xl, xh, b, U32.add(q, 1), m), m)

def impl_qup(+fuel: Nat, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +up: Bool) -> {X.q_up(fuel, xl, xh, b, q, up) == q_upg(fuel, xl, xh, b, q, up, 4294967295) : U32}:
  match fuel up:
    case 0n _:
      {==}
    case 1n+ +f False{}:
      {==}
    case 1n+ +f True{}:
      impl_qup(f, xl, xh, b, U32.add(q, 1), X.q_up_ok(xl, xh, b, U32.add(q, 1)))

def and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  W64S.and_l(a, b, h)

def and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  W64S.and_r(a, b, h)

def not_t(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(Equal.sym(Bool, False{}, True{}, h)))
    case False{}:
      {==}

# 1 + v(m) == 2^32 for the all-ones word
def m32(+one: Nat, +h1: {one == 1n : Nat}, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}) -> {1n+v(m) == C.shift(32n, one) : Nat}:
  Equal.trans(Nat, 1n+v(m), WD.sc(32n, one), C.shift(32n, one), W64S.mask_v(32n, {==}, one, h1, m, pm), Equal.sym(Nat, C.shift(32n, one), WD.sc(32n, one), W64M.shift_sc(32n, one)))

# q + 1 for q < m
def succ_m(+one: Nat, +h1: {one == 1n : Nat}, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +lt: {Nat.is_lt(v(q), v(m)) == True{} : Bool}) -> {v(U32.add(q, 1)) == 1n+v(q) : Nat}:
  +em = m32(one, h1, m, pm)
  +h = N.le_lt_trans(Nat.add(v(q), 1n), v(m), C.shift(32n, one), L.subst(Nat, z => {Nat.is_le(z, v(m)) == True{} : Bool}, 1n+v(q), Nat.add(v(q), 1n), Equal.sym(Nat, Nat.add(v(q), 1n), 1n+v(q), WA.plus1(v(q))), N.lt_succ_le_succ(v(q), v(m), lt)), L.subst(Nat, z => {Nat.is_lt(v(m), z) == True{} : Bool}, 1n+v(m), C.shift(32n, one), em, N.lt_succ(v(m))))
  Equal.trans(Nat, v(U32.add(q, 1)), Nat.add(v(q), 1n), 1n+v(q), WA.add_exact(one, h1, q, 1, WW.fits_one(32n, one, h1, Nat.add(v(q), 1n), h)), WA.plus1(v(q)))

def qstop(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +hle: {Nat.is_le(v(q), v(m)) == True{} : Bool}, +hX: {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(m), SW.value(b))) == True{} : Bool}, +a: Bool, +ha: {U32.is_lt(q, m) == a : Bool}, +c: Bool, +hcb: {Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b))) == c : Bool}, +hstop: {Bool.and(a, c) == False{} : Bool}) -> {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(q), SW.value(b))) == True{} : Bool}:
  match a c:
    case False{} _:
      +nl = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), False{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +eq = N.le_antisym(v(q), v(m), hle, N.not_lt_le(v(q), v(m), nl))
      L.subst(Nat, z => {Nat.is_lt(X96(xl, xh), Nat.mul(1n+z, SW.value(b))) == True{} : Bool}, v(m), v(q), Equal.sym(Nat, v(q), v(m), eq), hX)
    case True{} False{}:
      +lt = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), True{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +e1 = succ_m(one, h1, q, m, pm, lt)
      +ov = Equal.trans(Bool, Nat.is_lt(X96(xl, xh), QB(b, U32.add(q, 1))), X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)), True{}, Equal.sym(Bool, X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)), Nat.is_lt(X96(xl, xh), QB(b, U32.add(q, 1))), ovq(one, h1, xl, xh, b, U32.add(q, 1))), Equal.trans(Bool, X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)), Bool.not(Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)))), True{}, Equal.sym(Bool, Bool.not(Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)))), X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)), not_not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b)))), Equal.cong(Bool, Bool, t => Bool.not(t), Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b))), False{}, hcb)))
      L.subst(Nat, z => {Nat.is_lt(X96(xl, xh), Nat.mul(z, SW.value(b))) == True{} : Bool}, v(U32.add(q, 1)), 1n+v(q), e1, ov)
    case True{} True{}:
      Empty.absurd({Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(q), SW.value(b))) == True{} : Bool}, true_ne_false(hstop))


# up: q + 1 while q < m and (q + 1) b <= x; ends with q b <= x < (q + 1) b
def qup(+fu: Nat, +one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +ub: Bool, +hf: {Nat.is_lt(Nat.sub(v(m), v(q)), fu) == True{} : Bool}, +hle: {Nat.is_le(v(q), v(m)) == True{} : Bool}, +hs: {Nat.is_le(QB(b, q), X96(xl, xh)) == True{} : Bool}, +hX: {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(m), SW.value(b))) == True{} : Bool}, +hub: {q_up_okg(xl, xh, b, q, m) == ub : Bool}) -> {Nat.is_le(QB(b, q_upg(fu, xl, xh, b, q, ub, m)), X96(xl, xh)) == True{} : Bool} & {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(q_upg(fu, xl, xh, b, q, ub, m)), SW.value(b))) == True{} : Bool}:
  match fu ub:
    case 0n _:
      Empty.absurd({Nat.is_le(QB(b, q_upg(0n, xl, xh, b, q, ub, m)), X96(xl, xh)) == True{} : Bool} & {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(q_upg(0n, xl, xh, b, q, ub, m)), SW.value(b))) == True{} : Bool}, N.lt_zero_absurd(Nat.sub(v(m), v(q)), hf))
    case 1n+g False{}:
      (hs, qstop(one, h1, xl, xh, b, q, m, pm, hle, hX, U32.is_lt(q, m), {==}, Bool.not(X.over96(xl, xh, X.mul_32_64(U32.add(q, 1), b))), {==}, hub))
    case 1n+ +g True{}:
      +q1 = U32.add(q, 1)
      +ha = and_l(U32.is_lt(q, m), Bool.not(X.over96(xl, xh, X.mul_32_64(q1, b))), hub)
      +hb = and_r(U32.is_lt(q, m), Bool.not(X.over96(xl, xh, X.mul_32_64(q1, b))), hub)
      +lt = Equal.trans(Bool, Nat.is_lt(v(q), v(m)), U32.is_lt(q, m), True{}, Equal.sym(Bool, U32.is_lt(q, m), Nat.is_lt(v(q), v(m)), U.is_lt_nat(q, m)), ha)
      +e1 = succ_m(one, h1, q, m, pm, lt)
      +nov = not_t(X.over96(xl, xh, X.mul_32_64(q1, b)), hb)
      +hs1 = N.not_lt_le(X96(xl, xh), QB(b, q1), Equal.trans(Bool, Nat.is_lt(X96(xl, xh), QB(b, q1)), X.over96(xl, xh, X.mul_32_64(q1, b)), False{}, Equal.sym(Bool, X.over96(xl, xh, X.mul_32_64(q1, b)), Nat.is_lt(X96(xl, xh), QB(b, q1)), ovq(one, h1, xl, xh, b, q1)), nov))
      +hle1 = L.subst(Nat, z => {Nat.is_le(z, v(m)) == True{} : Bool}, 1n+v(q), v(q1), Equal.sym(Nat, v(q1), 1n+v(q), e1), N.lt_succ_le_succ(v(q), v(m), lt))
      +hf0 = L.subst(Nat, z => {Nat.is_lt(z, 1n+g) == True{} : Bool}, Nat.sub(v(m), v(q)), 1n+Nat.sub(v(m), 1n+v(q)), W64S.sub_succ_r(v(q), v(m), lt), hf)
      +hf1 = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), z), g) == True{} : Bool}, 1n+v(q), v(q1), Equal.sym(Nat, v(q1), 1n+v(q), e1), hf0)
      qup(g, one, h1, xl, xh, b, q1, m, pm, q_up_okg(xl, xh, b, q1, m), hf1, hle1, hs1, hX, {==})

# r b <= x < (r + 1) b: r == x / b and x - r b == x mod b
def div_uniq(+x: Nat, +r: Nat, +bp: Nat, +h1: {Nat.is_le(Nat.mul(r, 1n+bp), x) == True{} : Bool}, +h2: {Nat.is_lt(x, Nat.mul(1n+r, 1n+bp)) == True{} : Bool}) -> {Nat.div(x, 1n+bp) == r : Nat} & {Nat.mod(x, 1n+bp) == Nat.sub(x, Nat.mul(r, 1n+bp)) : Nat}:
  +t = Nat.sub(x, Nat.mul(r, 1n+bp))
  +ex = N.sub_add(x, Nat.mul(r, 1n+bp), h1)
  +h3 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(1n+bp, Nat.mul(r, 1n+bp))) == True{} : Bool}, x, Nat.add(Nat.mul(r, 1n+bp), t), Equal.sym(Nat, Nat.add(Nat.mul(r, 1n+bp), t), x, ex), h2)
  +h4 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(r, 1n+bp), t), z) == True{} : Bool}, Nat.add(1n+bp, Nat.mul(r, 1n+bp)), Nat.add(Nat.mul(r, 1n+bp), 1n+bp), N.add_comm(1n+bp, Nat.mul(r, 1n+bp)), h3)
  +ht = Equal.trans(Bool, Nat.is_lt(t, 1n+bp), Nat.is_lt(Nat.add(Nat.mul(r, 1n+bp), t), Nat.add(Nat.mul(r, 1n+bp), 1n+bp)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.mul(r, 1n+bp), t), Nat.add(Nat.mul(r, 1n+bp), 1n+bp)), Nat.is_lt(t, 1n+bp), WW.lt_cancel_l(Nat.mul(r, 1n+bp), t, 1n+bp)), h4)
  (Equal.trans(Nat, Nat.div(x, 1n+bp), Nat.div(Nat.add(Nat.mul(r, 1n+bp), t), 1n+bp), r, Equal.cong(Nat, Nat, z => Nat.div(z, 1n+bp), x, Nat.add(Nat.mul(r, 1n+bp), t), Equal.sym(Nat, Nat.add(Nat.mul(r, 1n+bp), t), x, ex)), NR.div_of(r, bp, t, ht)), Equal.trans(Nat, Nat.mod(x, 1n+bp), Nat.mod(Nat.add(Nat.mul(r, 1n+bp), t), 1n+bp), t, Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), x, Nat.add(Nat.mul(r, 1n+bp), t), Equal.sym(Nat, Nat.add(Nat.mul(r, 1n+bp), t), x, ex)), NR.mod_of(r, bp, t, ht)))

def qfu_g(+xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32) -> U32:
  q_upg(1n+v(U32.sub(m, q)), xl, xh, b, q, q_up_okg(xl, xh, b, q, m), m)

def impl_qfu(+xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32) -> {X.q_fix_up(xl, xh, b, q) == qfu_g(xl, xh, b, q, 4294967295) : U32}:
  impl_qup(1n+v(U32.sub(4294967295, q)), xl, xh, b, q, X.q_up_ok(xl, xh, b, q))

def qs_fin(+x: Nat, +r: Nat, +bp: Nat, +hB: {SW.value(WU.U64{0, 0}) == 0n : Nat}, p: {Nat.is_le(Nat.mul(r, 1n+bp), x) == True{} : Bool} & {Nat.is_lt(x, Nat.mul(1n+r, 1n+bp)) == True{} : Bool}) -> {Nat.div(x, 1n+bp) == r : Nat} & {Nat.mod(x, 1n+bp) == Nat.sub(x, Nat.mul(r, 1n+bp)) : Nat}:
  (+a, +c) = p
  div_uniq(x, r, bp, a, c)

def qs_fin2(+x: Nat, +r: Nat, +B: Nat, +bp: Nat, +hB: {B == 1n+bp : Nat}, p: {Nat.is_le(Nat.mul(r, B), x) == True{} : Bool} & {Nat.is_lt(x, Nat.mul(1n+r, B)) == True{} : Bool}) -> {Nat.div(x, 1n+bp) == r : Nat} & {Nat.mod(x, 1n+bp) == Nat.sub(x, Nat.mul(r, 1n+bp)) : Nat}:
  (+a, +c) = p
  div_uniq(x, r, bp, L.subst(Nat, z => {Nat.is_le(Nat.mul(r, z), x) == True{} : Bool}, B, 1n+bp, hB, a), L.subst(Nat, z => {Nat.is_lt(x, Nat.mul(1n+r, z)) == True{} : Bool}, B, 1n+bp, hB, c))

def qle_fin(+x: Nat, +r: Nat, +B: Nat, p: {Nat.is_le(Nat.mul(r, B), x) == True{} : Bool} & {Nat.is_lt(x, Nat.mul(1n+r, B)) == True{} : Bool}) -> {Nat.is_le(Nat.mul(r, B), x) == True{} : Bool}:
  (+a, +c) = p
  a

def QS(+xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32) -> U32:
  qfu_g(xl, xh, b, X.q_fix(1n+v(q), xl, xh, b, q, X.over96(xl, xh, X.mul_32_64(q, b))), m)

# the quotient loops from any estimate q: q' b <= x < (q' + 1) b
def qs_pair(+one: Nat, +h1: {one == 1n : Nat}, +xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32, +m: U32, +pm: {m == U32{WD.mask(32n, 32n)} : U32}, +hX: {Nat.is_lt(X96(xl, xh), Nat.mul(C.shift(32n, one), SW.value(b))) == True{} : Bool}) -> {Nat.is_le(QB(b, QS(xl, xh, b, q, m)), X96(xl, xh)) == True{} : Bool} & {Nat.is_lt(X96(xl, xh), Nat.mul(1n+v(QS(xl, xh, b, q, m)), SW.value(b))) == True{} : Bool}:
  +q1 = X.q_fix(1n+v(q), xl, xh, b, q, X.over96(xl, xh, X.mul_32_64(q, b)))
  +hs = qdn(1n+v(q), one, h1, xl, xh, b, q, X.over96(xl, xh, X.mul_32_64(q, b)), v(q), N.lt_succ(v(q)), {==}, {==})
  +em = m32(one, h1, m, pm)
  +hle = N.lt_succ_le(v(q1), v(m), L.subst(Nat, z => {Nat.is_lt(v(q1), z) == True{} : Bool}, C.shift(32n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), C.shift(32n, one), em), WW.lt_one(32n, one, h1, v(q1), vb(q1))))
  +hX1 = L.subst(Nat, z => {Nat.is_lt(X96(xl, xh), Nat.mul(z, SW.value(b))) == True{} : Bool}, C.shift(32n, one), 1n+v(m), Equal.sym(Nat, 1n+v(m), C.shift(32n, one), em), hX)
  +esub = U.sub_nat(m, q1, hle)
  +hf = L.subst(Nat, z => {Nat.is_lt(Nat.sub(v(m), v(q1)), 1n+z) == True{} : Bool}, Nat.sub(v(m), v(q1)), v(U32.sub(m, q1)), Equal.sym(Nat, v(U32.sub(m, q1)), Nat.sub(v(m), v(q1)), esub), N.lt_succ(Nat.sub(v(m), v(q1))))
  qup(1n+v(U32.sub(m, q1)), one, h1, xl, xh, b, q1, m, pm, q_up_okg(xl, xh, b, q1, m), hf, hle, hs, hX1, {==})

def impl_qs(+xl: WU.U64, +xh: U32, +b: WU.U64, +q: U32) -> {X.q_start(xl, xh, b, q) == QS(xl, xh, b, q, 4294967295) : U32}:
  impl_qfu(xl, xh, b, X.q_fix(1n+v(q), xl, xh, b, q, X.over96(xl, xh, X.mul_32_64(q, b))))

# ---- 64 / 64 ----

def fits_le(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}, +hy: {C.fits(k, y) == True{} : Bool}) -> {C.fits(k, x) == True{} : Bool}:
  WW.fits_of_lt(k, x, N.le_lt_trans(x, y, C.pow2(k), h, WW.lt_of_fits(k, y, hy)))

# a 96-bit value below 2^64 has top word 0: its low 64 bits are the value
def low_exact(+r: Nat, +t: Nat, +x: Nat, +e: {Nat.add(r, C.shift(64n, t)) == x : Nat}, +hr: {C.fits(64n, r) == True{} : Bool}, +hx: {C.fits(64n, x) == True{} : Bool}) -> {r == x : Nat}:
  +et = Equal.trans(Nat, t, C.high(64n, Nat.add(r, C.shift(64n, t))), 0n, Equal.sym(Nat, C.high(64n, Nat.add(r, C.shift(64n, t))), t, WW.high_u(64n, r, t, hr)), Equal.trans(Nat, C.high(64n, Nat.add(r, C.shift(64n, t))), C.high(64n, x), 0n, Equal.cong(Nat, Nat, z => C.high(64n, z), Nat.add(r, C.shift(64n, t)), x, e), N.eq_from_is_eq(C.high(64n, x), 0n, hx)))
  Equal.trans(Nat, r, Nat.add(r, C.shift(64n, 0n)), x, Equal.sym(Nat, Nat.add(r, C.shift(64n, 0n)), r, Equal.trans(Nat, Nat.add(r, C.shift(64n, 0n)), Nat.add(r, 0n), r, Equal.cong(Nat, Nat, z => Nat.add(r, z), C.shift(64n, 0n), 0n, WW.shift_zero(64n)), N.add_zero(r))), Equal.trans(Nat, Nat.add(r, C.shift(64n, 0n)), Nat.add(r, C.shift(64n, t)), x, Equal.cong(Nat, Nat, z => Nat.add(r, C.shift(64n, z)), 0n, t, Equal.sym(Nat, t, 0n, et)), e))

def pr1(-P: Type, -Q: Type, p: P & Q) -> P:
  (a, c) = p
  a

def pr2(-P: Type, -Q: Type, p: P & Q) -> Q:
  (a, c) = p
  c

def x96_0(+a: WU.U64) -> {X96(a, 0) == SW.value(a) : Nat}:
  Equal.trans(Nat, Nat.add(SW.value(a), C.shift(64n, 0n)), Nat.add(SW.value(a), 0n), SW.value(a), Equal.cong(Nat, Nat, z => Nat.add(SW.value(a), z), C.shift(64n, 0n), 0n, WW.shift_zero(64n)), N.add_zero(SW.value(a)))

def u32_0(+q: U32) -> {SW.value(WU.U64{q, 0}) == v(q) : Nat}:
  Equal.trans(Nat, Nat.add(v(q), C.shift(32n, 0n)), Nat.add(v(q), 0n), v(q), Equal.cong(Nat, Nat, z => Nat.add(v(q), z), C.shift(32n, 0n), 0n, WW.shift_zero(32n)), N.add_zero(v(q)))

# the big-divisor quotient: q b <= a < (q + 1) b
def dm_pair(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +e: U32, +hz: {U32.is_zero(bh) == False{} : Bool}, +bp: Nat, +hB: {SW.value(WU.U64{bl, bh}) == 1n+bp : Nat}) -> {Nat.div(SW.value(WU.U64{al, ah}), 1n+bp) == v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)) : Nat} & {Nat.mod(SW.value(WU.U64{al, ah}), 1n+bp) == Nat.sub(SW.value(WU.U64{al, ah}), Nat.mul(v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), 1n+bp)) : Nat}:
  +PP = C.shift(32n, one)
  +vbv = SW.value(WU.U64{bl, bh})
  +hbh = L.subst(Nat, z => {Nat.is_le(z, v(bh)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WA.pos_ne(v(bh), Equal.trans(Bool, Nat.is_eq(v(bh), 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(v(bh), 0n), LW.zero_nat(bh)), hz)))
  +hPb = N.le_trans(PP, C.shift(32n, v(bh)), vbv, WW.shift_mono(32n, one, v(bh), hbh), L.subst(Nat, z => {Nat.is_le(C.shift(32n, v(bh)), z) == True{} : Bool}, Nat.add(C.shift(32n, v(bh)), v(bl)), vbv, N.add_comm(C.shift(32n, v(bh)), v(bl)), N.le_add_right(C.shift(32n, v(bh)), v(bl))))
  +eS = Equal.trans(Nat, C.shift(64n, one), C.shift(32n, PP), Nat.mul(PP, PP), WW.shift_comp(32n, 32n, one), WW.shift_mul_one(32n, one, h1, PP))
  +ha = L.subst(Nat, z => {Nat.is_lt(SW.value(WU.U64{al, ah}), z) == True{} : Bool}, C.shift(64n, one), Nat.mul(PP, PP), eS, WW.lt_one(64n, one, h1, SW.value(WU.U64{al, ah}), fit64(WU.U64{al, ah})))
  +hX0 = N.lt_le_trans(SW.value(WU.U64{al, ah}), Nat.mul(PP, PP), Nat.mul(PP, vbv), ha, W64M.le_mul_r(PP, PP, vbv, hPb))
  +hX = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(PP, vbv)) == True{} : Bool}, SW.value(WU.U64{al, ah}), X96(WU.U64{al, ah}, 0), Equal.sym(Nat, X96(WU.U64{al, ah}, 0), SW.value(WU.U64{al, ah}), x96_0(WU.U64{al, ah})), hX0)
  pr = qs_pair(one, h1, WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295, {==}, hX)
  dv = qs_fin2(X96(WU.U64{al, ah}, 0), v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), vbv, bp, hB, pr)
  L.subst(Nat, z => {Nat.div(z, 1n+bp) == v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)) : Nat} & {Nat.mod(z, 1n+bp) == Nat.sub(z, Nat.mul(v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), 1n+bp)) : Nat}, X96(WU.U64{al, ah}, 0), SW.value(WU.U64{al, ah}), x96_0(WU.U64{al, ah}), dv)

def dm_le(+one: Nat, +h1: {one == 1n : Nat}, +al: U32, +ah: U32, +bl: U32, +bh: U32, +e: U32, +hz: {U32.is_zero(bh) == False{} : Bool}) -> {Nat.is_le(Nat.mul(v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), SW.value(WU.U64{bl, bh})), SW.value(WU.U64{al, ah})) == True{} : Bool}:
  +PP = C.shift(32n, one)
  +vbv = SW.value(WU.U64{bl, bh})
  +hbh = L.subst(Nat, z => {Nat.is_le(z, v(bh)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), WA.pos_ne(v(bh), Equal.trans(Bool, Nat.is_eq(v(bh), 0n), U32.is_zero(bh), False{}, Equal.sym(Bool, U32.is_zero(bh), Nat.is_eq(v(bh), 0n), LW.zero_nat(bh)), hz)))
  +hPb = N.le_trans(PP, C.shift(32n, v(bh)), vbv, WW.shift_mono(32n, one, v(bh), hbh), L.subst(Nat, z => {Nat.is_le(C.shift(32n, v(bh)), z) == True{} : Bool}, Nat.add(C.shift(32n, v(bh)), v(bl)), vbv, N.add_comm(C.shift(32n, v(bh)), v(bl)), N.le_add_right(C.shift(32n, v(bh)), v(bl))))
  +eS = Equal.trans(Nat, C.shift(64n, one), C.shift(32n, PP), Nat.mul(PP, PP), WW.shift_comp(32n, 32n, one), WW.shift_mul_one(32n, one, h1, PP))
  +ha = L.subst(Nat, z => {Nat.is_lt(SW.value(WU.U64{al, ah}), z) == True{} : Bool}, C.shift(64n, one), Nat.mul(PP, PP), eS, WW.lt_one(64n, one, h1, SW.value(WU.U64{al, ah}), fit64(WU.U64{al, ah})))
  +hX0 = N.lt_le_trans(SW.value(WU.U64{al, ah}), Nat.mul(PP, PP), Nat.mul(PP, vbv), ha, W64M.le_mul_r(PP, PP, vbv, hPb))
  +hX = L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(PP, vbv)) == True{} : Bool}, SW.value(WU.U64{al, ah}), X96(WU.U64{al, ah}, 0), Equal.sym(Nat, X96(WU.U64{al, ah}, 0), SW.value(WU.U64{al, ah}), x96_0(WU.U64{al, ah})), hX0)
  pr = qs_pair(one, h1, WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295, {==}, hX)
  L.subst(Nat, z => {Nat.is_le(Nat.mul(v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), vbv), z) == True{} : Bool}, X96(WU.U64{al, ah}, 0), SW.value(WU.U64{al, ah}), x96_0(WU.U64{al, ah}), qle_fin(X96(WU.U64{al, ah}, 0), v(QS(WU.U64{al, ah}, 0, WU.U64{bl, bh}, e, 4294967295)), vbv, pr))
