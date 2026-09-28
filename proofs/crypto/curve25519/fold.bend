import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as A
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./num.bend as M
import ./limbs.bend as LM
import ./poly.bend as PL

# The reduction of src/crypto/curve25519/field.bend: `pass` (a carry pass
# whose carry out c re-enters as 38 c, since 2^256 == 2 p + 38) keeps the
# value mod p, and three passes (`reduce`) take 32 limbs below 2^28 to 32
# limbs below 2^8: after the first pass the value is below 2^256 + 2^27, so
# the second carries out at most 1, which leaves the value below 2^256, so
# the third carries out 0 (TweetNaCl's car25519 argument, in radix 2^8).
#
# p is 1 + pp with (1 + pp) + 19 == 2^255 (hypothesis hP), 2^255 being
# WD.sc(255n, one) for the symbolic one == 1.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- 2^256 == 2 p + 38 ----

# A + 2^256 c == 2 c p + (A + 38 c)
def fold_id(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +a: Nat, +c: Nat) -> {Nat.add(a, LM.shn(32n, c)) == Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), Nat.add(a, Nat.mul(38n, c))) : Nat}:
  +P = {1n+pp : Nat}
  +e1 = Equal.sym(Nat, Nat.mul(c, WD.sc(256n, one)), WD.sc(256n, c), M.mul_sc_r(256n, one, h1, c))
  +e2 = Equal.trans(Nat, WD.sc(256n, one), Nat.add(WD.sc(255n, one), WD.sc(255n, one)), Nat.add(Nat.add(P, 19n), Nat.add(P, 19n)), Equal.sym(Nat, Nat.add(WD.sc(255n, one), WD.sc(255n, one)), WD.sc(256n, one), M.sc_dbl(255n, one)), M.cong_add(WD.sc(255n, one), Nat.add(P, 19n), WD.sc(255n, one), Nat.add(P, 19n), Equal.sym(Nat, Nat.add(P, 19n), WD.sc(255n, one), hP), Equal.sym(Nat, Nat.add(P, 19n), WD.sc(255n, one), hP)))
  +e3 = M.add4(P, 19n, P, 19n)
  +e4 = Equal.trans(Nat, WD.sc(256n, one), Nat.add(Nat.add(P, 19n), Nat.add(P, 19n)), Nat.add(Nat.add(P, P), 38n), e2, e3)
  +e5 = Equal.trans(Nat, Nat.mul(c, WD.sc(256n, one)), Nat.mul(c, Nat.add(Nat.add(P, P), 38n)), Nat.add(Nat.mul(c, Nat.add(P, P)), Nat.mul(c, 38n)), Equal.cong(Nat, Nat, t => Nat.mul(c, t), WD.sc(256n, one), Nat.add(Nat.add(P, P), 38n), e4), NA.mul_add_left(c, Nat.add(P, P), 38n))
  +e6 = Equal.trans(Nat, Nat.mul(c, Nat.add(P, P)), Nat.add(Nat.mul(c, P), Nat.mul(c, P)), Nat.mul(Nat.add(c, c), P), NA.mul_add_left(c, P, P), Equal.sym(Nat, Nat.mul(Nat.add(c, c), P), Nat.add(Nat.mul(c, P), Nat.mul(c, P)), NA.mul_add_right(c, c, P)))
  +e7 = M.cong_add(Nat.mul(c, Nat.add(P, P)), Nat.mul(Nat.add(c, c), P), Nat.mul(c, 38n), Nat.mul(38n, c), e6, NA.mul_comm(c, 38n))
  +q = Nat.mul(Nat.add(c, c), P)
  +r = Nat.mul(38n, c)
  +e8 = Equal.trans(Nat, WD.sc(256n, c), Nat.mul(c, WD.sc(256n, one)), Nat.add(q, r), e1, Equal.trans(Nat, Nat.mul(c, WD.sc(256n, one)), Nat.add(Nat.mul(c, Nat.add(P, P)), Nat.mul(c, 38n)), Nat.add(q, r), e5, e7))
  +e9 = M.cong_r(a, WD.sc(256n, c), Nat.add(q, r), e8)
  +e10 = Equal.trans(Nat, Nat.add(a, Nat.add(q, r)), Nat.add(q, Nat.add(a, r)), Nat.add(q, Nat.add(a, r)), NA.add_swap(a, q, r), {==})
  Equal.trans(Nat, Nat.add(a, WD.sc(256n, c)), Nat.add(a, Nat.add(q, r)), Nat.add(q, Nat.add(a, r)), e9, e10)

# ---- small bounds ----

# 38 x <= 2^6 x
def m38(+x: Nat) -> {Nat.is_le(Nat.mul(38n, x), WD.sc(6n, x)) == True{} : Bool}:
  +a = AR.mul_le(38n, 64n, x, {==})
  +b = Equal.trans(Nat, Nat.mul(64n, x), Nat.mul(x, 64n), WD.sc(6n, x), NA.mul_comm(64n, x), AR.mul_sc(6n, x))
  L.subst(Nat, z => {Nat.is_le(Nat.mul(38n, x), z) == True{} : Bool}, Nat.mul(64n, x), WD.sc(6n, x), b, a)

# 255 <= 2^27 (= 2^8 2^19)
def le255(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {Nat.is_le(255n, WD.sc(Nat.add(k, 8n), one)) == True{} : Bool}:
  +a = N.lt_le(255n, 256n, {==})
  +b = L.subst(Nat, z => {Nat.is_le(255n, z) == True{} : Bool}, 256n, WD.sc(8n, one), LM.k256(one, h1), a)
  +c = M.sc_mono(k, 8n, one)
  N.le_trans(255n, WD.sc(8n, one), WD.sc(Nat.add(k, 8n), one), b, c)

# 255 + 38 c <= 2^28 for c <= 2^21
def head_le(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +c: Nat, +hx: {Nat.is_le(x, 255n) == True{} : Bool}, +hc: {Nat.is_le(c, WD.sc(21n, one)) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, Nat.mul(38n, c)), WD.sc(28n, one)) == True{} : Bool}:
  +a = N.le_trans(x, 255n, WD.sc(27n, one), hx, le255(one, h1, 19n))
  +b0 = N.le_trans(Nat.mul(38n, c), Nat.mul(38n, WD.sc(21n, one)), WD.sc(6n, WD.sc(21n, one)), M.le_mul2(38n, c, 38n, WD.sc(21n, one), N.le_refl(38n), hc), m38(WD.sc(21n, one)))
  +s = M.le_add2(x, Nat.mul(38n, c), WD.sc(27n, one), WD.sc(27n, one), a, b0)
  L.subst(Nat, z => {Nat.is_le(Nat.add(x, Nat.mul(38n, c)), z) == True{} : Bool}, Nat.add(WD.sc(27n, one), WD.sc(27n, one)), WD.sc(28n, one), M.sc_dbl(27n, one), s)

# ---- add0 ----

def add0_val(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +xt: List<&2, U32>, +k: U32, +h: {Nat.is_lt(Nat.add(v(x), v(k)), WD.sc(32n, one)) == True{} : Bool}) -> {FS.value(F.add0(Con{x, xt}, k)) == Nat.add(FS.value(Con{x, xt}), v(k)) : Nat}:
  +X = C.shift(8n, FS.value(xt))
  +e1 = M.cong_l(v(U32.add(x, k)), Nat.add(v(x), v(k)), X, LM.add_v(one, h1, x, k, h))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(v(x), v(k)), X), Nat.add(v(x), Nat.add(v(k), X)), Nat.add(Nat.add(v(x), X), v(k)), NA.add_assoc(v(x), v(k), X), Equal.trans(Nat, Nat.add(v(x), Nat.add(v(k), X)), Nat.add(v(x), Nat.add(X, v(k))), Nat.add(Nat.add(v(x), X), v(k)), M.cong_r(v(x), Nat.add(v(k), X), Nat.add(X, v(k)), NA.add_comm(v(k), X)), Equal.sym(Nat, Nat.add(Nat.add(v(x), X), v(k)), Nat.add(v(x), Nat.add(X, v(k))), NA.add_assoc(v(x), X, v(k)))))
  Equal.trans(Nat, Nat.add(v(U32.add(x, k)), X), Nat.add(Nat.add(v(x), v(k)), X), Nat.add(Nat.add(v(x), X), v(k)), e1, e2)

def add0_zero(+xs: List<&2, U32>) -> {F.add0(xs, 0) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      Equal.cong(U32, List<&2, U32>, z => Con{z, xt}, U32.add(x, 0), x, A.add_zero(x))

# ---- one pass ----

def m38_v(+one: Nat, +h1: {one == 1n : Nat}, +c: U32, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {v(U32.mul(38, c)) == Nat.mul(38n, v(c)) : Nat}:
  +b = N.le_trans(Nat.mul(38n, v(c)), Nat.mul(38n, WD.sc(21n, one)), WD.sc(6n, WD.sc(21n, one)), M.le_mul2(38n, v(c), 38n, WD.sc(21n, one), N.le_refl(38n), hc), m38(WD.sc(21n, one)))
  LM.mul_v(one, h1, 38, c, N.le_lt_trans(Nat.mul(38n, v(c)), WD.sc(27n, one), WD.sc(32n, one), b, LM.sc_lt(4n, 27n, one, h1)))

def pass_fin_eta(+r: F.Cr) -> {F.pass_fin(r) == F.add0(LM.cl(r), U32.mul(38, LM.cc(r))) : List<&2, U32>}:
  match r:
    case F.Cr{a, c}:
      {==}

def fin_val(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +a: List<&2, U32>, +c: U32, +ha: {LM.okb(1n+m, a, 255n) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {FS.value(F.add0(a, U32.mul(38, c))) == Nat.add(FS.value(a), Nat.mul(38n, v(c))) : Nat}:
  match a:
    case Nil{}:
      Empty.absurd({0n == Nat.add(0n, Nat.mul(38n, v(c))) : Nat}, L.false_true(ha))
    case Con{+x, +xt}:
      +em = m38_v(one, h1, c, hc)
      +hb = N.le_lt_trans(Nat.add(v(x), v(U32.mul(38, c))), WD.sc(28n, one), WD.sc(32n, one), L.subst(Nat, z => {Nat.is_le(Nat.add(v(x), z), WD.sc(28n, one)) == True{} : Bool}, Nat.mul(38n, v(c)), v(U32.mul(38, c)), Equal.sym(Nat, v(U32.mul(38, c)), Nat.mul(38n, v(c)), em), head_le(one, h1, v(x), v(c), LM.okb_head(m, x, xt, 255n, ha), hc)), LM.sc_lt(3n, 28n, one, h1))
      Equal.trans(Nat, FS.value(F.add0(Con{x, xt}, U32.mul(38, c))), Nat.add(FS.value(Con{x, xt}), v(U32.mul(38, c))), Nat.add(FS.value(Con{x, xt}), Nat.mul(38n, v(c))), add0_val(one, h1, x, xt, U32.mul(38, c), hb), M.cong_r(FS.value(Con{x, xt}), v(U32.mul(38, c)), Nat.mul(38n, v(c)), em))

def fin_okb(+one: Nat, +h1: {one == 1n : Nat}, +m: Nat, +a: List<&2, U32>, +c: U32, +ha: {LM.okb(1n+m, a, 255n) == True{} : Bool}, +hc: {Nat.is_le(v(c), WD.sc(21n, one)) == True{} : Bool}) -> {LM.okb(1n+m, F.add0(a, U32.mul(38, c)), WD.sc(28n, one)) == True{} : Bool}:
  match a:
    case Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, WD.sc(28n, one)) == True{} : Bool}, L.false_true(ha))
    case Con{+x, +xt}:
      +em = m38_v(one, h1, c, hc)
      +hh = head_le(one, h1, v(x), v(c), LM.okb_head(m, x, xt, 255n, ha), hc)
      +hb = N.le_lt_trans(Nat.add(v(x), v(U32.mul(38, c))), WD.sc(28n, one), WD.sc(32n, one), L.subst(Nat, z => {Nat.is_le(Nat.add(v(x), z), WD.sc(28n, one)) == True{} : Bool}, Nat.mul(38n, v(c)), v(U32.mul(38, c)), Equal.sym(Nat, v(U32.mul(38, c)), Nat.mul(38n, v(c)), em), hh), LM.sc_lt(3n, 28n, one, h1))
      +ev = LM.add_v(one, h1, x, U32.mul(38, c), hb)
      +hd = L.subst(Nat, z => {Nat.is_le(z, WD.sc(28n, one)) == True{} : Bool}, Nat.add(v(x), Nat.mul(38n, v(c))), v(U32.add(x, U32.mul(38, c))), Equal.trans(Nat, Nat.add(v(x), Nat.mul(38n, v(c))), Nat.add(v(x), v(U32.mul(38, c))), v(U32.add(x, U32.mul(38, c))), M.cong_r(v(x), Nat.mul(38n, v(c)), v(U32.mul(38, c)), Equal.sym(Nat, v(U32.mul(38, c)), Nat.mul(38n, v(c)), em)), Equal.sym(Nat, v(U32.add(x, U32.mul(38, c))), Nat.add(v(x), v(U32.mul(38, c))), ev)), hh)
      L.and_intro(Nat.is_le(v(U32.add(x, U32.mul(38, c))), WD.sc(28n, one)), LM.okb(m, xt, WD.sc(28n, one)), hd, PL.okb_mono(m, xt, 255n, WD.sc(28n, one), le255(one, h1, 20n), LM.okb_tail(m, x, xt, 255n, ha)))

# the carry of a 32-limb input: its limbs, value and carry out
def cr_okb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {LM.okb(32n, LM.cl(F.carry(xs, 0)), 255n) == True{} : Bool}:
  LM.carry_ok(one, h1, 32n, xs, 0, hx, N.zero_le(WD.sc(21n, one)))

def cr_cb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.is_le(v(LM.cc(F.carry(xs, 0))), WD.sc(21n, one)) == True{} : Bool}:
  LM.carry_cb(one, h1, xs, 0, LM.okb_lea(32n, xs, WD.sc(28n, one), hx), N.zero_le(WD.sc(21n, one)))

def cr_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.add(FS.value(LM.cl(F.carry(xs, 0))), LM.shn(32n, v(LM.cc(F.carry(xs, 0))))) == FS.value(xs) : Nat}:
  +r = F.carry(xs, 0)
  +e = LM.carry_val(one, h1, xs, 0, LM.okb_lea(32n, xs, WD.sc(28n, one), hx), N.zero_le(WD.sc(21n, one)))
  %LM.sh_okb(32n, xs, WD.sc(28n, one), v(LM.cc(r)), hx) : {Nat.add(FS.value(LM.cl(r)), _) == FS.value(xs) : Nat}
  Equal.trans(Nat, Nat.add(FS.value(LM.cl(r)), LM.sh(xs, v(LM.cc(r)))), Nat.add(FS.value(xs), 0n), FS.value(xs), e, N.add_zero(FS.value(xs)))

def pass_val(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {FS.value(F.pass(xs)) == Nat.add(FS.value(LM.cl(F.carry(xs, 0))), Nat.mul(38n, v(LM.cc(F.carry(xs, 0))))) : Nat}:
  +r = F.carry(xs, 0)
  %Equal.sym(List<&2, U32>, F.pass_fin(r), F.add0(LM.cl(r), U32.mul(38, LM.cc(r))), pass_fin_eta(r)) : {FS.value(_) == Nat.add(FS.value(LM.cl(r)), Nat.mul(38n, v(LM.cc(r)))) : Nat}
  fin_val(one, h1, 31n, LM.cl(r), LM.cc(r), cr_okb(one, h1, xs, hx), cr_cb(one, h1, xs, hx))

def pass_okb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {LM.okb(32n, F.pass(xs), WD.sc(28n, one)) == True{} : Bool}:
  +r = F.carry(xs, 0)
  %Equal.sym(List<&2, U32>, F.pass_fin(r), F.add0(LM.cl(r), U32.mul(38, LM.cc(r))), pass_fin_eta(r)) : {LM.okb(32n, _, WD.sc(28n, one)) == True{} : Bool}
  fin_okb(one, h1, 31n, LM.cl(r), LM.cc(r), cr_okb(one, h1, xs, hx), cr_cb(one, h1, xs, hx))

# value(xs) == 2 c p + value(pass(xs))
def pass_fold(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {FS.value(xs) == Nat.add(Nat.mul(Nat.add(v(LM.cc(F.carry(xs, 0))), v(LM.cc(F.carry(xs, 0)))), 1n+pp), FS.value(F.pass(xs))) : Nat}:
  +r = F.carry(xs, 0)
  +a = FS.value(LM.cl(r))
  +c = v(LM.cc(r))
  +e1 = Equal.sym(Nat, Nat.add(a, LM.shn(32n, c)), FS.value(xs), cr_val(one, h1, xs, hx))
  +e2 = fold_id(one, h1, pp, hP, a, c)
  +e3 = M.cong_r(Nat.mul(Nat.add(c, c), 1n+pp), Nat.add(a, Nat.mul(38n, c)), FS.value(F.pass(xs)), Equal.sym(Nat, FS.value(F.pass(xs)), Nat.add(a, Nat.mul(38n, c)), pass_val(one, h1, xs, hx)))
  Equal.trans(Nat, FS.value(xs), Nat.add(a, LM.shn(32n, c)), Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), FS.value(F.pass(xs))), e1, Equal.trans(Nat, Nat.add(a, LM.shn(32n, c)), Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), Nat.add(a, Nat.mul(38n, c))), Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), FS.value(F.pass(xs))), e2, e3))

def pass_mod(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.mod(FS.value(F.pass(xs)), 1n+pp) == Nat.mod(FS.value(xs), 1n+pp) : Nat}:
  +c = v(LM.cc(F.carry(xs, 0)))
  %Equal.sym(Nat, FS.value(xs), Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), FS.value(F.pass(xs))), pass_fold(one, h1, pp, hP, xs, hx)) : {Nat.mod(FS.value(F.pass(xs)), 1n+pp) == Nat.mod(_, 1n+pp) : Nat}
  Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Nat.add(c, c), 1n+pp), FS.value(F.pass(xs))), 1n+pp), Nat.mod(FS.value(F.pass(xs)), 1n+pp), NR.absorb(pp, Nat.add(c, c), FS.value(F.pass(xs))))
