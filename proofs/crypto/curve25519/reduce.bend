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
import ./fold.bend as FD

# reduce = three passes: from 32 limbs below 2^28 to 32 limbs below 2^8,
# the value kept mod p. T = 2^(8 * 32) = LM.shn(32n, one).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# value(xs) < 2^(8 n) for n limbs below 2^8
def val_lt(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +e: {LM.okb(n, xs, 255n) == True{} : Bool}) -> {Nat.is_lt(FS.value(xs), LM.shn(n, one)) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      L.subst(Nat, o => {Nat.is_lt(0n, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
    case 0n Con{y, yt}:
      Empty.absurd({Nat.is_lt(FS.value(Con{y, yt}), one) == True{} : Bool}, L.false_true(e))
    case 1n+m Nil{}:
      Empty.absurd({Nat.is_lt(0n, LM.shn(1n+m, one)) == True{} : Bool}, L.false_true(e))
    case 1n+ +m Con{+y, +yt}:
      +X = FS.value(yt)
      +ih = val_lt(one, h1, m, yt, LM.okb_tail(m, y, yt, 255n, e))
      +a = M.le_sc(8n, 1n+X, LM.shn(m, one), N.lt_succ_le_succ(X, LM.shn(m, one), ih))
      +b = L.subst(Nat, z => {Nat.is_le(z, C.shift(8n, LM.shn(m, one))) == True{} : Bool}, WD.sc(8n, 1n+X), Nat.add(256n, C.shift(8n, X)), A.sc_succ(8n, X), a)
      +c = N.lt_add_r2(v(y), 256n, C.shift(8n, X), N.le_lt_succ(v(y), 255n, LM.okb_head(m, y, yt, 255n, e)))
      N.lt_le_trans(Nat.add(v(y), C.shift(8n, X)), Nat.add(256n, C.shift(8n, X)), C.shift(8n, LM.shn(m, one)), c, b)

# a + t < b + t -> a < b
def lt_cancel_r(+a: Nat, +b: Nat, +t: Nat, +h: {Nat.is_lt(Nat.add(a, t), Nat.add(b, t)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  +h1 = N.lt_succ_le_succ(Nat.add(a, t), Nat.add(b, t), h)
  +h2 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(b, t)) == True{} : Bool}, 1n+Nat.add(a, t), Nat.add(1n+a, t), {==}, h1)
  +h3 = L.subst(Nat, z => {Nat.is_le(z, Nat.add(b, t)) == True{} : Bool}, Nat.add(1n+a, t), Nat.add(t, 1n+a), NA.add_comm(1n+a, t), h2)
  +h4 = L.subst(Nat, z => {Nat.is_le(Nat.add(t, 1n+a), z) == True{} : Bool}, Nat.add(b, t), Nat.add(t, b), NA.add_comm(b, t), h3)
  +h5 = L.subst(Bool, z => {z == True{} : Bool}, Nat.is_le(Nat.add(t, 1n+a), Nat.add(t, b)), Nat.is_le(1n+a, b), NR.le_add_cancel(t, 1n+a, b), h4)
  N.succ_le_lt(a, b, h5)

# 2^256 c >= 2^256 when c >= 1
def shn_ge(+one: Nat, +c: Nat, +h: {Nat.is_le(one, c) == True{} : Bool}) -> {Nat.is_le(LM.shn(32n, one), LM.shn(32n, c)) == True{} : Bool}:
  AR.sc_le(256n, one, c, h)

# 2^256 c < 2^256 2 -> c < 2
def shn_lt_cancel(+c: Nat, +d: Nat, +h: {Nat.is_lt(LM.shn(32n, c), LM.shn(32n, d)) == True{} : Bool}) -> {Nat.is_lt(c, d) == True{} : Bool}:
  AR.sc_lt_cancel(256n, c, d, h)

# K = 2^27; K + 38 <= 2^256 and K < 2^256
def k_le_t(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(WD.sc(27n, one), LM.shn(32n, one)) == True{} : Bool}:
  M.sc_mono(229n, 27n, one)

def k38_le_t(+one: Nat, +h1: {one == 1n : Nat}) -> {Nat.is_le(Nat.add(WD.sc(27n, one), 38n), LM.shn(32n, one)) == True{} : Bool}:
  +a = N.le_trans(38n, 255n, WD.sc(27n, one), {==}, FD.le255(one, h1, 19n))
  +b = M.le_add2(WD.sc(27n, one), 38n, WD.sc(27n, one), WD.sc(27n, one), N.le_refl(WD.sc(27n, one)), a)
  +c = L.subst(Nat, z => {Nat.is_le(Nat.add(WD.sc(27n, one), 38n), z) == True{} : Bool}, Nat.add(WD.sc(27n, one), WD.sc(27n, one)), WD.sc(28n, one), M.sc_dbl(27n, one), b)
  N.le_trans(Nat.add(WD.sc(27n, one), 38n), WD.sc(28n, one), LM.shn(32n, one), c, M.sc_mono(228n, 28n, one))

# case c < 1 (so c == 0): a + 38 c == a < T
def small_zero(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +c: Nat, +ha: {Nat.is_lt(a, LM.shn(32n, one)) == True{} : Bool}, +hc: {Nat.is_lt(c, one) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, Nat.mul(38n, c)), LM.shn(32n, one)) == True{} : Bool}:
  +c0 = U.lt_one_zero(c, L.subst(Nat, o => {Nat.is_lt(c, o) == True{} : Bool}, one, 1n, h1, hc))
  %Equal.cong(Nat, Nat, z => Nat.add(a, Nat.mul(38n, z)), 0n, c, Equal.sym(Nat, c, 0n, c0)) : {Nat.is_lt(_, LM.shn(32n, one)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(a, 0n), a, N.add_zero(a)) : {Nat.is_lt(_, LM.shn(32n, one)) == True{} : Bool}
  ha

# case c >= 1: then a < K and c == 1, so a + 38 < K + 38 <= T
def small_one(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +c: Nat, +V: Nat, +hv: {Nat.add(a, LM.shn(32n, c)) == V : Nat}, +hV: {Nat.is_lt(V, Nat.add(LM.shn(32n, one), WD.sc(27n, one))) == True{} : Bool}, +hc: {Nat.is_le(one, c) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, Nat.mul(38n, c)), LM.shn(32n, one)) == True{} : Bool}:
  +T = LM.shn(32n, one)
  +K = WD.sc(27n, one)
  +s = LM.shn(32n, c)
  +hs = shn_ge(one, c, hc)
  +v1 = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(T, K)) == True{} : Bool}, V, Nat.add(a, s), Equal.sym(Nat, Nat.add(a, s), V, hv), hV)
  +v2 = N.le_lt_trans(Nat.add(a, T), Nat.add(a, s), Nat.add(T, K), N.le_add_left(T, s, a, hs), v1)
  +v3 = L.subst(Nat, z => {Nat.is_lt(Nat.add(a, T), z) == True{} : Bool}, Nat.add(T, K), Nat.add(K, T), NA.add_comm(T, K), v2)
  +ak = lt_cancel_r(a, K, T, v3)
  +w1 = N.le_lt_trans(s, Nat.add(a, s), Nat.add(T, K), PL.le_add_l(a, s), v1)
  +w2 = N.lt_le_trans(s, Nat.add(T, K), Nat.add(T, T), w1, N.le_add_left(K, T, T, k_le_t(one, h1)))
  +w3 = L.subst(Nat, z => {Nat.is_lt(s, z) == True{} : Bool}, Nat.add(T, T), LM.shn(32n, Nat.add(one, one)), M.sc_add(256n, one, one), w2)
  +c2 = shn_lt_cancel(c, Nat.add(one, one), w3)
  +c2b = L.subst(Nat, o => {Nat.is_lt(c, Nat.add(o, o)) == True{} : Bool}, one, 1n, h1, c2)
  +cle = L.subst(Nat, o => {Nat.is_le(c, o) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), N.lt_succ_le(c, 1n, c2b))
  +ce = N.le_antisym(c, one, cle, hc)
  +m1 = L.subst(Nat, o => {Nat.mul(38n, o) == 38n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  %Equal.cong(Nat, Nat, z => Nat.add(a, Nat.mul(38n, z)), one, c, Equal.sym(Nat, c, one, ce)) : {Nat.is_lt(_, T) == True{} : Bool}
  %M.cong_r(a, 38n, Nat.mul(38n, one), Equal.sym(Nat, Nat.mul(38n, one), 38n, m1)) : {Nat.is_lt(_, T) == True{} : Bool}
  N.lt_le_trans(Nat.add(a, 38n), Nat.add(K, 38n), T, N.lt_add_r2(a, K, 38n, ak), k38_le_t(one, h1))

def small_by(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +c: Nat, +V: Nat, +b: Bool, +hb: {Nat.is_lt(c, one) == b : Bool}, +ha: {Nat.is_lt(a, LM.shn(32n, one)) == True{} : Bool}, +hv: {Nat.add(a, LM.shn(32n, c)) == V : Nat}, +hV: {Nat.is_lt(V, Nat.add(LM.shn(32n, one), WD.sc(27n, one))) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, Nat.mul(38n, c)), LM.shn(32n, one)) == True{} : Bool}:
  match b:
    case True{}:
      small_zero(one, h1, a, c, ha, hb)
    case False{}:
      small_one(one, h1, a, c, V, hv, hV, N.not_lt_le(c, one, hb))

# after two passes the value is below 2^256
def two_lt(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.is_lt(FS.value(F.pass(F.pass(xs))), LM.shn(32n, one)) == True{} : Bool}:
  +T = LM.shn(32n, one)
  +K = WD.sc(27n, one)
  +r1 = F.carry(xs, 0)
  +a1 = FS.value(LM.cl(r1))
  +c1 = v(LM.cc(r1))
  +y1 = F.pass(xs)
  +hy1 = FD.pass_okb(one, h1, xs, hx)
  +la = val_lt(one, h1, 32n, LM.cl(r1), FD.cr_okb(one, h1, xs, hx))
  +lc = N.le_trans(Nat.mul(38n, c1), Nat.mul(38n, WD.sc(21n, one)), WD.sc(6n, WD.sc(21n, one)), M.le_mul2(38n, c1, 38n, WD.sc(21n, one), N.le_refl(38n), FD.cr_cb(one, h1, xs, hx)), FD.m38(WD.sc(21n, one)))
  +l1 = N.lt_le_trans(Nat.add(a1, Nat.mul(38n, c1)), Nat.add(T, Nat.mul(38n, c1)), Nat.add(T, K), N.lt_add_r2(a1, T, Nat.mul(38n, c1), la), N.le_add_left(Nat.mul(38n, c1), K, T, lc))
  +hV = L.subst(Nat, z => {Nat.is_lt(z, Nat.add(T, K)) == True{} : Bool}, Nat.add(a1, Nat.mul(38n, c1)), FS.value(y1), Equal.sym(Nat, FS.value(y1), Nat.add(a1, Nat.mul(38n, c1)), FD.pass_val(one, h1, xs, hx)), l1)
  +r2 = F.carry(y1, 0)
  +a2 = FS.value(LM.cl(r2))
  +c2 = v(LM.cc(r2))
  +la2 = val_lt(one, h1, 32n, LM.cl(r2), FD.cr_okb(one, h1, y1, hy1))
  +lt2 = small_by(one, h1, a2, c2, FS.value(y1), Nat.is_lt(c2, one), {==}, la2, FD.cr_val(one, h1, y1, hy1), hV)
  L.subst(Nat, z => {Nat.is_lt(z, T) == True{} : Bool}, Nat.add(a2, Nat.mul(38n, c2)), FS.value(F.pass(y1)), Equal.sym(Nat, FS.value(F.pass(y1)), Nat.add(a2, Nat.mul(38n, c2)), FD.pass_val(one, h1, y1, hy1)), lt2)

# a pass of a value below 2^256 carries out 0: the output is the carry's limbs
def last_zero(+one: Nat, +h1: {one == 1n : Nat}, +a: Nat, +c: Nat, +V: Nat, +hv: {Nat.add(a, LM.shn(32n, c)) == V : Nat}, +hV: {Nat.is_lt(V, LM.shn(32n, one)) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(c, one) == b : Bool}) -> {c == 0n : Nat}:
  match b:
    case True{}:
      U.lt_one_zero(c, L.subst(Nat, o => {Nat.is_lt(c, o) == True{} : Bool}, one, 1n, h1, hb))
    case False{}:
      +hs = shn_ge(one, c, N.not_lt_le(c, one, hb))
      +x = N.le_trans(LM.shn(32n, one), LM.shn(32n, c), V, hs, L.subst(Nat, z => {Nat.is_le(LM.shn(32n, c), z) == True{} : Bool}, Nat.add(a, LM.shn(32n, c)), V, hv, PL.le_add_l(a, LM.shn(32n, c))))
      Empty.absurd({c == 0n : Nat}, L.true_not_false(Nat.is_lt(V, LM.shn(32n, one)), hV, N.le_not_lt(V, LM.shn(32n, one), x)))

def pass_exact(+r: F.Cr, +hc: {LM.cc(r) == 0 : U32}) -> {F.pass_fin(r) == LM.cl(r) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, F.pass_fin(r), F.add0(LM.cl(r), U32.mul(38, LM.cc(r))), FD.pass_fin_eta(r)) : {_ == LM.cl(r) : List<&2, U32>}
  %Equal.cong(U32, List<&2, U32>, z => F.add0(LM.cl(r), U32.mul(38, z)), 0, LM.cc(r), Equal.sym(U32, LM.cc(r), 0, hc)) : {_ == LM.cl(r) : List<&2, U32>}
  FD.add0_zero(LM.cl(r))

# reduce gives 32 limbs below 2^8
def reduce_okb(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {LM.okb(32n, F.reduce(xs), 255n) == True{} : Bool}:
  +y2 = F.pass(F.pass(xs))
  +hy2 = FD.pass_okb(one, h1, F.pass(xs), FD.pass_okb(one, h1, xs, hx))
  +r3 = F.carry(y2, 0)
  +c3 = v(LM.cc(r3))
  +z = last_zero(one, h1, FS.value(LM.cl(r3)), c3, FS.value(y2), FD.cr_val(one, h1, y2, hy2), two_lt(one, h1, xs, hx), Nat.is_lt(c3, one), {==})
  +cz = U.injective(LM.cc(r3), 0, z)
  %Equal.sym(List<&2, U32>, F.pass_fin(r3), LM.cl(r3), pass_exact(r3, cz)) : {LM.okb(32n, _, 255n) == True{} : Bool}
  FD.cr_okb(one, h1, y2, hy2)

def reduce_mod(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +xs: List<&2, U32>, +hx: {LM.okb(32n, xs, WD.sc(28n, one)) == True{} : Bool}) -> {Nat.mod(FS.value(F.reduce(xs)), 1n+pp) == Nat.mod(FS.value(xs), 1n+pp) : Nat}:
  +y1 = F.pass(xs)
  +hy1 = FD.pass_okb(one, h1, xs, hx)
  +y2 = F.pass(y1)
  +hy2 = FD.pass_okb(one, h1, y1, hy1)
  Equal.trans(Nat, Nat.mod(FS.value(F.pass(y2)), 1n+pp), Nat.mod(FS.value(y2), 1n+pp), Nat.mod(FS.value(xs), 1n+pp), FD.pass_mod(one, h1, pp, hP, y2, hy2),
    Equal.trans(Nat, Nat.mod(FS.value(y2), 1n+pp), Nat.mod(FS.value(y1), 1n+pp), Nat.mod(FS.value(xs), 1n+pp), FD.pass_mod(one, h1, pp, hP, y1, hy1), FD.pass_mod(one, h1, pp, hP, xs, hx)))
