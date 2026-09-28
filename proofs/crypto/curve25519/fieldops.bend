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
import ../../lib/u32div.bend as UD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./num.bend as M
import ./limbs.bend as LM
import ./poly.bend as PL
import ./fold.bend as FD
import ./reduce.bend as RD
import ./consts.bend as K

# add, sub and select of src/crypto/curve25519/field.bend on tight
# elements (32 limbs below 2^8): the result is tight and its value is the
# sum / difference mod p.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# every limb at least b
def gea(xs: List<&2, U32>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      Bool.and(Nat.is_le(b, U32.to_nat(x)), gea(xt, b))

# 255 + 255 and 255 + 2040 are below 2^28
def le_small(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_le(x, 4096n) == True{} : Bool}) -> {Nat.is_le(x, WD.sc(28n, one)) == True{} : Bool}:
  +a = L.subst(Nat, o => {Nat.is_le(4096n, WD.sc(12n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
  N.le_trans(x, WD.sc(12n, one), WD.sc(28n, one), N.le_trans(x, 4096n, WD.sc(12n, one), hx, a), M.sc_mono(16n, 12n, one))

def lt32_small(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat, +hx: {Nat.is_le(x, 4096n) == True{} : Bool}) -> {Nat.is_lt(x, WD.sc(32n, one)) == True{} : Bool}:
  N.le_lt_trans(x, WD.sc(28n, one), WD.sc(32n, one), le_small(one, h1, x, hx), LM.sc_lt(3n, 28n, one, h1))

# ---- add ----

def addl_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.addl(a, b), WD.sc(28n, one)) == True{} : Bool}:
  +e = PL.addl_okb(one, h1, 32n, a, b, 255n, 255n, ha, LM.okb_lea(32n, b, 255n, hb), PL.okb_len_le(32n, b, 255n, hb), lt32_small(one, h1, Nat.add(255n, 255n), {==}))
  PL.okb_mono(32n, F.addl(a, b), Nat.add(255n, 255n), WD.sc(28n, one), le_small(one, h1, Nat.add(255n, 255n), {==}), e)

def add_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.add(a, b), 255n) == True{} : Bool}:
  RD.reduce_okb(one, h1, F.addl(a, b), addl_okb(one, h1, a, b, ha, hb))

def add_mod(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {Nat.mod(FS.value(F.add(a, b)), 1n+pp) == Nat.mod(Nat.add(FS.value(a), FS.value(b)), 1n+pp) : Nat}:
  +e1 = RD.reduce_mod(one, h1, pp, hP, F.addl(a, b), addl_okb(one, h1, a, b, ha, hb))
  +e2 = M.cong_mod(1n+pp, FS.value(F.addl(a, b)), Nat.add(FS.value(a), FS.value(b)), PL.addl_val(one, h1, a, b, 255n, 255n, LM.okb_lea(32n, a, 255n, ha), LM.okb_lea(32n, b, 255n, hb), lt32_small(one, h1, Nat.add(255n, 255n), {==})))
  Equal.trans(Nat, Nat.mod(FS.value(F.add(a, b)), 1n+pp), Nat.mod(FS.value(F.addl(a, b)), 1n+pp), Nat.mod(Nat.add(FS.value(a), FS.value(b)), 1n+pp), e1, e2)

# ---- sub ----

def gea_head(+h: U32, +t: List<&2, U32>, +b: Nat, +e: {gea(Con{h, t}, b) == True{} : Bool}) -> {Nat.is_le(b, v(h)) == True{} : Bool}:
  L.and_left(Nat.is_le(b, v(h)), gea(t, b), e)

def gea_tail(+h: U32, +t: List<&2, U32>, +b: Nat, +e: {gea(Con{h, t}, b) == True{} : Bool}) -> {gea(t, b) == True{} : Bool}:
  L.and_right(Nat.is_le(b, v(h)), gea(t, b), e)

# one limb: (x + k) - y with y <= k, no wrap
def subl_v(+one: Nat, +h1: {one == 1n : Nat}, +x: U32, +y: U32, +k: U32, +bx: Nat, +by: Nat, +bk: Nat, +hx: {Nat.is_le(v(x), bx) == True{} : Bool}, +hy: {Nat.is_le(v(y), by) == True{} : Bool}, +hk: {Nat.is_le(v(k), bk) == True{} : Bool}, +hg: {Nat.is_le(by, v(k)) == True{} : Bool}, +hb: {Nat.is_lt(Nat.add(bx, bk), WD.sc(32n, one)) == True{} : Bool}) -> {Nat.add(v(U32.sub(U32.add(x, k), y)), v(y)) == Nat.add(v(x), v(k)) : Nat}:
  +ea = PL.addl_v(one, h1, x, k, bx, bk, hx, hk, hb)
  +yk = N.le_trans(v(y), by, v(k), hy, hg)
  +yl = N.le_trans(v(y), v(k), Nat.add(v(x), v(k)), yk, PL.le_add_l(v(x), v(k)))
  +yl2 = L.subst(Nat, z => {Nat.is_le(v(y), z) == True{} : Bool}, Nat.add(v(x), v(k)), v(U32.add(x, k)), Equal.sym(Nat, v(U32.add(x, k)), Nat.add(v(x), v(k)), ea), yl)
  +es = U.sub_nat(U32.add(x, k), y, yl2)
  +e1 = M.cong_l(v(U32.sub(U32.add(x, k), y)), Nat.sub(v(U32.add(x, k)), v(y)), v(y), es)
  +e2 = Equal.trans(Nat, Nat.add(Nat.sub(v(U32.add(x, k)), v(y)), v(y)), Nat.add(v(y), Nat.sub(v(U32.add(x, k)), v(y))), v(U32.add(x, k)), NA.add_comm(Nat.sub(v(U32.add(x, k)), v(y)), v(y)), N.sub_add(v(U32.add(x, k)), v(y), yl2))
  Equal.trans(Nat, Nat.add(v(U32.sub(U32.add(x, k), y)), v(y)), Nat.add(Nat.sub(v(U32.add(x, k)), v(y)), v(y)), Nat.add(v(x), v(k)), e1, Equal.trans(Nat, Nat.add(Nat.sub(v(U32.add(x, k)), v(y)), v(y)), v(U32.add(x, k)), Nat.add(v(x), v(k)), e2, ea))

def subl_val(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +ks: List<&2, U32>, +bx: Nat, +by: Nat, +bk: Nat, +hx: {LM.okb(n, xs, bx) == True{} : Bool}, +hy: {LM.okb(n, ys, by) == True{} : Bool}, +hk: {LM.okb(n, ks, bk) == True{} : Bool}, +hg: {gea(ks, by) == True{} : Bool}, +hb: {Nat.is_lt(Nat.add(bx, bk), WD.sc(32n, one)) == True{} : Bool}) -> {Nat.add(FS.value(F.subl(xs, ys, ks)), FS.value(ys)) == Nat.add(FS.value(xs), FS.value(ks)) : Nat}:
  match n xs ys ks:
    case 0n Nil{} Nil{} Nil{}:
      {==}
    case 0n Nil{} Nil{} Con{k, kt}:
      Empty.absurd({Nat.add(0n, 0n) == Nat.add(0n, FS.value(Con{k, kt})) : Nat}, L.false_true(hk))
    case 0n Nil{} Con{y, yt} _:
      Empty.absurd({Nat.add(0n, FS.value(Con{y, yt})) == Nat.add(0n, FS.value(ks)) : Nat}, L.false_true(hy))
    case 0n Con{x, xt} _ _:
      Empty.absurd({Nat.add(FS.value(F.subl(Con{x, xt}, ys, ks)), FS.value(ys)) == Nat.add(FS.value(Con{x, xt}), FS.value(ks)) : Nat}, L.false_true(hx))
    case 1n+m Nil{} _ _:
      Empty.absurd({Nat.add(0n, FS.value(ys)) == Nat.add(0n, FS.value(ks)) : Nat}, L.false_true(hx))
    case 1n+m Con{x, xt} Nil{} _:
      Empty.absurd({Nat.add(0n, 0n) == Nat.add(FS.value(Con{x, xt}), FS.value(ks)) : Nat}, L.false_true(hy))
    case 1n+m Con{x, xt} Con{y, yt} Nil{}:
      Empty.absurd({Nat.add(0n, FS.value(Con{y, yt})) == Nat.add(FS.value(Con{x, xt}), 0n) : Nat}, L.false_true(hk))
    case 1n+ +m Con{+x, +xt} Con{+y, +yt} Con{+k, +kt}:
      +s = U32.sub(U32.add(x, k), y)
      +S = FS.value(F.subl(xt, yt, kt))
      +Y = FS.value(yt)
      +X = FS.value(xt)
      +KK = FS.value(kt)
      +el = subl_v(one, h1, x, y, k, bx, by, bk, LM.okb_head(m, x, xt, bx, hx), LM.okb_head(m, y, yt, by, hy), LM.okb_head(m, k, kt, bk, hk), gea_head(k, kt, by, hg), hb)
      +ih = subl_val(one, h1, m, xt, yt, kt, bx, by, bk, LM.okb_tail(m, x, xt, bx, hx), LM.okb_tail(m, y, yt, by, hy), LM.okb_tail(m, k, kt, bk, hk), gea_tail(k, kt, by, hg), hb)
      +e1 = M.add4(v(s), C.shift(8n, S), v(y), C.shift(8n, Y))
      +e2 = M.cong_add(Nat.add(v(s), v(y)), Nat.add(v(x), v(k)), Nat.add(C.shift(8n, S), C.shift(8n, Y)), C.shift(8n, Nat.add(X, KK)), el, Equal.trans(Nat, Nat.add(C.shift(8n, S), C.shift(8n, Y)), C.shift(8n, Nat.add(S, Y)), C.shift(8n, Nat.add(X, KK)), M.sc_add(8n, S, Y), M.cong_sc(8n, Nat.add(S, Y), Nat.add(X, KK), ih)))
      +e3 = Equal.trans(Nat, Nat.add(Nat.add(v(x), v(k)), C.shift(8n, Nat.add(X, KK))), Nat.add(Nat.add(v(x), v(k)), Nat.add(C.shift(8n, X), C.shift(8n, KK))), Nat.add(Nat.add(v(x), C.shift(8n, X)), Nat.add(v(k), C.shift(8n, KK))), M.cong_r(Nat.add(v(x), v(k)), C.shift(8n, Nat.add(X, KK)), Nat.add(C.shift(8n, X), C.shift(8n, KK)), Equal.sym(Nat, Nat.add(C.shift(8n, X), C.shift(8n, KK)), C.shift(8n, Nat.add(X, KK)), M.sc_add(8n, X, KK))), M.add4(v(x), v(k), C.shift(8n, X), C.shift(8n, KK)))
      Equal.trans(Nat, Nat.add(Nat.add(v(s), C.shift(8n, S)), Nat.add(v(y), C.shift(8n, Y))), Nat.add(Nat.add(v(s), v(y)), Nat.add(C.shift(8n, S), C.shift(8n, Y))), Nat.add(Nat.add(v(x), C.shift(8n, X)), Nat.add(v(k), C.shift(8n, KK))), e1, Equal.trans(Nat, Nat.add(Nat.add(v(s), v(y)), Nat.add(C.shift(8n, S), C.shift(8n, Y))), Nat.add(Nat.add(v(x), v(k)), C.shift(8n, Nat.add(X, KK))), Nat.add(Nat.add(v(x), C.shift(8n, X)), Nat.add(v(k), C.shift(8n, KK))), e2, e3))

def subl_okb(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +ks: List<&2, U32>, +bx: Nat, +by: Nat, +bk: Nat, +hx: {LM.okb(n, xs, bx) == True{} : Bool}, +hy: {LM.okb(n, ys, by) == True{} : Bool}, +hk: {LM.okb(n, ks, bk) == True{} : Bool}, +hg: {gea(ks, by) == True{} : Bool}, +hb: {Nat.is_lt(Nat.add(bx, bk), WD.sc(32n, one)) == True{} : Bool}) -> {LM.okb(n, F.subl(xs, ys, ks), Nat.add(bx, bk)) == True{} : Bool}:
  match n xs ys ks:
    case 0n Nil{} _ _:
      {==}
    case 0n Con{x, xt} _ _:
      Empty.absurd({LM.okb(0n, F.subl(Con{x, xt}, ys, ks), Nat.add(bx, bk)) == True{} : Bool}, L.false_true(hx))
    case 1n+m Nil{} _ _:
      Empty.absurd({LM.okb(1n+m, Nil{}, Nat.add(bx, bk)) == True{} : Bool}, L.false_true(hx))
    case 1n+m Con{x, xt} Nil{} _:
      Empty.absurd({LM.okb(1n+m, Nil{}, Nat.add(bx, bk)) == True{} : Bool}, L.false_true(hy))
    case 1n+m Con{x, xt} Con{y, yt} Nil{}:
      Empty.absurd({LM.okb(1n+m, Nil{}, Nat.add(bx, bk)) == True{} : Bool}, L.false_true(hk))
    case 1n+ +m Con{+x, +xt} Con{+y, +yt} Con{+k, +kt}:
      +s = U32.sub(U32.add(x, k), y)
      +hxh = LM.okb_head(m, x, xt, bx, hx)
      +hkh = LM.okb_head(m, k, kt, bk, hk)
      +el = subl_v(one, h1, x, y, k, bx, by, bk, hxh, LM.okb_head(m, y, yt, by, hy), hkh, gea_head(k, kt, by, hg), hb)
      +le1 = L.subst(Nat, z => {Nat.is_le(v(s), z) == True{} : Bool}, Nat.add(v(s), v(y)), Nat.add(v(x), v(k)), el, N.le_add_right(v(s), v(y)))
      +le2 = N.le_trans(v(s), Nat.add(v(x), v(k)), Nat.add(bx, bk), le1, M.le_add2(v(x), v(k), bx, bk, hxh, hkh))
      L.and_intro(Nat.is_le(v(s), Nat.add(bx, bk)), LM.okb(m, F.subl(xt, yt, kt), Nat.add(bx, bk)), le2, subl_okb(one, h1, m, xt, yt, kt, bx, by, bk, LM.okb_tail(m, x, xt, bx, hx), LM.okb_tail(m, y, yt, by, hy), LM.okb_tail(m, k, kt, bk, hk), gea_tail(k, kt, by, hg), hb))

# S + B == A + 8 P gives S == (A + P - (B mod P)) mod P, mod P
def sub_core(+pp: Nat, +A: Nat, +B: Nat, +S: Nat, +hS: {Nat.add(S, B) == Nat.add(A, Nat.mul(8n, 1n+pp)) : Nat}) -> {Nat.mod(S, 1n+pp) == Nat.mod(Nat.sub(Nat.add(A, 1n+pp), Nat.mod(B, 1n+pp)), 1n+pp) : Nat}:
  +P = {1n+pp : Nat}
  +q = Nat.div(B, P)
  +r = Nat.mod(B, P)
  +W = Nat.sub(Nat.add(A, P), r)
  +hB = NR.dm_eq(pp, B)
  +rle = N.le_trans(r, P, Nat.add(A, P), N.lt_le(r, P, NR.dm_lt(pp, B)), PL.le_add_l(A, P))
  +hW = Equal.trans(Nat, Nat.add(W, r), Nat.add(r, W), Nat.add(A, P), NA.add_comm(W, r), N.sub_add(Nat.add(A, P), r, rle))
  +x1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(q, P), S), r), Nat.add(S, Nat.add(Nat.mul(q, P), r)), Nat.add(A, Nat.mul(8n, P)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(q, P), S), r), Nat.add(Nat.add(S, Nat.mul(q, P)), r), Nat.add(S, Nat.add(Nat.mul(q, P), r)), M.cong_l(Nat.add(Nat.mul(q, P), S), Nat.add(S, Nat.mul(q, P)), r, NA.add_comm(Nat.mul(q, P), S)), NA.add_assoc(S, Nat.mul(q, P), r)),
    Equal.trans(Nat, Nat.add(S, Nat.add(Nat.mul(q, P), r)), Nat.add(S, B), Nat.add(A, Nat.mul(8n, P)), M.cong_r(S, Nat.add(Nat.mul(q, P), r), B, Equal.sym(Nat, B, Nat.add(Nat.mul(q, P), r), hB)), hS))
  +x2 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(7n, P), W), r), Nat.add(Nat.mul(7n, P), Nat.add(W, r)), Nat.add(A, Nat.mul(8n, P)), NA.add_assoc(Nat.mul(7n, P), W, r),
    Equal.trans(Nat, Nat.add(Nat.mul(7n, P), Nat.add(W, r)), Nat.add(Nat.mul(7n, P), Nat.add(A, P)), Nat.add(A, Nat.mul(8n, P)), M.cong_r(Nat.mul(7n, P), Nat.add(W, r), Nat.add(A, P), hW),
      Equal.trans(Nat, Nat.add(Nat.mul(7n, P), Nat.add(A, P)), Nat.add(A, Nat.add(Nat.mul(7n, P), P)), Nat.add(A, Nat.mul(8n, P)), NA.add_swap(Nat.mul(7n, P), A, P), M.cong_r(A, Nat.add(Nat.mul(7n, P), P), Nat.mul(8n, P), NA.add_comm(Nat.mul(7n, P), P)))))
  +x3 = Equal.trans(Nat, Nat.add(r, Nat.add(Nat.mul(q, P), S)), Nat.add(Nat.add(Nat.mul(q, P), S), r), Nat.add(r, Nat.add(Nat.mul(7n, P), W)), NA.add_comm(r, Nat.add(Nat.mul(q, P), S)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(q, P), S), r), Nat.add(Nat.add(Nat.mul(7n, P), W), r), Nat.add(r, Nat.add(Nat.mul(7n, P), W)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(q, P), S), r), Nat.add(A, Nat.mul(8n, P)), Nat.add(Nat.add(Nat.mul(7n, P), W), r), x1, Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(7n, P), W), r), Nat.add(A, Nat.mul(8n, P)), x2)), NA.add_comm(Nat.add(Nat.mul(7n, P), W), r)))
  +x4 = NR.add_cancel(r, Nat.add(Nat.mul(q, P), S), Nat.add(Nat.mul(7n, P), W), x3)
  +m1 = Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(q, P), S), P), Nat.mod(S, P), NR.absorb(pp, q, S))
  +m2 = M.cong_mod(P, Nat.add(Nat.mul(q, P), S), Nat.add(Nat.mul(7n, P), W), x4)
  +m3 = NR.absorb(pp, 7n, W)
  Equal.trans(Nat, Nat.mod(S, P), Nat.mod(Nat.add(Nat.mul(q, P), S), P), Nat.mod(W, P), m1, Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(q, P), S), P), Nat.mod(Nat.add(Nat.mul(7n, P), W), P), Nat.mod(W, P), m2, m3))

# sub with its 8p constant as a parameter
def subg_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ks: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}, +hk: {LM.okb(32n, ks, 2040n) == True{} : Bool}, +hg: {gea(ks, 255n) == True{} : Bool}) -> {LM.okb(32n, F.subl(a, b, ks), WD.sc(28n, one)) == True{} : Bool}:
  +e = subl_okb(one, h1, 32n, a, b, ks, 255n, 255n, 2040n, ha, hb, hk, hg, lt32_small(one, h1, Nat.add(255n, 2040n), {==}))
  PL.okb_mono(32n, F.subl(a, b, ks), Nat.add(255n, 2040n), WD.sc(28n, one), le_small(one, h1, Nat.add(255n, 2040n), {==}), e)

def subg_mod(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ks: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}, +hk: {LM.okb(32n, ks, 2040n) == True{} : Bool}, +hg: {gea(ks, 255n) == True{} : Bool}, +hv: {K.valo(one, ks) == Nat.mul(8n, 1n+pp) : Nat}) -> {Nat.mod(FS.value(F.reduce(F.subl(a, b, ks))), 1n+pp) == Nat.mod(Nat.sub(Nat.add(FS.value(a), 1n+pp), Nat.mod(FS.value(b), 1n+pp)), 1n+pp) : Nat}:
  +e1 = RD.reduce_mod(one, h1, pp, hP, F.subl(a, b, ks), subg_okb(one, h1, a, b, ks, ha, hb, hk, hg))
  +es = subl_val(one, h1, 32n, a, b, ks, 255n, 255n, 2040n, ha, hb, hk, hg, lt32_small(one, h1, Nat.add(255n, 2040n), {==}))
  +ek = Equal.trans(Nat, FS.value(ks), K.valo(one, ks), Nat.mul(8n, 1n+pp), Equal.sym(Nat, K.valo(one, ks), FS.value(ks), K.valo_value(one, h1, ks)), hv)
  +hS = Equal.trans(Nat, Nat.add(FS.value(F.subl(a, b, ks)), FS.value(b)), Nat.add(FS.value(a), FS.value(ks)), Nat.add(FS.value(a), Nat.mul(8n, 1n+pp)), es, M.cong_r(FS.value(a), FS.value(ks), Nat.mul(8n, 1n+pp), ek))
  Equal.trans(Nat, Nat.mod(FS.value(F.reduce(F.subl(a, b, ks))), 1n+pp), Nat.mod(FS.value(F.subl(a, b, ks)), 1n+pp), Nat.mod(Nat.sub(Nat.add(FS.value(a), 1n+pp), Nat.mod(FS.value(b), 1n+pp)), 1n+pp), e1, sub_core(pp, FS.value(a), FS.value(b), FS.value(F.subl(a, b, ks)), hS))

def eight_p_okb() -> {LM.okb(32n, F.eight_p(), 2040n) == True{} : Bool}:
  {==}

def eight_p_gea() -> {gea(F.eight_p(), 255n) == True{} : Bool}:
  {==}

def sub_okb(+one: Nat, +h1: {one == 1n : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {LM.okb(32n, F.sub(a, b), 255n) == True{} : Bool}:
  RD.reduce_okb(one, h1, F.subl(a, b, F.eight_p()), subg_okb(one, h1, a, b, F.eight_p(), ha, hb, eight_p_okb(), eight_p_gea()))

def sub_mod(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {Nat.mod(FS.value(F.sub(a, b)), 1n+pp) == Nat.mod(Nat.sub(Nat.add(FS.value(a), 1n+pp), Nat.mod(FS.value(b), 1n+pp)), 1n+pp) : Nat}:
  subg_mod(one, h1, pp, hP, a, b, F.eight_p(), ha, hb, eight_p_okb(), eight_p_gea(), K.eight_p_val(one, h1, pp, hP))

# ---- select ----

def mul1(+one: Nat, +h1: {one == 1n : Nat}, +x: U32) -> {U32.mul(x, 1) == x : U32}:
  +b = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, v(x), Nat.mul(v(x), 1n), Equal.sym(Nat, Nat.mul(v(x), 1n), v(x), NA.mul_one(v(x))), UD.vb(one, h1, x))
  U.injective(U32.mul(x, 1), x, Equal.trans(Nat, v(U32.mul(x, 1)), Nat.mul(v(x), 1n), v(x), LM.mul_v(one, h1, x, 1, b), NA.mul_one(v(x))))

def mul0(+one: Nat, +h1: {one == 1n : Nat}, +x: U32) -> {U32.mul(x, 0) == 0 : U32}:
  +b = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, 0n, Nat.mul(v(x), 0n), Equal.sym(Nat, Nat.mul(v(x), 0n), 0n, NA.mul_zero(v(x))), LM.sc_pos1(32n, one, h1))
  U.injective(U32.mul(x, 0), 0, Equal.trans(Nat, v(U32.mul(x, 0)), Nat.mul(v(x), 0n), 0n, LM.mul_v(one, h1, x, 0, b), NA.mul_zero(v(x))))

def select0(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +hx: {LM.okb(n, xs, 255n) == True{} : Bool}, +hy: {LM.okb(n, ys, 255n) == True{} : Bool}) -> {F.select(0, xs, ys) == xs : List<&2, U32>}:
  match n xs ys:
    case 0n Nil{} _:
      {==}
    case 0n Con{x, xt} _:
      Empty.absurd({F.select(0, Con{x, xt}, ys) == Con{x, xt} : List<&2, U32>}, L.false_true(hx))
    case 1n+m Nil{} _:
      {==}
    case 1n+m Con{x, xt} Nil{}:
      Empty.absurd({Nil{} == Con{x, xt} : List<&2, U32>}, L.false_true(hy))
    case 1n+ +m Con{+x, +xt} Con{+y, +yt}:
      +e1 = Equal.trans(U32, U32.add(U32.mul(x, 1), U32.mul(y, 0)), U32.add(x, U32.mul(y, 0)), x, Equal.cong(U32, U32, z => U32.add(z, U32.mul(y, 0)), U32.mul(x, 1), x, mul1(one, h1, x)) , Equal.trans(U32, U32.add(x, U32.mul(y, 0)), U32.add(x, 0), x, Equal.cong(U32, U32, z => U32.add(x, z), U32.mul(y, 0), 0, mul0(one, h1, y)), A.add_zero(x)))
      +e2 = select0(one, h1, m, xt, yt, LM.okb_tail(m, x, xt, 255n, hx), LM.okb_tail(m, y, yt, 255n, hy))
      Equal.trans(List<&2, U32>, Con{U32.add(U32.mul(x, 1), U32.mul(y, 0)), F.select(0, xt, yt)}, Con{x, F.select(0, xt, yt)}, Con{x, xt}, Equal.cong(U32, List<&2, U32>, z => Con{z, F.select(0, xt, yt)}, U32.add(U32.mul(x, 1), U32.mul(y, 0)), x, e1), Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, F.select(0, xt, yt), xt, e2))

def select1(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, +hx: {LM.okb(n, xs, 255n) == True{} : Bool}, +hy: {LM.okb(n, ys, 255n) == True{} : Bool}) -> {F.select(1, xs, ys) == ys : List<&2, U32>}:
  match n xs ys:
    case 0n Nil{} Nil{}:
      {==}
    case 0n Nil{} Con{y, yt}:
      Empty.absurd({F.select(1, Nil{}, Con{y, yt}) == Con{y, yt} : List<&2, U32>}, L.false_true(hy))
    case 0n Con{x, xt} _:
      Empty.absurd({F.select(1, Con{x, xt}, ys) == ys : List<&2, U32>}, L.false_true(hx))
    case 1n+m Nil{} _:
      Empty.absurd({Nil{} == ys : List<&2, U32>}, L.false_true(hx))
    case 1n+m Con{x, xt} Nil{}:
      {==}
    case 1n+ +m Con{+x, +xt} Con{+y, +yt}:
      +e1 = Equal.trans(U32, U32.add(U32.mul(x, 0), U32.mul(y, 1)), U32.add(0, y), y, Equal.trans(U32, U32.add(U32.mul(x, 0), U32.mul(y, 1)), U32.add(0, U32.mul(y, 1)), U32.add(0, y), Equal.cong(U32, U32, z => U32.add(z, U32.mul(y, 1)), U32.mul(x, 0), 0, mul0(one, h1, x)), Equal.cong(U32, U32, z => U32.add(0, z), U32.mul(y, 1), y, mul1(one, h1, y))), A.zero_add(y))
      +e2 = select1(one, h1, m, xt, yt, LM.okb_tail(m, x, xt, 255n, hx), LM.okb_tail(m, y, yt, 255n, hy))
      Equal.trans(List<&2, U32>, Con{U32.add(U32.mul(x, 0), U32.mul(y, 1)), F.select(1, xt, yt)}, Con{y, F.select(1, xt, yt)}, Con{y, yt}, Equal.cong(U32, List<&2, U32>, z => Con{z, F.select(1, xt, yt)}, U32.add(U32.mul(x, 0), U32.mul(y, 1)), y, e1), Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{y, z}, F.select(1, xt, yt), yt, e2))
