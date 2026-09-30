import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../curve25519/cong.bend as G
import ./nl.bend as NL
import ./pw.bend as PW
import ./carry.bend as CA
import ./pass.bend as PS
import ./bridge.bend as BR

# sub of src/crypto/curve25519/fe.bend: a + 8 p - b limbwise (kp8, every
# limb at least 2^19, so no limb underflows), then a carry pass. The
# constant's value is 8 p, derived in the symbolic one: every limb but the
# first is 8 R - 8 = 8 (R - 1), a telescoping sum.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# every entry at least b / at most b
def atleast(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      Bool.and(Nat.is_le(b, x), atleast(xt, b))

def atmost(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      Bool.and(Nat.is_le(x, b), atmost(xt, b))

# (a + c) - b == a + (c - b) for b <= c
def sub_add_r(+a: Nat, +c: Nat, +b: Nat, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.sub(Nat.add(a, c), b) == Nat.add(a, Nat.sub(c, b)) : Nat}:
  +d = Nat.sub(c, b)
  +e1 = Equal.cong(Nat, Nat, t => Nat.sub(Nat.add(a, t), b), c, Nat.add(b, d), sy(Nat.add(b, d), c, N.sub_add(c, b, h)))
  +e2 = Equal.cong(Nat, Nat, t => Nat.sub(t, b), Nat.add(a, Nat.add(b, d)), Nat.add(b, Nat.add(a, d)), NA.add_swap(a, b, d))
  tr(Nat.sub(Nat.add(a, c), b), Nat.sub(Nat.add(a, Nat.add(b, d)), b), Nat.add(a, d), e1, tr(Nat.sub(Nat.add(a, Nat.add(b, d)), b), Nat.sub(Nat.add(b, Nat.add(a, d)), b), Nat.add(a, d), e2, N.add_sub_cancel(b, Nat.add(a, d))))

# ---- the constant 8 p ----

# R 8 == 2^20
def r8(+one: Nat, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.mul(R, 8n) == WD.sc(20n, one) : Nat}:
  tr(Nat.mul(R, 8n), WD.sc(3n, R), WD.sc(20n, one), PS.mulp(3n, R), PS.at_r(one, R, hR, z => {WD.sc(3n, z) == WD.sc(20n, one) : Nat}, M.sc_sc(3n, 17n, one)))

def small_le(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk: {Nat.is_le(k, 256n) == True{} : Bool}, +j: Nat, +d: Nat, +hj: {Nat.add(d, 8n) == j : Nat}) -> {Nat.is_le(k, WD.sc(j, one)) == True{} : Bool}:
  +a = L.subst(Nat, o => {Nat.is_le(k, WD.sc(8n, o)) == True{} : Bool}, 1n, one, Equal.sym(Nat, one, 1n, h1), hk)
  N.le_trans(k, WD.sc(8n, one), WD.sc(j, one), a, L.subst(Nat, z => {Nat.is_le(WD.sc(8n, one), WD.sc(z, one)) == True{} : Bool}, Nat.add(d, 8n), j, hj, PW.le_sc(d, 8n, one)))

# (Q + k) + 2^17 L == R 8 + 2^17 L, given Q + k == R 8; and the telescoping step
def kstep(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +Q: Nat, +k: Nat, +hq: {Nat.add(k, Q) == Nat.mul(R, 8n) : Nat}, +T: List<&2, Nat>, +m: Nat, +ih: {Nat.add(FV.lv(T), Nat.mul(one, 8n)) == Nat.mul(NL.sh(m, one), 8n) : Nat}) -> {Nat.add(FV.lv(Con{Q, T}), k) == Nat.mul(NL.sh(1n+m, one), 8n) : Nat}:
  +VT = FV.lv(T)
  +e1 = CA.swap3(Q, C.shift(17n, VT), k)
  +e2 = M.cong_l(Nat.add(Q, k), Nat.mul(R, 8n), C.shift(17n, VT), tr(Nat.add(Q, k), Nat.add(k, Q), Nat.mul(R, 8n), NA.add_comm(Q, k), hq))
  +e3 = NA.add_comm(Nat.mul(R, 8n), C.shift(17n, VT))
  +f1 = AR.sc_mul(17n, NL.sh(m, one), 8n)
  +f2 = M.cong_sc(17n, Nat.mul(NL.sh(m, one), 8n), Nat.add(VT, Nat.mul(one, 8n)), sy(Nat.add(VT, Nat.mul(one, 8n)), Nat.mul(NL.sh(m, one), 8n), ih))
  +f3 = sy(Nat.add(C.shift(17n, VT), C.shift(17n, Nat.mul(one, 8n))), C.shift(17n, Nat.add(VT, Nat.mul(one, 8n))), M.sc_add(17n, VT, Nat.mul(one, 8n)))
  +f4 = M.cong_r(C.shift(17n, VT), C.shift(17n, Nat.mul(one, 8n)), Nat.mul(R, 8n), tr(C.shift(17n, Nat.mul(one, 8n)), Nat.mul(WD.sc(17n, one), 8n), Nat.mul(R, 8n), AR.sc_mul(17n, one, 8n), Equal.cong(Nat, Nat, z => Nat.mul(z, 8n), WD.sc(17n, one), R, sy(R, WD.sc(17n, one), hR))))
  +lhs = tr(Nat.add(Nat.add(Q, C.shift(17n, VT)), k), Nat.add(Nat.add(Q, k), C.shift(17n, VT)), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), e1, tr(Nat.add(Nat.add(Q, k), C.shift(17n, VT)), Nat.add(Nat.mul(R, 8n), C.shift(17n, VT)), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), e2, e3))
  +rhs = tr(Nat.mul(C.shift(17n, NL.sh(m, one)), 8n), C.shift(17n, Nat.mul(NL.sh(m, one), 8n)), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), sy(C.shift(17n, Nat.mul(NL.sh(m, one), 8n)), Nat.mul(C.shift(17n, NL.sh(m, one)), 8n), f1), tr(C.shift(17n, Nat.mul(NL.sh(m, one), 8n)), C.shift(17n, Nat.add(VT, Nat.mul(one, 8n))), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), f2, tr(C.shift(17n, Nat.add(VT, Nat.mul(one, 8n))), Nat.add(C.shift(17n, VT), C.shift(17n, Nat.mul(one, 8n))), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), f3, f4)))
  tr(Nat.add(Nat.add(Q, C.shift(17n, VT)), k), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), Nat.mul(C.shift(17n, NL.sh(m, one)), 8n), lhs, sy(Nat.mul(C.shift(17n, NL.sh(m, one)), 8n), Nat.add(C.shift(17n, VT), Nat.mul(R, 8n)), rhs))

def q8(+R: Nat) -> Nat:
  Nat.sub(Nat.mul(R, 8n), 8n)

def rep_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +n: Nat) -> {Nat.add(FV.lv(LS.rep(n, q8(R), Nil{})), Nat.mul(one, 8n)) == Nat.mul(NL.sh(n, one), 8n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      +e8 = L.subst(Nat, o => {Nat.mul(o, 8n) == 8n : Nat}, 1n, one, Equal.sym(Nat, one, 1n, h1), {==})
      +hq = N.sub_add(Nat.mul(R, 8n), 8n, L.subst(Nat, z => {Nat.is_le(8n, z) == True{} : Bool}, WD.sc(20n, one), Nat.mul(R, 8n), sy(Nat.mul(R, 8n), WD.sc(20n, one), r8(one, R, hR)), small_le(one, h1, 8n, {==}, 20n, 12n, {==})))
      +k = kstep(one, h1, R, hR, q8(R), 8n, hq, LS.rep(m, q8(R), Nil{}), m, rep_val(one, h1, R, hR, m))
      L.subst(Nat, z => {Nat.add(FV.lv(Con{q8(R), LS.rep(m, q8(R), Nil{})}), z) == Nat.mul(NL.sh(1n+m, one), 8n) : Nat}, 8n, Nat.mul(one, 8n), sy(Nat.mul(one, 8n), 8n, e8), k)

# value(kp8) == 8 p
def kp8_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {FV.lv(LS.kp8(R)) == Nat.mul(1n+pp, 8n) : Nat}:
  +P = {1n+pp : Nat}
  +Q0 = Nat.sub(Nat.mul(R, 8n), 152n)
  +hq = N.sub_add(Nat.mul(R, 8n), 152n, L.subst(Nat, z => {Nat.is_le(152n, z) == True{} : Bool}, WD.sc(20n, one), Nat.mul(R, 8n), sy(Nat.mul(R, 8n), WD.sc(20n, one), r8(one, R, hR)), small_le(one, h1, 152n, {==}, 20n, 12n, {==})))
  +k = kstep(one, h1, R, hR, Q0, 152n, hq, LS.rep(14n, q8(R), Nil{}), 14n, rep_val(one, h1, R, hR, 14n))
  +e1 = tr(Nat.mul(NL.sh(15n, one), 8n), Nat.mul(WD.sc(255n, one), 8n), Nat.add(Nat.mul(P, 8n), 152n), Equal.cong(Nat, Nat, z => Nat.mul(z, 8n), NL.sh(15n, one), WD.sc(255n, one), NL.sh15(one)), tr(Nat.mul(WD.sc(255n, one), 8n), Nat.mul(Nat.add(P, 19n), 8n), Nat.add(Nat.mul(P, 8n), 152n), Equal.cong(Nat, Nat, z => Nat.mul(z, 8n), WD.sc(255n, one), Nat.add(P, 19n), sy(Nat.add(P, 19n), WD.sc(255n, one), hP)), NA.mul_add_right(P, 19n, 8n)))
  +e2 = tr(Nat.add(152n, FV.lv(LS.kp8(R))), Nat.add(FV.lv(LS.kp8(R)), 152n), Nat.add(152n, Nat.mul(P, 8n)), NA.add_comm(152n, FV.lv(LS.kp8(R))), tr(Nat.add(FV.lv(LS.kp8(R)), 152n), Nat.mul(NL.sh(15n, one), 8n), Nat.add(152n, Nat.mul(P, 8n)), k, tr(Nat.mul(NL.sh(15n, one), 8n), Nat.add(Nat.mul(P, 8n), 152n), Nat.add(152n, Nat.mul(P, 8n)), e1, NA.add_comm(Nat.mul(P, 8n), 152n))))
  NR.add_cancel(152n, FV.lv(LS.kp8(R)), Nat.mul(P, 8n), e2)

def kp8_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> G.ceq(pp, FV.lv(LS.kp8(R)), 0n):
  +P = {1n+pp : Nat}
  +e = tr(FV.lv(LS.kp8(R)), Nat.mul(P, 8n), Nat.add(Nat.mul(8n, P), 0n), kp8_val(one, h1, pp, hP, R, hR), tr(Nat.mul(P, 8n), Nat.mul(8n, P), Nat.add(Nat.mul(8n, P), 0n), NA.mul_comm(P, 8n), sy(Nat.add(Nat.mul(8n, P), 0n), Nat.mul(8n, P), N.add_zero(Nat.mul(8n, P)))))
  G.c_trans(pp, FV.lv(LS.kp8(R)), Nat.add(Nat.mul(8n, P), 0n), 0n, G.c_eq(pp, FV.lv(LS.kp8(R)), Nat.add(Nat.mul(8n, P), 0n), e), NR.absorb(pp, 8n, 0n))

# 2^19 <= R 8 - k for k <= 2^19
def pw_lo(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +k: Nat, +hk: {Nat.is_le(k, WD.sc(19n, one)) == True{} : Bool}) -> {Nat.is_le(WD.sc(19n, one), Nat.sub(Nat.mul(R, 8n), k)) == True{} : Bool}:
  +s19 = WD.sc(19n, one)
  +e = tr(Nat.mul(R, 8n), WD.sc(20n, one), Nat.add(s19, s19), r8(one, R, hR), sy(Nat.add(s19, s19), WD.sc(20n, one), PW.dbl(19n, one)))
  +e2 = tr(Nat.sub(Nat.mul(R, 8n), k), Nat.sub(Nat.add(s19, s19), k), Nat.add(s19, Nat.sub(s19, k)), Equal.cong(Nat, Nat, z => Nat.sub(z, k), Nat.mul(R, 8n), Nat.add(s19, s19), e), sub_add_r(s19, s19, k, hk))
  L.subst(Nat, z => {Nat.is_le(s19, z) == True{} : Bool}, Nat.add(s19, Nat.sub(s19, k)), Nat.sub(Nat.mul(R, 8n), k), sy(Nat.sub(Nat.mul(R, 8n), k), Nat.add(s19, Nat.sub(s19, k)), e2), N.le_add_right(s19, Nat.sub(s19, k)))

def rep_atleast(+n: Nat, +k: Nat, +b: Nat, +h: {Nat.is_le(b, k) == True{} : Bool}) -> {atleast(LS.rep(n, k, Nil{}), b) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.and_intro(Nat.is_le(b, k), atleast(LS.rep(m, k, Nil{}), b), h, rep_atleast(m, k, b, h))

def rep_atmost(+n: Nat, +k: Nat, +b: Nat, +h: {Nat.is_le(k, b) == True{} : Bool}) -> {atmost(LS.rep(n, k, Nil{}), b) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      L.and_intro(Nat.is_le(k, b), atmost(LS.rep(m, k, Nil{}), b), h, rep_atmost(m, k, b, h))

# every limb of kp8 is at least 2^19 and at most 2^20
def kp8_bounds(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Bool.and(atleast(LS.kp8(R), WD.sc(19n, one)), atmost(LS.kp8(R), WD.sc(20n, one))) == True{} : Bool}:
  +s19 = WD.sc(19n, one)
  +s20 = WD.sc(20n, one)
  +e20 = r8(one, R, hR)
  +lo = pw_lo(one, h1, R, hR, 152n, small_le(one, h1, 152n, {==}, 19n, 11n, {==}))
  +lo8 = pw_lo(one, h1, R, hR, 8n, small_le(one, h1, 8n, {==}, 19n, 11n, {==}))
  +hi = L.subst(Nat, z => {Nat.is_le(Nat.sub(Nat.mul(R, 8n), 152n), z) == True{} : Bool}, Nat.mul(R, 8n), s20, e20, AR.sub_le2(Nat.mul(R, 8n), 152n))
  +hi8 = L.subst(Nat, z => {Nat.is_le(q8(R), z) == True{} : Bool}, Nat.mul(R, 8n), s20, e20, AR.sub_le2(Nat.mul(R, 8n), 8n))
  L.and_intro(atleast(LS.kp8(R), s19), atmost(LS.kp8(R), s20), L.and_intro(Nat.is_le(s19, Nat.sub(Nat.mul(R, 8n), 152n)), atleast(LS.rep(14n, q8(R), Nil{}), s19), lo, rep_atleast(14n, q8(R), s19, lo8)), L.and_intro(Nat.is_le(Nat.sub(Nat.mul(R, 8n), 152n), s20), atmost(LS.rep(14n, q8(R), Nil{}), s20), hi, rep_atmost(14n, q8(R), s20, hi8)))

# ---- subl ----

# value(subl(xs, ys, ks)) + value(ys) == value(xs) + value(ks) when every y is below b <= every k
def subl_val(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +ks: List<&2, Nat>, +b: Nat, +hy: {FV.below(ys, b) == True{} : Bool}, +hk: {atleast(ks, b) == True{} : Bool}, +l1: {PS.ln(xs) == PS.ln(ys) : Nat}, +l2: {PS.ln(ys) == PS.ln(ks) : Nat}) -> {Nat.add(FV.lv(LS.subl(xs, ys, ks)), FV.lv(ys)) == Nat.add(FV.lv(xs), FV.lv(ks)) : Nat}:
  match xs ys ks:
    case Nil{} Nil{} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt} Con{+k, +kt}:
      +d = Nat.sub(Nat.add(x, k), y)
      +hyk = N.le_trans(y, k, Nat.add(x, k), N.lt_le(y, k, N.lt_le_trans(y, b, k, NL.below_head(y, yt, b, hy), L.and_left(Nat.is_le(b, k), atleast(kt, b), hk))), NL.le_add_l(x, k))
      +ed = tr(Nat.add(d, y), Nat.add(y, d), Nat.add(x, k), NA.add_comm(d, y), N.sub_add(Nat.add(x, k), y, hyk))
      +ih = subl_val(xt, yt, kt, b, NL.below_tail(y, yt, b, hy), L.and_right(Nat.is_le(b, k), atleast(kt, b), hk), N.succ_inj(PS.ln(xt), PS.ln(yt), l1), N.succ_inj(PS.ln(yt), PS.ln(kt), l2))
      +D = FV.lv(LS.subl(xt, yt, kt))
      +Y = FV.lv(yt)
      +X = FV.lv(xt)
      +K = FV.lv(kt)
      +e1 = M.add4(d, C.shift(17n, D), y, C.shift(17n, Y))
      +e2 = M.cong_r(Nat.add(d, y), Nat.add(C.shift(17n, D), C.shift(17n, Y)), C.shift(17n, Nat.add(X, K)), tr(Nat.add(C.shift(17n, D), C.shift(17n, Y)), C.shift(17n, Nat.add(D, Y)), C.shift(17n, Nat.add(X, K)), M.sc_add(17n, D, Y), M.cong_sc(17n, Nat.add(D, Y), Nat.add(X, K), ih)))
      +e3 = M.cong_l(Nat.add(d, y), Nat.add(x, k), C.shift(17n, Nat.add(X, K)), ed)
      +e4 = M.cong_r(Nat.add(x, k), C.shift(17n, Nat.add(X, K)), Nat.add(C.shift(17n, X), C.shift(17n, K)), sy(Nat.add(C.shift(17n, X), C.shift(17n, K)), C.shift(17n, Nat.add(X, K)), M.sc_add(17n, X, K)))
      +e5 = M.add4(x, k, C.shift(17n, X), C.shift(17n, K))
      +Z0 = Nat.add(Nat.add(d, C.shift(17n, D)), Nat.add(y, C.shift(17n, Y)))
      +Z1 = Nat.add(Nat.add(d, y), Nat.add(C.shift(17n, D), C.shift(17n, Y)))
      +Z2 = Nat.add(Nat.add(d, y), C.shift(17n, Nat.add(X, K)))
      +Z3 = Nat.add(Nat.add(x, k), C.shift(17n, Nat.add(X, K)))
      +Z4 = Nat.add(Nat.add(x, k), Nat.add(C.shift(17n, X), C.shift(17n, K)))
      +Z5 = Nat.add(Nat.add(x, C.shift(17n, X)), Nat.add(k, C.shift(17n, K)))
      tr(Z0, Z1, Z5, e1, tr(Z1, Z2, Z5, e2, tr(Z2, Z3, Z5, e3, tr(Z3, Z4, Z5, e4, e5))))
    case Nil{} Nil{} Con{k, kt}:
      Empty.absurd({Nat.add(0n, 0n) == Nat.add(0n, FV.lv(Con{k, kt})) : Nat}, N.zero_succ(PS.ln(kt), l2))
    case Nil{} Con{y, yt} _:
      Empty.absurd({Nat.add(FV.lv(LS.subl(Nil{}, Con{y, yt}, ks)), FV.lv(Con{y, yt})) == Nat.add(0n, FV.lv(ks)) : Nat}, N.zero_succ(PS.ln(yt), l1))
    case Con{x, xt} Nil{} _:
      Empty.absurd({Nat.add(FV.lv(LS.subl(Con{x, xt}, Nil{}, ks)), 0n) == Nat.add(FV.lv(Con{x, xt}), FV.lv(ks)) : Nat}, N.succ_zero(PS.ln(xt), l1))
    case Con{x, xt} Con{y, yt} Nil{}:
      Empty.absurd({Nat.add(FV.lv(LS.subl(Con{x, xt}, Con{y, yt}, Nil{})), FV.lv(Con{y, yt})) == Nat.add(FV.lv(Con{x, xt}), 0n) : Nat}, N.succ_zero(PS.ln(yt), l2))

def subl_below(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +ks: List<&2, Nat>, +a: Nat, +kb: Nat, +hx: {FV.below(xs, a) == True{} : Bool}, +hk: {atmost(ks, kb) == True{} : Bool}) -> {FV.below(LS.subl(xs, ys, ks), Nat.add(a, kb)) == True{} : Bool}:
  match xs ys ks:
    case Nil{} _ _:
      {==}
    case Con{x, xt} Nil{} _:
      {==}
    case Con{x, xt} Con{y, yt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt} Con{+k, +kt}:
      +hxk = N.lt_le_trans(Nat.add(x, k), Nat.add(a, k), Nat.add(a, kb), N.lt_add_r2(x, a, k, NL.below_head(x, xt, a, hx)), N.le_add_left(k, kb, a, L.and_left(Nat.is_le(k, kb), atmost(kt, kb), hk)))
      NL.below_con(Nat.sub(Nat.add(x, k), y), LS.subl(xt, yt, kt), Nat.add(a, kb), N.le_lt_trans(Nat.sub(Nat.add(x, k), y), Nat.add(x, k), Nat.add(a, kb), AR.sub_le2(Nat.add(x, k), y), hxk), subl_below(xt, yt, kt, a, kb, NL.below_tail(x, xt, a, hx), L.and_right(Nat.is_le(k, kb), atmost(kt, kb), hk)))

# ---- sub on elements ----

def subl_len(+R: Nat, +a: FE.Fe, +b: FE.Fe) -> {PS.ln(LS.subl(FE.to_list(a), FE.to_list(b), LS.kp8(R))) == 15n : Nat}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

def kp8_len(+R: Nat) -> {PS.ln(LS.kp8(R)) == 15n : Nat}:
  {==}

def ln15(+a: FE.Fe) -> {PS.ln(FE.to_list(a)) == 15n : Nat}:
  match a:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

# value(sub(a, b)) == value(a) + p - (value(b) mod p)  (mod p)
def sub_c(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +hb: {FV.ok(one, b) == True{} : Bool}) -> G.ceq(pp, FV.value(FE.sub(R, a, b)), Nat.sub(Nat.add(FV.value(a), 1n+pp), Nat.mod(FV.value(b), 1n+pp))):
  +P = {1n+pp : Nat}
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +K = LS.kp8(R)
  +S = LS.subl(A, B, K)
  +X = FV.lv(A)
  +Y = FV.lv(B)
  +D = FV.lv(S)
  +r = Nat.mod(Y, P)
  +W = Nat.sub(Nat.add(X, P), r)
  +e0 = Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), FE.to_list(FE.sub(R, a, b)), LS.sub_l(R, A, B), BR.sub_b(R, a, b))
  +c0 = G.c_trans(pp, FV.value(FE.sub(R, a, b)), FV.lv(LS.pass(R, S)), D, G.c_eq(pp, FV.value(FE.sub(R, a, b)), FV.lv(LS.pass(R, S)), e0), PS.pass_c(one, h1, pp, hP, R, hR, S, subl_len(R, a, b)))
  +kb = kp8_bounds(one, h1, R, hR)
  +ev = subl_val(A, B, K, WD.sc(19n, one), hb, L.and_left(atleast(K, WD.sc(19n, one)), atmost(K, WD.sc(20n, one)), kb), Equal.trans(Nat, PS.ln(A), 15n, PS.ln(B), ln15(a), Equal.sym(Nat, PS.ln(B), 15n, ln15(b))), Equal.trans(Nat, PS.ln(B), 15n, PS.ln(K), ln15(b), Equal.sym(Nat, PS.ln(K), 15n, kp8_len(R))))
  +c1 = G.c_add(pp, D, D, r, Y, G.c_refl(pp, D), G.c_mod(pp, Y))
  +c2 = G.c_eq(pp, Nat.add(D, Y), Nat.add(X, FV.lv(K)), ev)
  +c3 = G.c_add(pp, X, X, FV.lv(K), 0n, G.c_refl(pp, X), kp8_c(one, h1, pp, hP, R, hR))
  +c4 = G.c_eq(pp, Nat.add(X, 0n), X, N.add_zero(X))
  +cDr = G.c_trans(pp, Nat.add(D, r), Nat.add(D, Y), X, c1, G.c_trans(pp, Nat.add(D, Y), Nat.add(X, FV.lv(K)), X, c2, G.c_trans(pp, Nat.add(X, FV.lv(K)), Nat.add(X, 0n), X, c3, c4)))
  +hr = N.le_trans(r, P, Nat.add(X, P), N.lt_le(r, P, NR.dm_lt(pp, Y)), NL.le_add_l(X, P))
  +eW = tr(Nat.add(W, r), Nat.add(r, W), Nat.add(X, P), NA.add_comm(W, r), N.sub_add(Nat.add(X, P), r, hr))
  +eXP = tr(Nat.add(X, P), Nat.add(P, X), Nat.add(Nat.mul(1n, P), X), NA.add_comm(X, P), M.cong_l(P, Nat.mul(1n, P), X, sy(Nat.mul(1n, P), P, AR.one_mul(P))))
  +cW = G.c_trans(pp, Nat.add(W, r), Nat.add(Nat.mul(1n, P), X), X, G.c_eq(pp, Nat.add(W, r), Nat.add(Nat.mul(1n, P), X), tr(Nat.add(W, r), Nat.add(X, P), Nat.add(Nat.mul(1n, P), X), eW, eXP)), NR.absorb(pp, 1n, X))
  +cc = G.c_cancel(pp, D, W, r, G.c_trans(pp, Nat.add(D, r), X, Nat.add(W, r), cDr, G.c_sym(pp, Nat.add(W, r), X, cW)))
  G.c_trans(pp, FV.value(FE.sub(R, a, b)), D, W, c0, cc)

def sub_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +a: FE.Fe, +b: FE.Fe, +ha: {FV.ok(one, a) == True{} : Bool}) -> {FV.ok(one, FE.sub(R, a, b)) == True{} : Bool}:
  +A = FE.to_list(a)
  +B = FE.to_list(b)
  +K = LS.kp8(R)
  +S = LS.subl(A, B, K)
  +s19 = WD.sc(19n, one)
  +s20 = WD.sc(20n, one)
  +kb = kp8_bounds(one, h1, R, hR)
  +h0 = subl_below(A, B, K, s19, s20, ha, L.and_right(atleast(K, s19), atmost(K, s20), kb))
  +l1 = N.le_trans(Nat.add(s19, s20), Nat.add(s20, s20), WD.sc(47n, one), M.le_add_r(s19, s20, s20, PW.le_sc(1n, 19n, one)), L.subst(Nat, z => {Nat.is_le(z, WD.sc(47n, one)) == True{} : Bool}, WD.sc(21n, one), Nat.add(s20, s20), sy(Nat.add(s20, s20), WD.sc(21n, one), PW.dbl(20n, one)), PW.le_sc(26n, 21n, one)))
  +h47 = NL.below_mono(S, Nat.add(s19, s20), WD.sc(47n, one), l1, h0)
  L.subst(List<&2, Nat>, z => {FV.below(z, s19) == True{} : Bool}, LS.pass(R, S), FE.to_list(FE.sub(R, a, b)), Equal.sym(List<&2, Nat>, FE.to_list(FE.sub(R, a, b)), LS.pass(R, S), BR.sub_b(R, a, b)), PS.pass_ok(one, h1, R, hR, S, subl_len(R, a, b), h47))
