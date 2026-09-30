import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../fe/nl.bend as NL
import ../fe/pw.bend as PW
import ../fe/carry.bend as CA
import ../fe/pass.bend as PS
import ../fe/ops.bend as OP
import ../fe/canon.bend as CN
import ../fe/bytes.bend as BY
import ./subb.bend as SB
import ../curve25519/cong.bend as G

# One step of Horner's rule mod L (src/crypto/ed25519/scalar.bend step):
# for an accumulator a < L in 15 limbs below R = 2^17 and a limb d < R,
# the result is (d + R a) mod L in 15 limbs below R. The estimate m of the
# quotient satisfies m L <= t < m L + 2 L (below); subtracting m L and then
# L with borrows, and keeping the second difference exactly when it does
# not borrow, leaves t mod L.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# ---- lists ----

def lv_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {FV.lv(LS.app(xs, ys)) == Nat.add(FV.lv(xs), NL.sh(PS.ln(xs), FV.lv(ys))) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +A = FV.lv(xt)
      +B = NL.sh(PS.ln(xt), FV.lv(ys))
      tr(Nat.add(x, C.shift(17n, FV.lv(LS.app(xt, ys)))), Nat.add(x, C.shift(17n, Nat.add(A, B))), Nat.add(Nat.add(x, C.shift(17n, A)), C.shift(17n, B)), M.cong_r(x, C.shift(17n, FV.lv(LS.app(xt, ys))), C.shift(17n, Nat.add(A, B)), M.cong_sc(17n, FV.lv(LS.app(xt, ys)), Nat.add(A, B), lv_app(xt, ys))), tr(Nat.add(x, C.shift(17n, Nat.add(A, B))), Nat.add(x, Nat.add(C.shift(17n, A), C.shift(17n, B))), Nat.add(Nat.add(x, C.shift(17n, A)), C.shift(17n, B)), M.cong_r(x, C.shift(17n, Nat.add(A, B)), Nat.add(C.shift(17n, A), C.shift(17n, B)), sy(Nat.add(C.shift(17n, A), C.shift(17n, B)), C.shift(17n, Nat.add(A, B)), M.sc_add(17n, A, B))), sy(Nat.add(Nat.add(x, C.shift(17n, A)), C.shift(17n, B)), Nat.add(x, Nat.add(C.shift(17n, A), C.shift(17n, B))), NA.add_assoc(x, C.shift(17n, A), C.shift(17n, B)))))

# value([c]) == c
def lv1(+c: Nat) -> {FV.lv([c]) == c : Nat}:
  N.add_zero(c)

def take_len(+n: Nat, +k: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == Nat.add(n, k) : Nat}) -> {PS.ln(LS.take(n, xs)) == n : Nat}:
  match n xs:
    case 0n _:
      {==}
    case 1n+m Nil{}:
      Empty.absurd({0n == 1n+m : Nat}, N.zero_succ(Nat.add(m, k), hl))
    case 1n+ +m Con{+x, +xt}:
      Equal.cong(Nat, Nat, z => 1n+z, PS.ln(LS.take(m, xt)), m, take_len(m, k, xt, N.succ_inj(PS.ln(xt), Nat.add(m, k), hl)))

def scal_len(+m: Nat, +xs: List<&2, Nat>) -> {PS.ln(LS.scal(m, xs)) == PS.ln(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      Equal.cong(Nat, Nat, z => 1n+z, PS.ln(LS.scal(m, xt)), PS.ln(xt), scal_len(m, xt))

def sel_len(+s: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {PS.ln(LS.sel(s, xs, ys)) == PS.ln(xs) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      Empty.absurd({0n == 1n+PS.ln(xt) : Nat}, N.succ_zero(PS.ln(xt), h))
    case Con{+x, +xt} Con{+y, +yt}:
      Equal.cong(Nat, Nat, t => 1n+t, PS.ln(LS.sel(s, xt, yt)), PS.ln(xt), sel_len(s, xt, yt, N.succ_inj(PS.ln(xt), PS.ln(yt), h)))

# 2^(17 n) x == x 2^(17 n)
def sh_mul(+one: Nat, +h1: {one == 1n : Nat}, +n: Nat, +x: Nat) -> {NL.sh(n, x) == Nat.mul(x, NL.sh(n, one)) : Nat}:
  tr(NL.sh(n, x), WD.sc(NL.m17(n), x), Nat.mul(x, NL.sh(n, one)), NL.sh_sc(n, x), tr(WD.sc(NL.m17(n), x), Nat.mul(x, WD.sc(NL.m17(n), one)), Nat.mul(x, NL.sh(n, one)), sy(Nat.mul(x, WD.sc(NL.m17(n), one)), WD.sc(NL.m17(n), x), AR.mul_sc1(NL.m17(n), one, h1, x)), Equal.cong(Nat, Nat, z => Nat.mul(x, z), WD.sc(NL.m17(n), one), NL.sh(n, one), sy(NL.sh(n, one), WD.sc(NL.m17(n), one), NL.sh_sc(n, one)))))

# CA.shl through the length
def shl_mul(+one: Nat, +h1: {one == 1n : Nat}, +xs: List<&2, Nat>, +n: Nat, +hl: {PS.ln(xs) == n : Nat}, +c: Nat) -> {CA.shl(xs, c) == Nat.mul(c, NL.sh(n, one)) : Nat}:
  tr(CA.shl(xs, c), NL.sh(PS.ln(xs), c), Nat.mul(c, NL.sh(n, one)), PS.shl_sh(xs, c), tr(NL.sh(PS.ln(xs), c), NL.sh(n, c), Nat.mul(c, NL.sh(n, one)), Equal.cong(Nat, Nat, z => NL.sh(z, c), PS.ln(xs), n, hl), sh_mul(one, h1, n, c)))

# 16 limbs with value below R^15: the first 15 hold the value
def take15(+one: Nat, +h1: {one == 1n : Nat}, +zs: List<&2, Nat>, +hv: {Nat.is_lt(FV.lv(zs), NL.sh(15n, one)) == True{} : Bool}) -> {FV.lv(LS.take(15n, zs)) == FV.lv(zs) : Nat}:
  +T = FV.lv(LS.take(15n, zs))
  +D = FV.lv(LS.drop(15n, zs))
  +S15 = NL.sh(15n, one)
  +es = NL.lv_split(15n, zs)
  +ed = tr(NL.sh(15n, D), Nat.mul(D, S15), Nat.mul(D, S15), sh_mul(one, h1, 15n, D), {==})
  +hD = CN.mul_lt_cancel(D, 1n, S15, N.le_lt_trans(Nat.mul(D, S15), FV.lv(zs), Nat.mul(1n, S15), L.subst(Nat, z => {Nat.is_le(Nat.mul(D, S15), z) == True{} : Bool}, Nat.add(T, NL.sh(15n, D)), FV.lv(zs), sy(FV.lv(zs), Nat.add(T, NL.sh(15n, D)), es), L.subst(Nat, z => {Nat.is_le(Nat.mul(D, S15), Nat.add(T, z)) == True{} : Bool}, Nat.mul(D, S15), NL.sh(15n, D), sy(NL.sh(15n, D), Nat.mul(D, S15), ed), NL.le_add_l(T, Nat.mul(D, S15)))), L.subst(Nat, z => {Nat.is_lt(FV.lv(zs), z) == True{} : Bool}, S15, Nat.mul(1n, S15), sy(Nat.mul(1n, S15), S15, AR.one_mul(S15)), hv)))
  +eD = BY.lt_one_zero(D, hD)
  sy(FV.lv(zs), T, tr(FV.lv(zs), Nat.add(T, NL.sh(15n, D)), T, es, tr(Nat.add(T, NL.sh(15n, D)), Nat.add(T, NL.sh(15n, 0n)), T, M.cong_r(T, NL.sh(15n, D), NL.sh(15n, 0n), Equal.cong(Nat, Nat, z => NL.sh(15n, z), D, 0n, eD)), tr(Nat.add(T, NL.sh(15n, 0n)), Nat.add(T, 0n), T, M.cong_r(T, NL.sh(15n, 0n), 0n, NL.sh_zero(15n)), N.add_zero(T)))))

# ---- the two subtractions ----

# b <= 1, U + ML == T + b S, U < S, ML <= T: b == 0
def borrow0(+b: Nat, +U: Nat, +ML: Nat, +T: Nat, +S: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +he: {Nat.add(U, ML) == Nat.add(T, Nat.mul(b, S)) : Nat}, +hU: {Nat.is_lt(U, S) == True{} : Bool}, +hm: {Nat.is_le(ML, T) == True{} : Bool}) -> {b == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+ +c:
      +X = Nat.add(T, Nat.mul(1n+c, S))
      +l1 = N.le_add_left(ML, T, U, hm)
      +l2 = N.lt_add_r2(U, S, T, hU)
      +l3 = M.le_add_r(S, Nat.mul(1n+c, S), T, N.le_add_right(S, Nat.mul(c, S)))
      +l4 = L.subst(Nat, z => {Nat.is_le(Nat.add(S, T), z) == True{} : Bool}, Nat.add(Nat.mul(1n+c, S), T), X, NA.add_comm(Nat.mul(1n+c, S), T), l3)
      +l5 = N.lt_le_trans(Nat.add(U, T), Nat.add(S, T), X, l2, l4)
      +l6 = N.le_lt_trans(Nat.add(U, ML), Nat.add(U, T), X, l1, l5)
      +l7 = L.subst(Nat, z => {Nat.is_lt(z, X) == True{} : Bool}, Nat.add(U, ML), X, he, l6)
      Empty.absurd({1n+c == 0n : Nat}, L.true_not_false(Nat.is_lt(X, X), l7, N.lt_irrefl(X)))

# a + c < a + d -> c < d
def lt_cancel_l(+a: Nat, +c: Nat, +d: Nat, +h: {Nat.is_lt(Nat.add(a, c), Nat.add(a, d)) == True{} : Bool}) -> {Nat.is_lt(c, d) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(c, d), Nat.is_lt(Nat.add(a, c), Nat.add(a, d)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(a, c), Nat.add(a, d)), Nat.is_lt(c, d), CN.lt_add_cancel(a, c, d)), h)

# the end: the second difference or the first, by the borrow
def fin_case(+mm: Nat, +b: Nat, +W: Nat, +U: Nat, +ML: Nat, +T: Nat, +S: Nat, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +hw: {Nat.add(W, Nat.add(1n+mm, 0n)) == Nat.add(U, Nat.mul(b, S)) : Nat}, +hW: {Nat.is_lt(W, S) == True{} : Bool}, +hu: {Nat.add(U, ML) == T : Nat}, +hU2: {Nat.is_lt(U, Nat.add(1n+mm, 1n+mm)) == True{} : Bool}, +q: Nat, +hq: {ML == Nat.mul(q, 1n+mm) : Nat}) -> {Bool.and(Nat.is_lt(Bool.pick(Nat, Nat.is_eq(b, 0n), W, U), 1n+mm), Nat.is_eq(Bool.pick(Nat, Nat.is_eq(b, 0n), W, U), Nat.mod(T, 1n+mm))) == True{} : Bool}:
  match b:
    case 0n:
      +P = {1n+mm : Nat}
      +e1 = tr(Nat.add(W, P), Nat.add(W, Nat.add(P, 0n)), U, M.cong_r(W, P, Nat.add(P, 0n), sy(Nat.add(P, 0n), P, N.add_zero(P))), tr(Nat.add(W, Nat.add(P, 0n)), Nat.add(U, Nat.mul(0n, S)), U, hw, N.add_zero(U)))
      +hWP = lt_cancel_l(P, W, P, L.subst(Nat, z => {Nat.is_lt(z, Nat.add(P, P)) == True{} : Bool}, U, Nat.add(P, W), tr(U, Nat.add(W, P), Nat.add(P, W), sy(Nat.add(W, P), U, e1), NA.add_comm(W, P)), hU2))
      +eT = tr(T, Nat.add(U, ML), Nat.add(Nat.mul(1n+q, P), W), sy(Nat.add(U, ML), T, hu), tr(Nat.add(U, ML), Nat.add(Nat.add(W, P), Nat.mul(q, P)), Nat.add(Nat.mul(1n+q, P), W), M.cong_add(U, Nat.add(W, P), ML, Nat.mul(q, P), sy(Nat.add(W, P), U, e1), hq), tr(Nat.add(Nat.add(W, P), Nat.mul(q, P)), Nat.add(W, Nat.add(P, Nat.mul(q, P))), Nat.add(Nat.mul(1n+q, P), W), NA.add_assoc(W, P, Nat.mul(q, P)), NA.add_comm(W, Nat.add(P, Nat.mul(q, P))))))
      +em = tr(Nat.mod(T, P), Nat.mod(Nat.add(Nat.mul(1n+q, P), W), P), W, Equal.cong(Nat, Nat, z => Nat.mod(z, P), T, Nat.add(Nat.mul(1n+q, P), W), eT), NR.mod_of(1n+q, mm, W, hWP))
      L.and_intro(Nat.is_lt(W, P), Nat.is_eq(W, Nat.mod(T, P)), hWP, L.subst(Nat, z => {Nat.is_eq(W, z) == True{} : Bool}, W, Nat.mod(T, P), sy(Nat.mod(T, P), W, em), N.is_eq_refl(W)))
    case 1n+ +c:
      +P = {1n+mm : Nat}
      +e1 = tr(Nat.add(W, P), Nat.add(W, Nat.add(P, 0n)), Nat.add(U, Nat.mul(1n+c, S)), M.cong_r(W, P, Nat.add(P, 0n), sy(Nat.add(P, 0n), P, N.add_zero(P))), hw)
      +l1 = N.le_lt_trans(Nat.add(U, S), Nat.add(U, Nat.mul(1n+c, S)), Nat.add(S, P), N.le_add_left(S, Nat.mul(1n+c, S), U, N.le_add_right(S, Nat.mul(c, S))), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(S, P)) == True{} : Bool}, Nat.add(W, P), Nat.add(U, Nat.mul(1n+c, S)), e1, N.lt_add_r2(W, S, P, hW)))
      +hUP = lt_cancel_l(S, U, P, L.subst(Nat, z => {Nat.is_lt(z, Nat.add(S, P)) == True{} : Bool}, Nat.add(U, S), Nat.add(S, U), NA.add_comm(U, S), l1))
      +eT = tr(T, Nat.add(U, ML), Nat.add(Nat.mul(q, P), U), sy(Nat.add(U, ML), T, hu), tr(Nat.add(U, ML), Nat.add(ML, U), Nat.add(Nat.mul(q, P), U), NA.add_comm(U, ML), M.cong_l(ML, Nat.mul(q, P), U, hq)))
      +em = tr(Nat.mod(T, P), Nat.mod(Nat.add(Nat.mul(q, P), U), P), U, Equal.cong(Nat, Nat, z => Nat.mod(z, P), T, Nat.add(Nat.mul(q, P), U), eT), NR.mod_of(q, mm, U, hUP))
      L.and_intro(Nat.is_lt(U, P), Nat.is_eq(U, Nat.mod(T, P)), hUP, L.subst(Nat, z => {Nat.is_eq(U, z) == True{} : Bool}, U, Nat.mod(T, P), sy(Nat.mod(T, P), U, em), N.is_eq_refl(U)))

# ---- selection by the borrow ----

def sel_pick(+b: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +hl: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {LS.sel(b, xs, ys) == Bool.pick(List<&2, Nat>, Nat.is_eq(b, 0n), xs, ys) : List<&2, Nat>}:
  match b:
    case 0n:
      OP.sel0(xs, ys, hl)
    case 1n:
      OP.sel1(xs, ys, hl)
    case 2n+c:
      Empty.absurd({LS.sel(2n+c, xs, ys) == ys : List<&2, Nat>}, L.false_true(hb))

def lv_pick(+c: Bool, +xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {FV.lv(Bool.pick(List<&2, Nat>, c, xs, ys)) == Bool.pick(Nat, c, FV.lv(xs), FV.lv(ys)) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def below_pick(+c: Bool, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hx: {FV.below(xs, b) == True{} : Bool}, +hy: {FV.below(ys, b) == True{} : Bool}) -> {FV.below(Bool.pick(List<&2, Nat>, c, xs, ys), b) == True{} : Bool}:
  match c:
    case True{}:
      hx
    case False{}:
      hy

def sc35(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.mul(WD.sc(18n, one), R) == WD.sc(35n, one) : Nat}:
  PS.at_r(one, R, hR, z => {Nat.mul(WD.sc(18n, one), z) == WD.sc(35n, one) : Nat}, PW.scsc(18n, 17n, one, h1))

def ae35(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_le(Nat.add(WD.sc(35n, one), WD.sc(19n, one)), Nat.mul(R, WD.sc(19n, one))) == True{} : Bool}:
  +a = PW.add_le_dbl(WD.sc(35n, one), WD.sc(19n, one), 35n, one, N.le_refl(WD.sc(35n, one)), PW.le_sc(16n, 19n, one))
  +b = L.subst(Nat, z => {Nat.is_le(Nat.add(WD.sc(35n, one), WD.sc(19n, one)), z) == True{} : Bool}, WD.sc(36n, one), Nat.mul(WD.sc(17n, one), WD.sc(19n, one)), sy(Nat.mul(WD.sc(17n, one), WD.sc(19n, one)), WD.sc(36n, one), PW.scsc(17n, 19n, one, h1)), a)
  PS.at_r(one, R, hR, z => {Nat.is_le(Nat.add(WD.sc(35n, one), WD.sc(19n, one)), Nat.mul(z, WD.sc(19n, one))) == True{} : Bool}, b)

def r_lt_16(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.is_lt(WD.sc(16n, one), R) == True{} : Bool}:
  PS.at_r(one, R, hR, z => {Nat.is_lt(WD.sc(16n, one), z) == True{} : Bool}, PW.lt_sc(0n, 16n, one, h1))

# ---- step_fin ----

def step_fin_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +mm: Nat, +l: List<&2, Nat>, +hLv: {FV.lv(l) == 1n+mm : Nat}, +hLb: {FV.below(l, R) == True{} : Bool}, +hLl: {PS.ln(l) == 15n : Nat}, +hL253: {Nat.is_lt(1n+mm, WD.sc(253n, one)) == True{} : Bool}, +t: List<&2, Nat>, +T: Nat, +hT: {FV.lv(t) == T : Nat}, +htb: {FV.below(t, R) == True{} : Bool}, +htl: {PS.ln(t) == 16n : Nat}, +m: Nat, +hm18: {Nat.is_lt(m, WD.sc(18n, one)) == True{} : Bool}, +hmL: {Nat.is_le(Nat.mul(m, 1n+mm), T) == True{} : Bool}, +hT2: {Nat.is_lt(T, Nat.add(Nat.mul(m, 1n+mm), Nat.add(1n+mm, 1n+mm))) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(ESC.step_fin(R, l, t, LS.carry(R, LS.scal(m, l), 0n)), R), Nat.is_lt(FV.lv(ESC.step_fin(R, l, t, LS.carry(R, LS.scal(m, l), 0n))), 1n+mm)), Nat.is_eq(FV.lv(ESC.step_fin(R, l, t, LS.carry(R, LS.scal(m, l), 0n))), Nat.mod(T, 1n+mm))) == True{} : Bool}:
  +P = {1n+mm : Nat}
  +sc = LS.scal(m, l)
  +cr = LS.carry(R, sc, 0n)
  +cl = LS.cr_limbs(cr)
  +cc = LS.cr_out(cr)
  +ml = LS.app(cl, [cc])
  +ML = Nat.mul(m, P)
  +S15 = NL.sh(15n, one)
  +S16 = NL.sh(16n, one)
  +lsc = tr(PS.ln(sc), PS.ln(l), 15n, scal_len(m, l), hLl)
  +lcl = tr(PS.ln(cl), PS.ln(sc), 15n, CN.carry_len(R, sc, 0n), lsc)
  +vsc = tr(FV.lv(sc), Nat.mul(m, FV.lv(l)), ML, NL.lv_scal(m, l), Equal.cong(Nat, Nat, z => Nat.mul(m, z), FV.lv(l), P, hLv))
  +cv = CA.carry_val(one, h1, R, hR, sc, 0n)
  +esh = shl_mul(one, h1, sc, 15n, lsc, cc)
  +e_cl = tr(Nat.add(FV.lv(cl), Nat.mul(cc, S15)), Nat.add(FV.lv(cl), CA.shl(sc, cc)), ML, M.cong_r(FV.lv(cl), Nat.mul(cc, S15), CA.shl(sc, cc), sy(CA.shl(sc, cc), Nat.mul(cc, S15), esh)), tr(Nat.add(FV.lv(cl), CA.shl(sc, cc)), Nat.add(FV.lv(sc), 0n), ML, cv, tr(Nat.add(FV.lv(sc), 0n), FV.lv(sc), ML, N.add_zero(FV.lv(sc)), vsc)))
  +vml = tr(FV.lv(ml), Nat.add(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc]))), ML, lv_app(cl, [cc]), tr(Nat.add(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc]))), Nat.add(FV.lv(cl), Nat.mul(cc, S15)), ML, M.cong_r(FV.lv(cl), NL.sh(PS.ln(cl), FV.lv([cc])), Nat.mul(cc, S15), tr(NL.sh(PS.ln(cl), FV.lv([cc])), NL.sh(15n, cc), Nat.mul(cc, S15), tr(NL.sh(PS.ln(cl), FV.lv([cc])), NL.sh(15n, FV.lv([cc])), NL.sh(15n, cc), Equal.cong(Nat, Nat, z => NL.sh(z, FV.lv([cc])), PS.ln(cl), 15n, lcl), Equal.cong(Nat, Nat, z => NL.sh(15n, z), FV.lv([cc]), cc, lv1(cc))), sh_mul(one, h1, 15n, cc))), e_cl))
  +hsc35 = L.subst(Nat, z => {FV.below(sc, z) == True{} : Bool}, Nat.mul(WD.sc(18n, one), R), WD.sc(35n, one), sc35(one, h1, R, hR), NL.scal_below(m, l, WD.sc(18n, one), R, hm18, hLb))
  +hcb = CA.carry_below(one, h1, R, hR, sc, 0n, WD.sc(35n, one), WD.sc(19n, one), hsc35, PW.sc_pos(19n, one, h1), ae35(one, h1, R, hR))
  +hcl = L.and_left(FV.below(cl, R), Nat.is_lt(cc, WD.sc(19n, one)), hcb)
  +hML = L.subst(Nat, z => {Nat.is_lt(ML, z) == True{} : Bool}, Nat.mul(WD.sc(18n, one), WD.sc(253n, one)), Nat.mul(WD.sc(16n, one), S15), tr(Nat.mul(WD.sc(18n, one), WD.sc(253n, one)), WD.sc(271n, one), Nat.mul(WD.sc(16n, one), S15), PW.scsc(18n, 253n, one, h1), tr(WD.sc(271n, one), Nat.mul(WD.sc(16n, one), WD.sc(255n, one)), Nat.mul(WD.sc(16n, one), S15), sy(Nat.mul(WD.sc(16n, one), WD.sc(255n, one)), WD.sc(271n, one), PW.scsc(16n, 255n, one, h1)), Equal.cong(Nat, Nat, z => Nat.mul(WD.sc(16n, one), z), WD.sc(255n, one), S15, sy(S15, WD.sc(255n, one), NL.sh15(one))))), NL.lt_mul2(m, P, WD.sc(18n, one), WD.sc(253n, one), hm18, hL253))
  +hcc16 = CN.mul_lt_cancel(cc, WD.sc(16n, one), S15, N.le_lt_trans(Nat.mul(cc, S15), ML, Nat.mul(WD.sc(16n, one), S15), L.subst(Nat, z => {Nat.is_le(Nat.mul(cc, S15), z) == True{} : Bool}, Nat.add(FV.lv(cl), Nat.mul(cc, S15)), ML, e_cl, NL.le_add_l(FV.lv(cl), Nat.mul(cc, S15))), hML))
  +hccR = N.lt_trans(cc, WD.sc(16n, one), R, hcc16, r_lt_16(one, h1, R, hR))
  +hml = BY.app_below(cl, [cc], R, hcl, NL.below_con(cc, Nil{}, R, hccR, {==}))
  +lml = tr(PS.ln(ml), Nat.add(PS.ln(cl), 1n), 16n, BY.app_len(cl, [cc]), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), PS.ln(cl), 15n, lcl))
  +hlt = tr(PS.ln(t), 16n, PS.ln(ml), htl, sy(PS.ln(ml), 16n, lml))
  +us = ESC.subb(R, t, ml, 0n)
  +u = ESC.sb_limbs(us)
  +b1 = ESC.sb_out(us)
  +su = SB.subb_val(one, h1, R, hR, t, ml, 0n, htb, hml, {==}, hlt)
  +so = SB.subb_ok(one, h1, R, hR, t, ml, 0n, htb, {==})
  +hub = L.and_left(FV.below(u, R), Nat.is_le(b1, 1n), so)
  +hb1 = L.and_right(FV.below(u, R), Nat.is_le(b1, 1n), so)
  +lu = tr(PS.ln(u), PS.ln(t), 16n, SB.subb_len(R, t, ml, 0n, hlt), htl)
  +e_u = tr(Nat.add(FV.lv(u), ML), Nat.add(FV.lv(u), Nat.add(FV.lv(ml), 0n)), Nat.add(T, Nat.mul(b1, S16)), M.cong_r(FV.lv(u), ML, Nat.add(FV.lv(ml), 0n), sy(Nat.add(FV.lv(ml), 0n), ML, tr(Nat.add(FV.lv(ml), 0n), FV.lv(ml), ML, N.add_zero(FV.lv(ml)), vml))), tr(Nat.add(FV.lv(u), Nat.add(FV.lv(ml), 0n)), Nat.add(FV.lv(t), CA.shl(t, b1)), Nat.add(T, Nat.mul(b1, S16)), su, M.cong_add(FV.lv(t), T, CA.shl(t, b1), Nat.mul(b1, S16), hT, shl_mul(one, h1, t, 16n, htl, b1))))
  +hU = L.subst(Nat, z => {Nat.is_lt(FV.lv(u), z) == True{} : Bool}, NL.sh(PS.ln(u), one), S16, Equal.cong(Nat, Nat, z => NL.sh(z, one), PS.ln(u), 16n, lu), CN.lv_lt(one, h1, R, hR, u, hub))
  +b1z = borrow0(b1, FV.lv(u), ML, T, S16, hb1, e_u, hU, hmL)
  +e_u0 = tr(Nat.add(FV.lv(u), ML), Nat.add(T, Nat.mul(b1, S16)), T, e_u, tr(Nat.add(T, Nat.mul(b1, S16)), Nat.add(T, Nat.mul(0n, S16)), T, M.cong_r(T, Nat.mul(b1, S16), Nat.mul(0n, S16), Equal.cong(Nat, Nat, z => Nat.mul(z, S16), b1, 0n, b1z)), N.add_zero(T)))
  +hU2 = lt_cancel_l(ML, FV.lv(u), Nat.add(P, P), L.subst(Nat, z => {Nat.is_lt(z, Nat.add(ML, Nat.add(P, P))) == True{} : Bool}, T, Nat.add(ML, FV.lv(u)), tr(T, Nat.add(FV.lv(u), ML), Nat.add(ML, FV.lv(u)), sy(Nat.add(FV.lv(u), ML), T, e_u0), NA.add_comm(FV.lv(u), ML)), hT2))
  +lL = LS.app(l, [0n])
  +vlL = tr(FV.lv(lL), Nat.add(FV.lv(l), NL.sh(PS.ln(l), FV.lv([0n]))), P, lv_app(l, [0n]), tr(Nat.add(FV.lv(l), NL.sh(PS.ln(l), FV.lv([0n]))), Nat.add(FV.lv(l), 0n), P, M.cong_r(FV.lv(l), NL.sh(PS.ln(l), FV.lv([0n])), 0n, tr(NL.sh(PS.ln(l), FV.lv([0n])), NL.sh(PS.ln(l), 0n), 0n, Equal.cong(Nat, Nat, z => NL.sh(PS.ln(l), z), FV.lv([0n]), 0n, lv1(0n)), NL.sh_zero(PS.ln(l)))), tr(Nat.add(FV.lv(l), 0n), FV.lv(l), P, N.add_zero(FV.lv(l)), hLv)))
  +hlL = BY.app_below(l, [0n], R, hLb, NL.below_con(0n, Nil{}, R, CA.r_pos(one, h1, R, hR), {==}))
  +llL = tr(PS.ln(lL), Nat.add(PS.ln(l), 1n), 16n, BY.app_len(l, [0n]), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), PS.ln(l), 15n, hLl))
  +hul = tr(PS.ln(u), 16n, PS.ln(lL), lu, sy(PS.ln(lL), 16n, llL))
  +ws = ESC.subb(R, u, lL, 0n)
  +w = ESC.sb_limbs(ws)
  +b2 = ESC.sb_out(ws)
  +sw = SB.subb_val(one, h1, R, hR, u, lL, 0n, hub, hlL, {==}, hul)
  +sow = SB.subb_ok(one, h1, R, hR, u, lL, 0n, hub, {==})
  +hwb = L.and_left(FV.below(w, R), Nat.is_le(b2, 1n), sow)
  +hb2 = L.and_right(FV.below(w, R), Nat.is_le(b2, 1n), sow)
  +lw = tr(PS.ln(w), PS.ln(u), 16n, SB.subb_len(R, u, lL, 0n, hul), lu)
  +e_w = tr(Nat.add(FV.lv(w), Nat.add(P, 0n)), Nat.add(FV.lv(w), Nat.add(FV.lv(lL), 0n)), Nat.add(FV.lv(u), Nat.mul(b2, S16)), M.cong_r(FV.lv(w), Nat.add(P, 0n), Nat.add(FV.lv(lL), 0n), M.cong_l(P, FV.lv(lL), 0n, sy(FV.lv(lL), P, vlL))), tr(Nat.add(FV.lv(w), Nat.add(FV.lv(lL), 0n)), Nat.add(FV.lv(u), CA.shl(u, b2)), Nat.add(FV.lv(u), Nat.mul(b2, S16)), sw, M.cong_r(FV.lv(u), CA.shl(u, b2), Nat.mul(b2, S16), shl_mul(one, h1, u, 16n, lu, b2))))
  +hW = L.subst(Nat, z => {Nat.is_lt(FV.lv(w), z) == True{} : Bool}, NL.sh(PS.ln(w), one), S16, Equal.cong(Nat, Nat, z => NL.sh(z, one), PS.ln(w), 16n, lw), CN.lv_lt(one, h1, R, hR, w, hwb))
  +fc = fin_case(mm, b2, FV.lv(w), FV.lv(u), ML, T, S16, hb2, e_w, hW, e_u0, hU2, m, {==})
  +c = Nat.is_eq(b2, 0n)
  +pk = Bool.pick(List<&2, Nat>, c, w, u)
  +V = Bool.pick(Nat, c, FV.lv(w), FV.lv(u))
  +esel = sel_pick(b2, w, u, hb2, tr(PS.ln(w), 16n, PS.ln(u), lw, sy(PS.ln(u), 16n, lu)))
  +r16 = LS.sel(b2, w, u)
  +ev16 = tr(FV.lv(r16), FV.lv(pk), V, Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), r16, pk, esel), lv_pick(c, w, u))
  +hVP = L.and_left(Nat.is_lt(V, P), Nat.is_eq(V, Nat.mod(T, P)), fc)
  +hVm = L.and_right(Nat.is_lt(V, P), Nat.is_eq(V, Nat.mod(T, P)), fc)
  +hS15 = N.lt_le_trans(V, P, S15, hVP, N.lt_le(P, S15, N.lt_le_trans(P, WD.sc(253n, one), S15, hL253, L.subst(Nat, z => {Nat.is_le(WD.sc(253n, one), z) == True{} : Bool}, WD.sc(255n, one), S15, sy(S15, WD.sc(255n, one), NL.sh15(one)), PW.le_sc(2n, 253n, one)))))
  +ev = tr(FV.lv(LS.take(15n, r16)), FV.lv(r16), V, take15(one, h1, r16, L.subst(Nat, z => {Nat.is_lt(z, S15) == True{} : Bool}, V, FV.lv(r16), sy(FV.lv(r16), V, ev16), hS15)), ev16)
  +hb16 = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, pk, r16, Equal.sym(List<&2, Nat>, r16, pk, esel), below_pick(c, w, u, R, hwb, hub))
  +hbr = NL.take_below(15n, r16, R, hb16)
  +hlt2 = L.subst(Nat, z => {Nat.is_lt(z, P) == True{} : Bool}, V, FV.lv(LS.take(15n, r16)), sy(FV.lv(LS.take(15n, r16)), V, ev), hVP)
  +heq = L.subst(Nat, z => {Nat.is_eq(z, Nat.mod(T, P)) == True{} : Bool}, V, FV.lv(LS.take(15n, r16)), sy(FV.lv(LS.take(15n, r16)), V, ev), hVm)
  L.and_intro(Bool.and(FV.below(LS.take(15n, r16), R), Nat.is_lt(FV.lv(LS.take(15n, r16)), P)), Nat.is_eq(FV.lv(LS.take(15n, r16)), Nat.mod(T, P)), L.and_intro(FV.below(LS.take(15n, r16), R), Nat.is_lt(FV.lv(LS.take(15n, r16)), P), hbr, hlt2), heq)

# ---- the quotient estimate ----

def nil_of(+xs: List<&2, Nat>, +h: {PS.ln(xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, xt}:
      Empty.absurd({Con{x, xt} == Nil{} : List<&2, Nat>}, N.succ_zero(PS.ln(xt), h))

# drop(k, xs) for len(xs) == k + 2: its two last limbs
def drop2(+k: Nat, +xs: List<&2, Nat>, +hl: {PS.ln(xs) == Nat.add(k, 2n) : Nat}) -> {LS.drop(k, xs) == Con{ESC.nth(k, xs), Con{ESC.nth(1n+k, xs), Nil{}}} : List<&2, Nat>}:
  match k xs:
    case _ Nil{}:
      Empty.absurd({Nil{} == Con{0n, Con{0n, Nil{}}} : List<&2, Nat>}, N.zero_succ(Nat.add(k, 1n), tr(0n, Nat.add(k, 2n), 1n+Nat.add(k, 1n), hl, N.add_succ(k, 1n))))
    case 0n Con{+x, Nil{}}:
      Empty.absurd({Con{x, Nil{}} == Con{x, Con{0n, Nil{}}} : List<&2, Nat>}, N.zero_succ(0n, N.succ_inj(0n, 1n, hl)))
    case 0n Con{+x, Con{+y, +yt}}:
      +h0 = N.succ_inj(PS.ln(yt), 0n, N.succ_inj(1n+PS.ln(yt), 1n, hl))
      +enil = nil_of(yt, h0)
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{x, Con{y, z}}, yt, Nil{}, enil)
    case 1n+ +j Con{+x, +xt}:
      drop2(j, xt, N.succ_inj(PS.ln(xt), Nat.add(j, 2n), hl))

# R / 8 == 2^14
def r14(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}) -> {Nat.div(R, 8n) == WD.sc(14n, one) : Nat}:
  +s = WD.sc(14n, one)
  +e = tr(R, WD.sc(17n, one), Nat.add(Nat.mul(s, 8n), 0n), hR, tr(WD.sc(17n, one), WD.sc(3n, s), Nat.add(Nat.mul(s, 8n), 0n), sy(WD.sc(3n, s), WD.sc(17n, one), M.sc_sc(3n, 14n, one)), tr(WD.sc(3n, s), Nat.mul(s, 8n), Nat.add(Nat.mul(s, 8n), 0n), sy(Nat.mul(s, 8n), WD.sc(3n, s), AR.mul_sc(3n, s)), sy(Nat.add(Nat.mul(s, 8n), 0n), Nat.mul(s, 8n), N.add_zero(Nat.mul(s, 8n))))))
  tr(Nat.div(R, 8n), Nat.div(Nat.add(Nat.mul(s, 8n), 0n), 8n), s, Equal.cong(Nat, Nat, z => Nat.div(z, 8n), R, Nat.add(Nat.mul(s, 8n), 0n), e), NR.div_of(s, 7n, 0n, {==}))

def LD_pos(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat) -> {1n+Nat.sub(WD.sc(k, one), 1n) == WD.sc(k, one) : Nat}:
  PW.pos_succ(one, h1, k)

# q = x div 2^14: q 2^14 <= x and x + 1 <= (q + 1) 2^14
def flo(+one: Nat, +h1: {one == 1n : Nat}, +x: Nat) -> {Bool.and(Nat.is_le(Nat.mul(Nat.div(x, WD.sc(14n, one)), WD.sc(14n, one)), x), Nat.is_le(Nat.add(x, one), Nat.mul(1n+Nat.div(x, WD.sc(14n, one)), WD.sc(14n, one)))) == True{} : Bool}:
  +s = WD.sc(14n, one)
  +b = Nat.sub(s, 1n)
  +hb = LD_pos(one, h1, 14n)
  +q = Nat.div(x, s)
  +r = Nat.mod(x, s)
  +e = L.subst(Nat, t => {x == Nat.add(Nat.mul(Nat.div(x, t), t), Nat.mod(x, t)) : Nat}, 1n+b, s, hb, NR.dm_eq(b, x))
  +hr = L.subst(Nat, t => {Nat.is_lt(Nat.mod(x, t), t) == True{} : Bool}, 1n+b, s, hb, NR.dm_lt(b, x))
  +l1 = L.subst(Nat, t => {Nat.is_le(Nat.mul(q, s), t) == True{} : Bool}, Nat.add(Nat.mul(q, s), r), x, sy(x, Nat.add(Nat.mul(q, s), r), e), N.le_add_right(Nat.mul(q, s), r))
  +l2 = N.le_trans(Nat.add(x, one), Nat.add(Nat.add(Nat.mul(q, s), r), one), Nat.mul(1n+q, s), L.subst(Nat, t => {Nat.is_le(Nat.add(t, one), Nat.add(Nat.add(Nat.mul(q, s), r), one)) == True{} : Bool}, Nat.add(Nat.mul(q, s), r), x, sy(x, Nat.add(Nat.mul(q, s), r), e), N.le_refl(Nat.add(Nat.add(Nat.mul(q, s), r), one))), L.subst(Nat, t => {Nat.is_le(t, Nat.mul(1n+q, s)) == True{} : Bool}, Nat.add(Nat.mul(q, s), Nat.add(r, one)), Nat.add(Nat.add(Nat.mul(q, s), r), one), sy(Nat.add(Nat.add(Nat.mul(q, s), r), one), Nat.add(Nat.mul(q, s), Nat.add(r, one)), NA.add_assoc(Nat.mul(q, s), r, one)), L.subst(Nat, t => {Nat.is_le(Nat.add(Nat.mul(q, s), Nat.add(r, one)), t) == True{} : Bool}, Nat.add(Nat.mul(q, s), s), Nat.mul(1n+q, s), tr(Nat.add(Nat.mul(q, s), s), Nat.add(s, Nat.mul(q, s)), Nat.mul(1n+q, s), NA.add_comm(Nat.mul(q, s), s), {==}), N.le_add_left(Nat.add(r, one), s, Nat.mul(q, s), PW.succ_le(one, h1, r, s, hr)))))
  L.and_intro(Nat.is_le(Nat.mul(q, s), x), Nat.is_le(Nat.add(x, one), Nat.mul(1n+q, s)), l1, l2)


# with m = qh - 1: m P <= T < m P + 2 P, from qh Q <= T < (qh + 1) Q,
# Q <= P <= Q + c and qh c <= Q
def est(+qh: Nat, +P: Nat, +Q: Nat, +c: Nat, +T: Nat, +hq1: {Nat.is_le(Nat.mul(qh, Q), T) == True{} : Bool}, +hq2: {Nat.is_lt(T, Nat.mul(1n+qh, Q)) == True{} : Bool}, +hlo: {Nat.is_le(Q, P) == True{} : Bool}, +hhi: {Nat.is_le(P, Nat.add(Q, c)) == True{} : Bool}, +hc: {Nat.is_le(Nat.mul(qh, c), Q) == True{} : Bool}) -> {Bool.and(Nat.is_le(Nat.mul(Nat.sub(qh, 1n), P), T), Nat.is_lt(T, Nat.add(Nat.mul(Nat.sub(qh, 1n), P), Nat.add(P, P)))) == True{} : Bool}:
  match qh:
    case 0n:
      +h2 = L.subst(Nat, z => {Nat.is_lt(T, z) == True{} : Bool}, Nat.add(Q, 0n), Q, N.add_zero(Q), hq2)
      L.and_intro(Nat.is_le(0n, T), Nat.is_lt(T, Nat.add(P, P)), N.zero_le(T), N.lt_le_trans(T, Q, Nat.add(P, P), h2, N.le_trans(Q, P, Nat.add(P, P), hlo, N.le_add_right(P, P))))
    case 1n+ +k:
      +l1 = PW.mul_le_r(k, P, Nat.add(Q, c), hhi)
      +l2 = L.subst(Nat, z => {Nat.is_le(Nat.mul(k, P), z) == True{} : Bool}, Nat.mul(k, Nat.add(Q, c)), Nat.add(Nat.mul(k, Q), Nat.mul(k, c)), NA.mul_add_left(k, Q, c), l1)
      +l3 = N.le_trans(Nat.mul(k, c), Nat.mul(1n+k, c), Q, NL.le_add_l(c, Nat.mul(k, c)), hc)
      +l4 = N.le_trans(Nat.mul(k, P), Nat.add(Nat.mul(k, Q), Nat.mul(k, c)), Nat.add(Nat.mul(k, Q), Q), l2, N.le_add_left(Nat.mul(k, c), Q, Nat.mul(k, Q), l3))
      +l5 = L.subst(Nat, z => {Nat.is_le(Nat.mul(k, P), z) == True{} : Bool}, Nat.add(Nat.mul(k, Q), Q), Nat.mul(1n+k, Q), NA.add_comm(Nat.mul(k, Q), Q), l4)
      +le = N.le_trans(Nat.mul(k, P), Nat.mul(1n+k, Q), T, l5, hq1)
      +u1 = M.le_add2(Q, Nat.add(Q, Nat.mul(k, Q)), P, Nat.add(P, Nat.mul(k, P)), hlo, M.le_add2(Q, Nat.mul(k, Q), P, Nat.mul(k, P), hlo, PW.mul_le_r(k, Q, P, hlo)))
      +eP = tr(Nat.add(P, Nat.add(P, Nat.mul(k, P))), Nat.add(Nat.add(P, P), Nat.mul(k, P)), Nat.add(Nat.mul(k, P), Nat.add(P, P)), sy(Nat.add(Nat.add(P, P), Nat.mul(k, P)), Nat.add(P, Nat.add(P, Nat.mul(k, P))), NA.add_assoc(P, P, Nat.mul(k, P))), NA.add_comm(Nat.add(P, P), Nat.mul(k, P)))
      +lt = N.lt_le_trans(T, Nat.mul(2n+k, Q), Nat.add(Nat.mul(k, P), Nat.add(P, P)), hq2, L.subst(Nat, z => {Nat.is_le(Nat.mul(2n+k, Q), z) == True{} : Bool}, Nat.add(P, Nat.add(P, Nat.mul(k, P))), Nat.add(Nat.mul(k, P), Nat.add(P, P)), eP, u1))
      +g = L.and_intro(Nat.is_le(Nat.mul(k, P), T), Nat.is_lt(T, Nat.add(Nat.mul(k, P), Nat.add(P, P))), le, lt)
      L.subst(Nat, z => {Bool.and(Nat.is_le(Nat.mul(z, P), T), Nat.is_lt(T, Nat.add(Nat.mul(z, P), Nat.add(P, P)))) == True{} : Bool}, k, Nat.sub(k, 0n), sy(Nat.sub(k, 0n), k, N.sub_zero(k)), g)

# ---- one step ----

def add1(+y: Nat) -> {Nat.add(y, 1n) == 1n+y : Nat}:
  SB.add1(y)

def step_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +mm: Nat, +l: List<&2, Nat>, +hLv: {FV.lv(l) == 1n+mm : Nat}, +hLb: {FV.below(l, R) == True{} : Bool}, +hLl: {PS.ln(l) == 15n : Nat}, +hL253: {Nat.is_lt(1n+mm, WD.sc(253n, one)) == True{} : Bool}, +hlo: {Nat.is_le(WD.sc(252n, one), 1n+mm) == True{} : Bool}, +hhi: {Nat.is_le(1n+mm, Nat.add(WD.sc(252n, one), WD.sc(125n, one))) == True{} : Bool}, +acc: List<&2, Nat>, +hab: {FV.below(acc, R) == True{} : Bool}, +hal: {PS.ln(acc) == 15n : Nat}, +hav: {Nat.is_lt(FV.lv(acc), 1n+mm) == True{} : Bool}, +d: Nat, +hd: {Nat.is_lt(d, R) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(ESC.step(R, l, acc, d), R), Nat.is_lt(FV.lv(ESC.step(R, l, acc, d)), 1n+mm)), Nat.is_eq(FV.lv(ESC.step(R, l, acc, d)), Nat.mod(Nat.add(d, C.shift(17n, FV.lv(acc))), 1n+mm))) == True{} : Bool}:
  +P = {1n+mm : Nat}
  +t = {Con{d, acc} : List<&2, Nat>}
  +T = Nat.add(d, C.shift(17n, FV.lv(acc)))
  +a13 = ESC.nth(13n, acc)
  +a14 = ESC.nth(14n, acc)
  +x = Nat.add(a13, Nat.mul(a14, R))
  +qh = Nat.div(x, Nat.div(R, 8n))
  +m = Nat.sub(qh, 1n)
  +s14 = WD.sc(14n, one)
  +S14 = NL.sh(14n, one)
  +Q = Nat.mul(s14, S14)
  +eqh = Equal.cong(Nat, Nat, z => Nat.div(x, z), Nat.div(R, 8n), s14, r14(one, h1, R, hR))
  +F = flo(one, h1, x)
  +F1 = L.subst(Nat, z => {Nat.is_le(Nat.mul(z, s14), x) == True{} : Bool}, Nat.div(x, s14), qh, sy(qh, Nat.div(x, s14), eqh), L.and_left(Nat.is_le(Nat.mul(Nat.div(x, s14), s14), x), Nat.is_le(Nat.add(x, one), Nat.mul(1n+Nat.div(x, s14), s14)), F))
  +F2 = L.subst(Nat, z => {Nat.is_le(Nat.add(x, one), Nat.mul(1n+z, s14)) == True{} : Bool}, Nat.div(x, s14), qh, sy(qh, Nat.div(x, s14), eqh), L.and_right(Nat.is_le(Nat.mul(Nat.div(x, s14), s14), x), Nat.is_le(Nat.add(x, one), Nat.mul(1n+Nat.div(x, s14), s14)), F))
  +t13 = LS.take(13n, acc)
  +lo = FV.lv(Con{d, t13})
  +es = NL.lv_split(13n, acc)
  +ed = drop2(13n, acc, hal)
  +ex = tr(FV.lv(LS.drop(13n, acc)), FV.lv([a13, a14]), x, Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), LS.drop(13n, acc), [a13, a14], ed), M.cong_r(a13, C.shift(17n, Nat.add(a14, C.shift(17n, 0n))), Nat.mul(a14, R), tr(C.shift(17n, Nat.add(a14, C.shift(17n, 0n))), C.shift(17n, a14), Nat.mul(a14, R), M.cong_sc(17n, Nat.add(a14, C.shift(17n, 0n)), a14, N.add_zero(a14)), tr(C.shift(17n, a14), Nat.mul(R, a14), Nat.mul(a14, R), sy(Nat.mul(R, a14), C.shift(17n, a14), CA.mul_r(one, h1, R, hR, a14)), NA.mul_comm(R, a14)))))
  +X13 = FV.lv(t13)
  +D13 = NL.sh(13n, FV.lv(LS.drop(13n, acc)))
  +eT = tr(T, Nat.add(d, C.shift(17n, Nat.add(X13, D13))), Nat.add(lo, Nat.mul(x, S14)), M.cong_r(d, C.shift(17n, FV.lv(acc)), C.shift(17n, Nat.add(X13, D13)), M.cong_sc(17n, FV.lv(acc), Nat.add(X13, D13), es)), tr(Nat.add(d, C.shift(17n, Nat.add(X13, D13))), Nat.add(lo, C.shift(17n, D13)), Nat.add(lo, Nat.mul(x, S14)), tr(Nat.add(d, C.shift(17n, Nat.add(X13, D13))), Nat.add(d, Nat.add(C.shift(17n, X13), C.shift(17n, D13))), Nat.add(lo, C.shift(17n, D13)), M.cong_r(d, C.shift(17n, Nat.add(X13, D13)), Nat.add(C.shift(17n, X13), C.shift(17n, D13)), sy(Nat.add(C.shift(17n, X13), C.shift(17n, D13)), C.shift(17n, Nat.add(X13, D13)), M.sc_add(17n, X13, D13))), sy(Nat.add(lo, C.shift(17n, D13)), Nat.add(d, Nat.add(C.shift(17n, X13), C.shift(17n, D13))), NA.add_assoc(d, C.shift(17n, X13), C.shift(17n, D13)))), M.cong_r(lo, C.shift(17n, D13), Nat.mul(x, S14), tr(NL.sh(14n, FV.lv(LS.drop(13n, acc))), NL.sh(14n, x), Nat.mul(x, S14), Equal.cong(Nat, Nat, z => NL.sh(14n, z), FV.lv(LS.drop(13n, acc)), x, ex), sh_mul(one, h1, 14n, x)))))
  +hlo14 = L.subst(Nat, z => {Nat.is_lt(lo, NL.sh(z, one)) == True{} : Bool}, PS.ln(Con{d, t13}), 14n, Equal.cong(Nat, Nat, z => 1n+z, PS.ln(t13), 13n, take_len(13n, 2n, acc, hal)), CN.lv_lt(one, h1, R, hR, Con{d, t13}, NL.below_con(d, t13, R, hd, NL.take_below(13n, acc, R, hab))))
  +hq1 = L.subst(Nat, z => {Nat.is_le(z, T) == True{} : Bool}, Nat.mul(Nat.mul(qh, s14), S14), Nat.mul(qh, Q), NA.mul_assoc(qh, s14, S14), N.le_trans(Nat.mul(Nat.mul(qh, s14), S14), Nat.mul(x, S14), T, AR.mul_le(Nat.mul(qh, s14), x, S14, F1), L.subst(Nat, z => {Nat.is_le(Nat.mul(x, S14), z) == True{} : Bool}, Nat.add(lo, Nat.mul(x, S14)), T, sy(T, Nat.add(lo, Nat.mul(x, S14)), eT), NL.le_add_l(lo, Nat.mul(x, S14)))))
  +F2b = L.subst(Nat, z => {Nat.is_le(z, Nat.mul(1n+qh, s14)) == True{} : Bool}, Nat.add(x, one), 1n+x, tr(Nat.add(x, one), Nat.add(x, 1n), 1n+x, M.cong_r(x, one, 1n, h1), add1(x)), F2)
  +hq2a = N.lt_le_trans(T, Nat.mul(1n+x, S14), Nat.mul(Nat.mul(1n+qh, s14), S14), L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(1n+x, S14)) == True{} : Bool}, Nat.add(lo, Nat.mul(x, S14)), T, sy(T, Nat.add(lo, Nat.mul(x, S14)), eT), N.lt_add_r2(lo, S14, Nat.mul(x, S14), hlo14)), AR.mul_le(1n+x, Nat.mul(1n+qh, s14), S14, F2b))
  +hq2 = L.subst(Nat, z => {Nat.is_lt(T, z) == True{} : Bool}, Nat.mul(Nat.mul(1n+qh, s14), S14), Nat.mul(1n+qh, Q), NA.mul_assoc(1n+qh, s14, S14), hq2a)
  +eQ252 = tr(Q, Nat.mul(s14, WD.sc(238n, one)), WD.sc(252n, one), Equal.cong(Nat, Nat, z => Nat.mul(s14, z), S14, WD.sc(238n, one), NL.sh_sc(14n, one)), PW.scsc(14n, 238n, one, h1))
  +hloQ = L.subst(Nat, z => {Nat.is_le(z, P) == True{} : Bool}, WD.sc(252n, one), Q, sy(Q, WD.sc(252n, one), eQ252), hlo)
  +hhiQ = L.subst(Nat, z => {Nat.is_le(P, Nat.add(z, WD.sc(125n, one))) == True{} : Bool}, WD.sc(252n, one), Q, sy(Q, WD.sc(252n, one), eQ252), hhi)
  +hTR = N.lt_le_trans(T, Nat.add(R, C.shift(17n, FV.lv(acc))), Nat.mul(R, P), N.lt_add_r2(d, R, C.shift(17n, FV.lv(acc)), hd), L.subst(Nat, z => {Nat.is_le(Nat.add(R, z), Nat.mul(R, P)) == True{} : Bool}, Nat.mul(R, FV.lv(acc)), C.shift(17n, FV.lv(acc)), CA.mul_r(one, h1, R, hR, FV.lv(acc)), L.subst(Nat, z => {Nat.is_le(z, Nat.mul(R, P)) == True{} : Bool}, Nat.mul(R, 1n+FV.lv(acc)), Nat.add(R, Nat.mul(R, FV.lv(acc))), NA.mul_succ(R, FV.lv(acc)), PW.mul_le_r(R, 1n+FV.lv(acc), P, N.lt_succ_le_succ(FV.lv(acc), P, hav)))))
  +e270a = PS.at_r(one, R, hR, z => {Nat.mul(z, WD.sc(253n, one)) == WD.sc(270n, one) : Nat}, PW.scsc(17n, 253n, one, h1))
  +e270b = tr(Nat.mul(WD.sc(18n, one), Q), Nat.mul(WD.sc(18n, one), WD.sc(252n, one)), WD.sc(270n, one), Equal.cong(Nat, Nat, z => Nat.mul(WD.sc(18n, one), z), Q, WD.sc(252n, one), eQ252), PW.scsc(18n, 252n, one, h1))
  +hRP = L.subst(Nat, z => {Nat.is_lt(Nat.mul(R, P), z) == True{} : Bool}, Nat.mul(R, WD.sc(253n, one)), Nat.mul(WD.sc(18n, one), Q), tr(Nat.mul(R, WD.sc(253n, one)), WD.sc(270n, one), Nat.mul(WD.sc(18n, one), Q), e270a, sy(Nat.mul(WD.sc(18n, one), Q), WD.sc(270n, one), e270b)), L.subst(Nat, z => {Nat.is_lt(z, Nat.mul(R, WD.sc(253n, one))) == True{} : Bool}, Nat.mul(P, R), Nat.mul(R, P), NA.mul_comm(P, R), L.subst(Nat, z => {Nat.is_lt(Nat.mul(P, R), z) == True{} : Bool}, Nat.mul(WD.sc(253n, one), R), Nat.mul(R, WD.sc(253n, one)), NA.mul_comm(WD.sc(253n, one), R), PS.mul_lt_r(P, WD.sc(253n, one), R, CA.r_pos(one, h1, R, hR), hL253))))
  +hq18 = CN.mul_lt_cancel(qh, WD.sc(18n, one), Q, N.le_lt_trans(Nat.mul(qh, Q), T, Nat.mul(WD.sc(18n, one), Q), hq1, N.lt_trans(T, Nat.mul(R, P), Nat.mul(WD.sc(18n, one), Q), hTR, hRP)))
  +hm18 = N.le_lt_trans(m, qh, WD.sc(18n, one), AR.sub_le2(qh, 1n), hq18)
  +hc = N.le_trans(Nat.mul(qh, WD.sc(125n, one)), Nat.mul(WD.sc(18n, one), WD.sc(125n, one)), Q, AR.mul_le(qh, WD.sc(18n, one), WD.sc(125n, one), N.lt_le(qh, WD.sc(18n, one), hq18)), L.subst(Nat, z => {Nat.is_le(Nat.mul(WD.sc(18n, one), WD.sc(125n, one)), z) == True{} : Bool}, WD.sc(252n, one), Q, sy(Q, WD.sc(252n, one), eQ252), L.subst(Nat, z => {Nat.is_le(z, WD.sc(252n, one)) == True{} : Bool}, WD.sc(143n, one), Nat.mul(WD.sc(18n, one), WD.sc(125n, one)), sy(Nat.mul(WD.sc(18n, one), WD.sc(125n, one)), WD.sc(143n, one), PW.scsc(18n, 125n, one, h1)), PW.le_sc(109n, 143n, one))))
  +E = est(qh, P, Q, WD.sc(125n, one), T, hq1, hq2, hloQ, hhiQ, hc)
  +htb = NL.below_con(d, acc, R, hd, hab)
  +htl = Equal.cong(Nat, Nat, z => 1n+z, PS.ln(acc), 15n, hal)
  step_fin_ok(one, h1, R, hR, mm, l, hLv, hLb, hLl, hL253, t, T, {==}, htb, htl, m, hm18, L.and_left(Nat.is_le(Nat.mul(m, P), T), Nat.is_lt(T, Nat.add(Nat.mul(m, P), Nat.add(P, P))), E), L.and_right(Nat.is_le(Nat.mul(m, P), T), Nat.is_lt(T, Nat.add(Nat.mul(m, P), Nat.add(P, P))), E))

def step_len(+R: Nat, +l: List<&2, Nat>, +acc: List<&2, Nat>, +d: Nat, +hLl: {PS.ln(l) == 15n : Nat}, +hal: {PS.ln(acc) == 15n : Nat}) -> {PS.ln(ESC.step(R, l, acc, d)) == 15n : Nat}:
  +t = {Con{d, acc} : List<&2, Nat>}
  +x = Nat.add(ESC.nth(13n, acc), Nat.mul(ESC.nth(14n, acc), R))
  +m = Nat.sub(Nat.div(x, Nat.div(R, 8n)), 1n)
  +cr = LS.carry(R, LS.scal(m, l), 0n)
  +ml = LS.app(LS.cr_limbs(cr), [LS.cr_out(cr)])
  +htl = Equal.cong(Nat, Nat, z => 1n+z, PS.ln(acc), 15n, hal)
  +lml = tr(PS.ln(ml), Nat.add(PS.ln(LS.cr_limbs(cr)), 1n), 16n, BY.app_len(LS.cr_limbs(cr), [LS.cr_out(cr)]), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), PS.ln(LS.cr_limbs(cr)), 15n, tr(PS.ln(LS.cr_limbs(cr)), PS.ln(LS.scal(m, l)), 15n, CN.carry_len(R, LS.scal(m, l), 0n), tr(PS.ln(LS.scal(m, l)), PS.ln(l), 15n, scal_len(m, l), hLl))))
  +hlt = tr(PS.ln(t), 16n, PS.ln(ml), htl, sy(PS.ln(ml), 16n, lml))
  +u = ESC.sb_limbs(ESC.subb(R, t, ml, 0n))
  +lu = tr(PS.ln(u), PS.ln(t), 16n, SB.subb_len(R, t, ml, 0n, hlt), htl)
  +lL = LS.app(l, [0n])
  +llL = tr(PS.ln(lL), Nat.add(PS.ln(l), 1n), 16n, BY.app_len(l, [0n]), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), PS.ln(l), 15n, hLl))
  +hul = tr(PS.ln(u), 16n, PS.ln(lL), lu, sy(PS.ln(lL), 16n, llL))
  +ws = ESC.subb(R, u, lL, 0n)
  +lw = tr(PS.ln(ESC.sb_limbs(ws)), PS.ln(u), 16n, SB.subb_len(R, u, lL, 0n, hul), lu)
  +l16 = tr(PS.ln(LS.sel(ESC.sb_out(ws), ESC.sb_limbs(ws), u)), PS.ln(ESC.sb_limbs(ws)), 16n, sel_len(ESC.sb_out(ws), ESC.sb_limbs(ws), u, tr(PS.ln(ESC.sb_limbs(ws)), 16n, PS.ln(u), lw, sy(PS.ln(u), 16n, lu))), lw)
  take_len(15n, 1n, LS.sel(ESC.sb_out(ws), ESC.sb_limbs(ws), u), l16)

def rep0(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{0n, rep0(m)}

def zeros_below(+n: Nat, +b: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool}) -> {FV.below(rep0(n), b) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      NL.below_con(0n, rep0(m), b, hb, zeros_below(m, b, hb))

def zeros_eq() -> {ESC.zeros() == rep0(15n) : List<&2, Nat>}:
  {==}

def hr_len(+R: Nat, +l: List<&2, Nat>, +xs: List<&2, Nat>, +hLl: {PS.ln(l) == 15n : Nat}) -> {PS.ln(ESC.hr(R, l, xs)) == 15n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      step_len(R, l, ESC.hr(R, l, xt), x, hLl, hr_len(R, l, xt, hLl))

def hr_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +mm: Nat, +l: List<&2, Nat>, +hLv: {FV.lv(l) == 1n+mm : Nat}, +hLb: {FV.below(l, R) == True{} : Bool}, +hLl: {PS.ln(l) == 15n : Nat}, +hL253: {Nat.is_lt(1n+mm, WD.sc(253n, one)) == True{} : Bool}, +hlo: {Nat.is_le(WD.sc(252n, one), 1n+mm) == True{} : Bool}, +hhi: {Nat.is_le(1n+mm, Nat.add(WD.sc(252n, one), WD.sc(125n, one))) == True{} : Bool}, +xs: List<&2, Nat>, +hxs: {FV.below(xs, R) == True{} : Bool}) -> {Bool.and(Bool.and(FV.below(ESC.hr(R, l, xs), R), Nat.is_lt(FV.lv(ESC.hr(R, l, xs)), 1n+mm)), Nat.is_eq(FV.lv(ESC.hr(R, l, xs)), Nat.mod(FV.lv(xs), 1n+mm))) == True{} : Bool}:
  match xs:
    case Nil{}:
      +hz = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, rep0(15n), ESC.zeros(), Equal.sym(List<&2, Nat>, ESC.zeros(), rep0(15n), zeros_eq()), zeros_below(15n, R, CA.r_pos(one, h1, R, hR)))
      L.and_intro(Bool.and(FV.below(ESC.zeros(), R), True{}), True{}, L.and_intro(FV.below(ESC.zeros(), R), True{}, hz, {==}), {==})
    case Con{+x, +xt}:
      +P = {1n+mm : Nat}
      +acc = ESC.hr(R, l, xt)
      +ih = hr_ok(one, h1, R, hR, mm, l, hLv, hLb, hLl, hL253, hlo, hhi, xt, NL.below_tail(x, xt, R, hxs))
      +hab = L.and_left(FV.below(acc, R), Nat.is_lt(FV.lv(acc), P), L.and_left(Bool.and(FV.below(acc, R), Nat.is_lt(FV.lv(acc), P)), Nat.is_eq(FV.lv(acc), Nat.mod(FV.lv(xt), P)), ih))
      +hav = L.and_right(FV.below(acc, R), Nat.is_lt(FV.lv(acc), P), L.and_left(Bool.and(FV.below(acc, R), Nat.is_lt(FV.lv(acc), P)), Nat.is_eq(FV.lv(acc), Nat.mod(FV.lv(xt), P)), ih))
      +hae = N.eq_from_is_eq(FV.lv(acc), Nat.mod(FV.lv(xt), P), L.and_right(Bool.and(FV.below(acc, R), Nat.is_lt(FV.lv(acc), P)), Nat.is_eq(FV.lv(acc), Nat.mod(FV.lv(xt), P)), ih))
      +S = step_ok(one, h1, R, hR, mm, l, hLv, hLb, hLl, hL253, hlo, hhi, acc, hab, hr_len(R, l, xt, hLl), hav, x, NL.below_head(x, xt, R, hxs))
      +st = ESC.step(R, l, acc, x)
      +cA = G.c_trans(mm, FV.lv(acc), Nat.mod(FV.lv(xt), P), FV.lv(xt), G.c_eq(mm, FV.lv(acc), Nat.mod(FV.lv(xt), P), hae), G.c_mod(mm, FV.lv(xt)))
      +cS = G.c_trans(mm, C.shift(17n, FV.lv(acc)), Nat.mul(R, FV.lv(acc)), C.shift(17n, FV.lv(xt)), G.c_eq(mm, C.shift(17n, FV.lv(acc)), Nat.mul(R, FV.lv(acc)), sy(Nat.mul(R, FV.lv(acc)), C.shift(17n, FV.lv(acc)), CA.mul_r(one, h1, R, hR, FV.lv(acc)))), G.c_trans(mm, Nat.mul(R, FV.lv(acc)), Nat.mul(R, FV.lv(xt)), C.shift(17n, FV.lv(xt)), G.c_mul(mm, R, R, FV.lv(acc), FV.lv(xt), G.c_refl(mm, R), cA), G.c_eq(mm, Nat.mul(R, FV.lv(xt)), C.shift(17n, FV.lv(xt)), CA.mul_r(one, h1, R, hR, FV.lv(xt)))))
      +cX = G.c_add(mm, x, x, C.shift(17n, FV.lv(acc)), C.shift(17n, FV.lv(xt)), G.c_refl(mm, x), cS)
      +S1 = L.and_left(Bool.and(FV.below(st, R), Nat.is_lt(FV.lv(st), P)), Nat.is_eq(FV.lv(st), Nat.mod(Nat.add(x, C.shift(17n, FV.lv(acc))), P)), S)
      +S2 = L.and_right(Bool.and(FV.below(st, R), Nat.is_lt(FV.lv(st), P)), Nat.is_eq(FV.lv(st), Nat.mod(Nat.add(x, C.shift(17n, FV.lv(acc))), P)), S)
      +S3 = L.subst(Nat, z => {Nat.is_eq(FV.lv(st), z) == True{} : Bool}, Nat.mod(Nat.add(x, C.shift(17n, FV.lv(acc))), P), Nat.mod(Nat.add(x, C.shift(17n, FV.lv(xt))), P), cX, S2)
      L.and_intro(Bool.and(FV.below(st, R), Nat.is_lt(FV.lv(st), P)), Nat.is_eq(FV.lv(st), Nat.mod(Nat.add(x, C.shift(17n, FV.lv(xt))), P)), S1, S3)
