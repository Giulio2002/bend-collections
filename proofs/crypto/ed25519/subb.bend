import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/fe.bend as FV
import ../../../src/crypto/ed25519/scalar.bend as ESC
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ../curve25519/num.bend as M
import ../fe/nl.bend as NL
import ../fe/carry.bend as CA
import ../fe/pass.bend as PS

# Subtraction with borrows of src/crypto/ed25519/scalar.bend (subb) in
# radix R = 2^17: value(digits) + (value(ys) + b) == value(xs) + R^n b_out
# for limbs below R and a borrow b <= 1; digits below R, b_out <= 1.

def tr(+a: Nat, +b: Nat, +c: Nat, +e1: {a == b : Nat}, +e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def sy(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def sl_con(+l: Nat, +r: ESC.Sb) -> {ESC.sb_limbs(ESC.sb_con(l, r)) == Con{l, ESC.sb_limbs(r)} : List<&2, Nat>}:
  match r:
    case ESC.Sb{a, b}:
      {==}

def so_con(+l: Nat, +r: ESC.Sb) -> {ESC.sb_out(ESC.sb_con(l, r)) == ESC.sb_out(r) : Nat}:
  match r:
    case ESC.Sb{a, b}:
      {==}

def add1(+y: Nat) -> {Nat.add(y, 1n) == 1n+y : Nat}:
  tr(Nat.add(y, 1n), 1n+Nat.add(y, 0n), 1n+y, N.add_succ(y, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(y, 0n), y, N.add_zero(y)))

# y + b <= R for y < R, b <= 1
def yb_le(+R: Nat, +y: Nat, +b: Nat, +hy: {Nat.is_lt(y, R) == True{} : Bool}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, b), R) == True{} : Bool}:
  N.le_trans(Nat.add(y, b), Nat.add(y, 1n), R, N.le_add_left(b, 1n, y, hb), L.subst(Nat, z => {Nat.is_le(z, R) == True{} : Bool}, 1n+y, Nat.add(y, 1n), sy(Nat.add(y, 1n), 1n+y, add1(y)), N.lt_succ_le_succ(y, R, hy)))

def dq(+R: Nat, +x: Nat, +y: Nat, +b: Nat) -> Nat:
  Nat.sub(Nat.add(x, R), Nat.add(y, b))

# d div R <= 1
def dig_q(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: Nat, +y: Nat, +b: Nat, +hx: {Nat.is_lt(x, R) == True{} : Bool}) -> {Nat.is_le(Nat.div(dq(R, x, y, b), R), 1n) == True{} : Bool}:
  +d = dq(R, x, y, b)
  +h2 = N.le_lt_trans(d, Nat.add(x, R), Nat.mul(R, 2n), AR.sub_le2(Nat.add(x, R), Nat.add(y, b)), L.subst(Nat, z => {Nat.is_lt(Nat.add(x, R), z) == True{} : Bool}, Nat.add(R, R), Nat.mul(R, 2n), tr(Nat.add(R, R), Nat.add(R, Nat.mul(R, 1n)), Nat.mul(R, 2n), M.cong_r(R, R, Nat.mul(R, 1n), sy(Nat.mul(R, 1n), R, NA.mul_one(R))), sy(Nat.mul(R, 2n), Nat.add(R, Nat.mul(R, 1n)), NA.mul_succ(R, 1n))), N.lt_add_r2(x, R, R, hx)))
  N.lt_succ_le(Nat.div(d, R), 1n, CA.div_lt(one, h1, R, hR, d, 2n, h2))

# q + (1 - q) == 1 for q <= 1
def q_one(+q: Nat, +h: {Nat.is_le(q, 1n) == True{} : Bool}) -> {Nat.add(q, Nat.sub(1n, q)) == 1n : Nat}:
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+r:
      Empty.absurd({Nat.add(2n+r, 0n) == 1n : Nat}, L.false_true(h))

# d mod R + (y + b) == x + R (1 - d div R)
def dig_eq(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: Nat, +y: Nat, +b: Nat, +hx: {Nat.is_lt(x, R) == True{} : Bool}, +hy: {Nat.is_lt(y, R) == True{} : Bool}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Nat.add(Nat.mod(dq(R, x, y, b), R), Nat.add(y, b)) == Nat.add(x, Nat.mul(R, Nat.sub(1n, Nat.div(dq(R, x, y, b), R)))) : Nat}:
  +yb = Nat.add(y, b)
  +d = dq(R, x, y, b)
  +q = Nat.div(d, R)
  +m = Nat.mod(d, R)
  +nq = Nat.sub(1n, q)
  +hyb = N.le_trans(yb, R, Nat.add(x, R), yb_le(R, y, b, hy, hb), NL.le_add_l(x, R))
  +ec = N.sub_add(Nat.add(x, R), yb, hyb)
  +em = tr(Nat.add(m, Nat.mul(R, q)), Nat.add(m, C.shift(17n, q)), d, M.cong_r(m, Nat.mul(R, q), C.shift(17n, q), CA.mul_r(one, h1, R, hR, q)), CA.dm(one, h1, R, hR, d))
  +eR = tr(Nat.add(Nat.mul(R, q), Nat.mul(R, nq)), Nat.mul(R, Nat.add(q, nq)), R, sy(Nat.mul(R, Nat.add(q, nq)), Nat.add(Nat.mul(R, q), Nat.mul(R, nq)), NA.mul_add_left(R, q, nq)), tr(Nat.mul(R, Nat.add(q, nq)), Nat.mul(R, 1n), R, Equal.cong(Nat, Nat, z => Nat.mul(R, z), Nat.add(q, nq), 1n, q_one(q, dig_q(one, h1, R, hR, x, y, b, hx))), NA.mul_one(R)))
  +Rq = Nat.mul(R, q)
  +e1 = tr(Nat.add(Rq, Nat.add(m, yb)), Nat.add(Nat.add(m, Rq), yb), Nat.add(x, R), tr(Nat.add(Rq, Nat.add(m, yb)), Nat.add(Nat.add(Rq, m), yb), Nat.add(Nat.add(m, Rq), yb), sy(Nat.add(Nat.add(Rq, m), yb), Nat.add(Rq, Nat.add(m, yb)), NA.add_assoc(Rq, m, yb)), M.cong_l(Nat.add(Rq, m), Nat.add(m, Rq), yb, NA.add_comm(Rq, m))), tr(Nat.add(Nat.add(m, Rq), yb), Nat.add(d, yb), Nat.add(x, R), M.cong_l(Nat.add(m, Rq), d, yb, em), tr(Nat.add(d, yb), Nat.add(yb, d), Nat.add(x, R), NA.add_comm(d, yb), ec)))
  +e2 = tr(Nat.add(x, R), Nat.add(x, Nat.add(Rq, Nat.mul(R, nq))), Nat.add(Rq, Nat.add(x, Nat.mul(R, nq))), M.cong_r(x, R, Nat.add(Rq, Nat.mul(R, nq)), sy(Nat.add(Rq, Nat.mul(R, nq)), R, eR)), NA.add_swap(x, Rq, Nat.mul(R, nq)))
  NR.add_cancel(Rq, Nat.add(m, yb), Nat.add(x, Nat.mul(R, nq)), tr(Nat.add(Rq, Nat.add(m, yb)), Nat.add(x, R), Nat.add(Rq, Nat.add(x, Nat.mul(R, nq))), e1, e2))

# (m + S A) + ((y + S B) + b) == (m + (y + b)) + S (A + B)
def re4(+m: Nat, +A: Nat, +y: Nat, +B: Nat, +b: Nat) -> {Nat.add(Nat.add(m, C.shift(17n, A)), Nat.add(Nat.add(y, C.shift(17n, B)), b)) == Nat.add(Nat.add(m, Nat.add(y, b)), C.shift(17n, Nat.add(A, B))) : Nat}:
  +SA = C.shift(17n, A)
  +SB = C.shift(17n, B)
  +e1 = M.cong_r(Nat.add(m, SA), Nat.add(Nat.add(y, SB), b), Nat.add(Nat.add(y, b), SB), CA.swap3(y, SB, b))
  +e2 = M.add4(m, SA, Nat.add(y, b), SB)
  +e3 = M.cong_r(Nat.add(m, Nat.add(y, b)), Nat.add(SA, SB), C.shift(17n, Nat.add(A, B)), M.sc_add(17n, A, B))
  tr(Nat.add(Nat.add(m, SA), Nat.add(Nat.add(y, SB), b)), Nat.add(Nat.add(m, SA), Nat.add(Nat.add(y, b), SB)), Nat.add(Nat.add(m, Nat.add(y, b)), C.shift(17n, Nat.add(A, B))), e1, tr(Nat.add(Nat.add(m, SA), Nat.add(Nat.add(y, b), SB)), Nat.add(Nat.add(m, Nat.add(y, b)), Nat.add(SA, SB)), Nat.add(Nat.add(m, Nat.add(y, b)), C.shift(17n, Nat.add(A, B))), e2, e3))

# (x + R c) + S (A + B) == x + S (A + (B + c))
def re5(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +x: Nat, +c: Nat, +A: Nat, +B: Nat) -> {Nat.add(Nat.add(x, Nat.mul(R, c)), C.shift(17n, Nat.add(A, B))) == Nat.add(x, C.shift(17n, Nat.add(A, Nat.add(B, c)))) : Nat}:
  +e1 = NA.add_assoc(x, Nat.mul(R, c), C.shift(17n, Nat.add(A, B)))
  +e2 = M.cong_r(x, Nat.add(Nat.mul(R, c), C.shift(17n, Nat.add(A, B))), Nat.add(C.shift(17n, c), C.shift(17n, Nat.add(A, B))), M.cong_l(Nat.mul(R, c), C.shift(17n, c), C.shift(17n, Nat.add(A, B)), CA.mul_r(one, h1, R, hR, c)))
  +e3 = M.cong_r(x, Nat.add(C.shift(17n, c), C.shift(17n, Nat.add(A, B))), C.shift(17n, Nat.add(c, Nat.add(A, B))), M.sc_add(17n, c, Nat.add(A, B)))
  +e4 = M.cong_r(x, C.shift(17n, Nat.add(c, Nat.add(A, B))), C.shift(17n, Nat.add(A, Nat.add(B, c))), M.cong_sc(17n, Nat.add(c, Nat.add(A, B)), Nat.add(A, Nat.add(B, c)), tr(Nat.add(c, Nat.add(A, B)), Nat.add(Nat.add(A, B), c), Nat.add(A, Nat.add(B, c)), NA.add_comm(c, Nat.add(A, B)), NA.add_assoc(A, B, c))))
  tr(Nat.add(Nat.add(x, Nat.mul(R, c)), C.shift(17n, Nat.add(A, B))), Nat.add(x, Nat.add(Nat.mul(R, c), C.shift(17n, Nat.add(A, B)))), Nat.add(x, C.shift(17n, Nat.add(A, Nat.add(B, c)))), e1, tr(Nat.add(x, Nat.add(Nat.mul(R, c), C.shift(17n, Nat.add(A, B)))), Nat.add(x, Nat.add(C.shift(17n, c), C.shift(17n, Nat.add(A, B)))), Nat.add(x, C.shift(17n, Nat.add(A, Nat.add(B, c)))), e2, tr(Nat.add(x, Nat.add(C.shift(17n, c), C.shift(17n, Nat.add(A, B)))), Nat.add(x, C.shift(17n, Nat.add(c, Nat.add(A, B)))), Nat.add(x, C.shift(17n, Nat.add(A, Nat.add(B, c)))), e3, e4)))

def subb_val(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hx: {FV.below(xs, R) == True{} : Bool}, +hy: {FV.below(ys, R) == True{} : Bool}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}, +hl: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {Nat.add(FV.lv(ESC.sb_limbs(ESC.subb(R, xs, ys, b))), Nat.add(FV.lv(ys), b)) == Nat.add(FV.lv(xs), CA.shl(xs, ESC.sb_out(ESC.subb(R, xs, ys, b)))) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nat.add(0n, Nat.add(FV.lv(Con{y, yt}), b)) == Nat.add(0n, b) : Nat}, N.zero_succ(PS.ln(yt), hl))
    case Con{x, xt} Nil{}:
      Empty.absurd({Nat.add(0n, Nat.add(0n, b)) == Nat.add(FV.lv(Con{x, xt}), CA.shl(Con{x, xt}, b)) : Nat}, N.succ_zero(PS.ln(xt), hl))
    case Con{+x, +xt} Con{+y, +yt}:
      +d = dq(R, x, y, b)
      +m = Nat.mod(d, R)
      +c = Nat.sub(1n, Nat.div(d, R))
      +r = ESC.subb(R, xt, yt, c)
      +A = FV.lv(ESC.sb_limbs(r))
      +B = FV.lv(yt)
      +hx0 = NL.below_head(x, xt, R, hx)
      +hy0 = NL.below_head(y, yt, R, hy)
      +hc = AR.sub_le2(1n, Nat.div(d, R))
      +ih = subb_val(one, h1, R, hR, xt, yt, c, NL.below_tail(x, xt, R, hx), NL.below_tail(y, yt, R, hy), hc, N.succ_inj(PS.ln(xt), PS.ln(yt), hl))
      +e0 = M.cong_add(FV.lv(ESC.sb_limbs(ESC.sb_con(m, r))), FV.lv(Con{m, ESC.sb_limbs(r)}), Nat.add(FV.lv(Con{y, yt}), b), Nat.add(FV.lv(Con{y, yt}), b), Equal.cong(List<&2, Nat>, Nat, z => FV.lv(z), ESC.sb_limbs(ESC.sb_con(m, r)), Con{m, ESC.sb_limbs(r)}, sl_con(m, r)), {==})
      +e1 = re4(m, A, y, B, b)
      +e2 = M.cong_l(Nat.add(m, Nat.add(y, b)), Nat.add(x, Nat.mul(R, c)), C.shift(17n, Nat.add(A, B)), dig_eq(one, h1, R, hR, x, y, b, hx0, hy0, hb))
      +e3 = re5(one, h1, R, hR, x, c, A, B)
      +e4 = M.cong_r(x, C.shift(17n, Nat.add(A, Nat.add(B, c))), C.shift(17n, Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r)))), M.cong_sc(17n, Nat.add(A, Nat.add(B, c)), Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r))), ih))
      +e5 = tr(Nat.add(x, C.shift(17n, Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r))))), Nat.add(x, Nat.add(C.shift(17n, FV.lv(xt)), C.shift(17n, CA.shl(xt, ESC.sb_out(r))))), Nat.add(Nat.add(x, C.shift(17n, FV.lv(xt))), C.shift(17n, CA.shl(xt, ESC.sb_out(r)))), M.cong_r(x, C.shift(17n, Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r)))), Nat.add(C.shift(17n, FV.lv(xt)), C.shift(17n, CA.shl(xt, ESC.sb_out(r)))), sy(Nat.add(C.shift(17n, FV.lv(xt)), C.shift(17n, CA.shl(xt, ESC.sb_out(r)))), C.shift(17n, Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r)))), M.sc_add(17n, FV.lv(xt), CA.shl(xt, ESC.sb_out(r))))), sy(Nat.add(Nat.add(x, C.shift(17n, FV.lv(xt))), C.shift(17n, CA.shl(xt, ESC.sb_out(r)))), Nat.add(x, Nat.add(C.shift(17n, FV.lv(xt)), C.shift(17n, CA.shl(xt, ESC.sb_out(r))))), NA.add_assoc(x, C.shift(17n, FV.lv(xt)), C.shift(17n, CA.shl(xt, ESC.sb_out(r))))))
      +e6 = M.cong_r(Nat.add(x, C.shift(17n, FV.lv(xt))), C.shift(17n, CA.shl(xt, ESC.sb_out(r))), C.shift(17n, CA.shl(xt, ESC.sb_out(ESC.sb_con(m, r)))), M.cong_sc(17n, CA.shl(xt, ESC.sb_out(r)), CA.shl(xt, ESC.sb_out(ESC.sb_con(m, r))), Equal.cong(Nat, Nat, z => CA.shl(xt, z), ESC.sb_out(r), ESC.sb_out(ESC.sb_con(m, r)), sy(ESC.sb_out(ESC.sb_con(m, r)), ESC.sb_out(r), so_con(m, r)))))
      +Z0 = Nat.add(FV.lv(ESC.sb_limbs(ESC.sb_con(m, r))), Nat.add(FV.lv(Con{y, yt}), b))
      +Z1 = Nat.add(Nat.add(m, C.shift(17n, A)), Nat.add(Nat.add(y, C.shift(17n, B)), b))
      +Z2 = Nat.add(Nat.add(m, Nat.add(y, b)), C.shift(17n, Nat.add(A, B)))
      +Z3 = Nat.add(Nat.add(x, Nat.mul(R, c)), C.shift(17n, Nat.add(A, B)))
      +Z4 = Nat.add(x, C.shift(17n, Nat.add(A, Nat.add(B, c))))
      +Z5 = Nat.add(x, C.shift(17n, Nat.add(FV.lv(xt), CA.shl(xt, ESC.sb_out(r)))))
      +Z6 = Nat.add(Nat.add(x, C.shift(17n, FV.lv(xt))), C.shift(17n, CA.shl(xt, ESC.sb_out(r))))
      +Z7 = Nat.add(Nat.add(x, C.shift(17n, FV.lv(xt))), C.shift(17n, CA.shl(xt, ESC.sb_out(ESC.sb_con(m, r)))))
      tr(Z0, Z1, Z7, e0, tr(Z1, Z2, Z7, e1, tr(Z2, Z3, Z7, e2, tr(Z3, Z4, Z7, e3, tr(Z4, Z5, Z7, e4, tr(Z5, Z6, Z7, e5, e6))))))

def subb_ok(+one: Nat, +h1: {one == 1n : Nat}, +R: Nat, +hR: {R == WD.sc(17n, one) : Nat}, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hx: {FV.below(xs, R) == True{} : Bool}, +hb: {Nat.is_le(b, 1n) == True{} : Bool}) -> {Bool.and(FV.below(ESC.sb_limbs(ESC.subb(R, xs, ys, b)), R), Nat.is_le(ESC.sb_out(ESC.subb(R, xs, ys, b)), 1n)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      hb
    case Con{x, xt} Nil{}:
      hb
    case Con{+x, +xt} Con{+y, +yt}:
      +d = dq(R, x, y, b)
      +m = Nat.mod(d, R)
      +c = Nat.sub(1n, Nat.div(d, R))
      +r = ESC.subb(R, xt, yt, c)
      +ih = subb_ok(one, h1, R, hR, xt, yt, c, NL.below_tail(x, xt, R, hx), AR.sub_le2(1n, Nat.div(d, R)))
      +hl = L.and_left(FV.below(ESC.sb_limbs(r), R), Nat.is_le(ESC.sb_out(r), 1n), ih)
      +ho = L.and_right(FV.below(ESC.sb_limbs(r), R), Nat.is_le(ESC.sb_out(r), 1n), ih)
      +bl = L.subst(List<&2, Nat>, z => {FV.below(z, R) == True{} : Bool}, Con{m, ESC.sb_limbs(r)}, ESC.sb_limbs(ESC.sb_con(m, r)), Equal.sym(List<&2, Nat>, ESC.sb_limbs(ESC.sb_con(m, r)), Con{m, ESC.sb_limbs(r)}, sl_con(m, r)), NL.below_con(m, ESC.sb_limbs(r), R, CA.mod_lt(one, h1, R, hR, d), hl))
      +bo = L.subst(Nat, z => {Nat.is_le(z, 1n) == True{} : Bool}, ESC.sb_out(r), ESC.sb_out(ESC.sb_con(m, r)), sy(ESC.sb_out(ESC.sb_con(m, r)), ESC.sb_out(r), so_con(m, r)), ho)
      L.and_intro(FV.below(ESC.sb_limbs(ESC.sb_con(m, r)), R), Nat.is_le(ESC.sb_out(ESC.sb_con(m, r)), 1n), bl, bo)

def subb_len(+R: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hl: {PS.ln(xs) == PS.ln(ys) : Nat}) -> {PS.ln(ESC.sb_limbs(ESC.subb(R, xs, ys, b))) == PS.ln(xs) : Nat}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      Empty.absurd({0n == 1n+PS.ln(xt) : Nat}, N.succ_zero(PS.ln(xt), hl))
    case Con{+x, +xt} Con{+y, +yt}:
      +d = dq(R, x, y, b)
      +m = Nat.mod(d, R)
      +c = Nat.sub(1n, Nat.div(d, R))
      +r = ESC.subb(R, xt, yt, c)
      tr(PS.ln(ESC.sb_limbs(ESC.sb_con(m, r))), 1n+PS.ln(ESC.sb_limbs(r)), 1n+PS.ln(xt), Equal.cong(List<&2, Nat>, Nat, z => PS.ln(z), ESC.sb_limbs(ESC.sb_con(m, r)), Con{m, ESC.sb_limbs(r)}, sl_con(m, r)), Equal.cong(Nat, Nat, z => 1n+z, PS.ln(ESC.sb_limbs(r)), PS.ln(xt), subb_len(R, xt, yt, c, N.succ_inj(PS.ln(xt), PS.ln(yt), hl))))
