import Base
import ../../../spec/lib/common.bend as C
import ../../../src/math/natural.bend as M
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../natural/sqrtn.bend as SQ
import ./width.bend as WW
import ./f64sqa.bend as AQ
import ./f64sqn.bend as QN
import ./w64dm.bend as DM
import ./w64div.bend as W64D

# Nat facts for one step of Zimmermann's Karatsuba square root (used by
# f64sqr.bend): (a + b)^2 expanded, 2 (s 2^32) w == (w 2 s) 2^32,
# (s 2^32)^2 + r 2^64 == n 2^64, q <= 2^32, and (T + 3)^2 > (T + 1)^2 + 4 T.

# (a + b)^2 expanded
def sqa(+a: Nat, +b: Nat) -> {Nat.mul(Nat.add(a, b), Nat.add(a, b)) == Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(a, b), Nat.add(a, b)), Nat.add(Nat.mul(a, Nat.add(a, b)), Nat.mul(b, Nat.add(a, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), NA.mul_add_right(a, b, Nat.add(a, b)), Equal.trans(Nat, Nat.add(Nat.mul(a, Nat.add(a, b)), Nat.mul(b, Nat.add(a, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.mul(b, Nat.add(a, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(b, Nat.add(a, b))), Nat.mul(a, Nat.add(a, b)), Nat.add(Nat.mul(a, a), Nat.mul(a, b)), NA.mul_add_left(a, a, b)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.mul(b, Nat.add(a, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.add(Nat.mul(b, a), Nat.mul(b, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), z), Nat.mul(b, Nat.add(a, b)), Nat.add(Nat.mul(b, a), Nat.mul(b, b)), NA.mul_add_left(b, a, b)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.add(Nat.mul(b, a), Nat.mul(b, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.add(Nat.mul(a, b), Nat.mul(b, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.add(z, Nat.mul(b, b))), Nat.mul(b, a), Nat.mul(a, b), NA.mul_comm(b, a)), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(a, b)), Nat.add(Nat.mul(a, b), Nat.mul(b, b))), Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.add(Nat.mul(a, b), Nat.mul(b, b)))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), NA.add_assoc(Nat.mul(a, a), Nat.mul(a, b), Nat.add(Nat.mul(a, b), Nat.mul(b, b))), Equal.trans(Nat, Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.add(Nat.mul(a, b), Nat.mul(b, b)))), Nat.add(Nat.mul(a, a), Nat.add(Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(b, b))), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a, a), z), Nat.add(Nat.mul(a, b), Nat.add(Nat.mul(a, b), Nat.mul(b, b))), Nat.add(Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(b, b)), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(b, b)), Nat.add(Nat.mul(a, b), Nat.add(Nat.mul(a, b), Nat.mul(b, b))), NA.add_assoc(Nat.mul(a, b), Nat.mul(a, b), Nat.mul(b, b)))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b))), Nat.mul(b, b)), Nat.add(Nat.mul(a, a), Nat.add(Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(b, b))), NA.add_assoc(Nat.mul(a, a), Nat.add(Nat.mul(a, b), Nat.mul(a, b)), Nat.mul(b, b)))))))))

# 2 (s 2^32) w == (w D) 2^32 for D = 2 s
def uw2(+s: Nat, +w: Nat, +D: Nat, +hD: {Nat.add(s, s) == D : Nat}) -> {Nat.add(Nat.mul(C.shift(32n, s), w), Nat.mul(C.shift(32n, s), w)) == C.shift(32n, Nat.mul(w, D)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(C.shift(32n, s), w), Nat.mul(C.shift(32n, s), w)), Nat.add(C.shift(32n, Nat.mul(s, w)), Nat.mul(C.shift(32n, s), w)), C.shift(32n, Nat.mul(w, D)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(C.shift(32n, s), w)), Nat.mul(C.shift(32n, s), w), C.shift(32n, Nat.mul(s, w)), WW.shift_mul_l(32n, s, w)), Equal.trans(Nat, Nat.add(C.shift(32n, Nat.mul(s, w)), Nat.mul(C.shift(32n, s), w)), Nat.add(C.shift(32n, Nat.mul(s, w)), C.shift(32n, Nat.mul(s, w))), C.shift(32n, Nat.mul(w, D)), Equal.cong(Nat, Nat, z => Nat.add(C.shift(32n, Nat.mul(s, w)), z), Nat.mul(C.shift(32n, s), w), C.shift(32n, Nat.mul(s, w)), WW.shift_mul_l(32n, s, w)), Equal.trans(Nat, Nat.add(C.shift(32n, Nat.mul(s, w)), C.shift(32n, Nat.mul(s, w))), C.shift(32n, Nat.add(Nat.mul(s, w), Nat.mul(s, w))), C.shift(32n, Nat.mul(w, D)), Equal.sym(Nat, C.shift(32n, Nat.add(Nat.mul(s, w), Nat.mul(s, w))), Nat.add(C.shift(32n, Nat.mul(s, w)), C.shift(32n, Nat.mul(s, w))), WW.shift_add(32n, Nat.mul(s, w), Nat.mul(s, w))), Equal.trans(Nat, C.shift(32n, Nat.add(Nat.mul(s, w), Nat.mul(s, w))), C.shift(32n, Nat.mul(Nat.add(s, s), w)), C.shift(32n, Nat.mul(w, D)), Equal.cong(Nat, Nat, z => C.shift(32n, z), Nat.add(Nat.mul(s, w), Nat.mul(s, w)), Nat.mul(Nat.add(s, s), w), Equal.sym(Nat, Nat.mul(Nat.add(s, s), w), Nat.add(Nat.mul(s, w), Nat.mul(s, w)), NA.mul_add_right(s, s, w))), Equal.trans(Nat, C.shift(32n, Nat.mul(Nat.add(s, s), w)), C.shift(32n, Nat.mul(D, w)), C.shift(32n, Nat.mul(w, D)), Equal.cong(Nat, Nat, z => C.shift(32n, Nat.mul(z, w)), Nat.add(s, s), D, hD), Equal.cong(Nat, Nat, z => C.shift(32n, z), Nat.mul(D, w), Nat.mul(w, D), NA.mul_comm(D, w)))))))

# (s 2^32)^2 + r 2^64 == n 2^64 for s^2 + r == n
def usq(+s: Nat, +r: Nat, +n: Nat, +hn: {Nat.add(Nat.mul(s, s), r) == n : Nat}) -> {Nat.add(Nat.mul(C.shift(32n, s), C.shift(32n, s)), C.shift(32n, C.shift(32n, r))) == C.shift(32n, C.shift(32n, n)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(C.shift(32n, s), C.shift(32n, s)), C.shift(32n, C.shift(32n, r))), Nat.add(C.shift(32n, C.shift(32n, Nat.mul(s, s))), C.shift(32n, C.shift(32n, r))), C.shift(32n, C.shift(32n, n)), Equal.cong(Nat, Nat, z => Nat.add(z, C.shift(32n, C.shift(32n, r))), Nat.mul(C.shift(32n, s), C.shift(32n, s)), C.shift(32n, C.shift(32n, Nat.mul(s, s))), AQ.sh_sq(32n, s)), Equal.trans(Nat, Nat.add(C.shift(32n, C.shift(32n, Nat.mul(s, s))), C.shift(32n, C.shift(32n, r))), C.shift(32n, Nat.add(C.shift(32n, Nat.mul(s, s)), C.shift(32n, r))), C.shift(32n, C.shift(32n, n)), Equal.sym(Nat, C.shift(32n, Nat.add(C.shift(32n, Nat.mul(s, s)), C.shift(32n, r))), Nat.add(C.shift(32n, C.shift(32n, Nat.mul(s, s))), C.shift(32n, C.shift(32n, r))), WW.shift_add(32n, C.shift(32n, Nat.mul(s, s)), C.shift(32n, r))), Equal.trans(Nat, C.shift(32n, Nat.add(C.shift(32n, Nat.mul(s, s)), C.shift(32n, r))), C.shift(32n, C.shift(32n, Nat.add(Nat.mul(s, s), r))), C.shift(32n, C.shift(32n, n)), Equal.cong(Nat, Nat, z => C.shift(32n, z), Nat.add(C.shift(32n, Nat.mul(s, s)), C.shift(32n, r)), C.shift(32n, Nat.add(Nat.mul(s, s), r)), Equal.sym(Nat, C.shift(32n, Nat.add(Nat.mul(s, s), r)), Nat.add(C.shift(32n, Nat.mul(s, s)), C.shift(32n, r)), WW.shift_add(32n, Nat.mul(s, s), r))), Equal.cong(Nat, Nat, z => C.shift(32n, C.shift(32n, z)), Nat.add(Nat.mul(s, s), r), n, hn))))

# from below: n 2^64 < (S0 + 1)^2, so isqrt(n 2^64) <= S0
# from above: S0^2 <= n 2^64 + q^2
# q <= 2^32: q D <= r 2^32 <= D 2^32 < (2^32 + 1) D
def qb(+one: Nat, +h1: {one == 1n : Nat}, +r: Nat, +q: Nat, +D: Nat, +hq: {Nat.is_le(Nat.mul(q, D), C.shift(32n, r)) == True{} : Bool}, +hr: {Nat.is_le(r, D) == True{} : Bool}, +hD: {Nat.is_lt(0n, D) == True{} : Bool}) -> {Nat.is_le(q, C.shift(32n, one)) == True{} : Bool}:
  +e1 = Equal.trans(Nat, C.shift(32n, D), Nat.mul(D, C.shift(32n, one)), Nat.mul(C.shift(32n, one), D), WW.shift_mul_one(32n, one, h1, D), NA.mul_comm(D, C.shift(32n, one)))
  +h2 = N.le_trans(Nat.mul(q, D), C.shift(32n, r), C.shift(32n, D), hq, WW.shift_mono(32n, r, D, hr))
  +h3 = L.subst(Nat, z => {Nat.is_le(Nat.mul(q, D), z) == True{} : Bool}, C.shift(32n, D), Nat.mul(C.shift(32n, one), D), e1, h2)
  +h4 = L.subst(Nat, z => {Nat.is_lt(Nat.mul(C.shift(32n, one), D), z) == True{} : Bool}, Nat.add(Nat.mul(C.shift(32n, one), D), D), Nat.add(D, Nat.mul(C.shift(32n, one), D)), NA.add_comm(Nat.mul(C.shift(32n, one), D), D), DM.lt_add_pos(Nat.mul(C.shift(32n, one), D), D, hD))
  +h5 = N.le_lt_trans(Nat.mul(q, D), Nat.mul(C.shift(32n, one), D), Nat.mul(1n+C.shift(32n, one), D), h3, h4)
  N.lt_succ_le(q, C.shift(32n, one), W64D.lt_cancel_mul(q, 1n+C.shift(32n, one), D, h5))

def four(+x: Nat) -> {C.shift(2n, x) == Nat.add(Nat.add(x, x), Nat.add(x, x)) : Nat}:
  Equal.trans(Nat, Nat.double(Nat.double(x)), Nat.add(Nat.double(x), Nat.double(x)), Nat.add(Nat.add(x, x), Nat.add(x, x)), NA.double_self(Nat.double(x)), Equal.trans(Nat, Nat.add(Nat.double(x), Nat.double(x)), Nat.add(Nat.add(x, x), Nat.double(x)), Nat.add(Nat.add(x, x), Nat.add(x, x)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.double(x)), Nat.double(x), Nat.add(x, x), NA.double_self(x)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(x, x), z), Nat.double(x), Nat.add(x, x), NA.double_self(x))))

def two_mul(+x: Nat) -> {Nat.mul(x, 2n) == Nat.add(x, x) : Nat}:
  QN.two_mul(x)

# (T + 3)^2 exceeds (T + 1)^2 + 4 T
def t3(+T: Nat) -> {Nat.is_lt(Nat.add(Nat.mul(1n+T, 1n+T), Nat.add(Nat.add(T, T), Nat.add(T, T))), Nat.mul(Nat.add(1n+T, 2n), Nat.add(1n+T, 2n))) == True{} : Bool}:
  +a : Nat = 1n+T
  +e2 = Equal.trans(Nat, Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), Nat.add(Nat.add(a, a), Nat.mul(a, 2n)), Nat.add(Nat.add(a, a), Nat.add(a, a)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(a, 2n)), Nat.mul(a, 2n), Nat.add(a, a), two_mul(a)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(a, a), z), Nat.mul(a, 2n), Nat.add(a, a), two_mul(a)))
  +hT = N.le_succ(T)
  +h4 = SQ.le_add2(Nat.add(T, T), Nat.add(a, a), Nat.add(T, T), Nat.add(a, a), SQ.le_add2(T, a, T, a, hT, hT), SQ.le_add2(T, a, T, a, hT, hT))
  +h5 = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(T, T), Nat.add(T, T)), z) == True{} : Bool}, Nat.add(Nat.add(a, a), Nat.add(a, a)), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), Equal.sym(Nat, Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), Nat.add(Nat.add(a, a), Nat.add(a, a)), e2), h4)
  +h6 = N.le_lt_trans(Nat.add(Nat.add(T, T), Nat.add(T, T)), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n), h5, DM.lt_add_pos(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n, {==}))
  +h7 = Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(a, a), Nat.add(Nat.add(T, T), Nat.add(T, T))), Nat.add(Nat.mul(a, a), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n))), Nat.is_lt(Nat.add(Nat.add(T, T), Nat.add(T, T)), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n)), True{}, WW.lt_cancel_l(Nat.mul(a, a), Nat.add(Nat.add(T, T), Nat.add(T, T)), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n)), h6)
  +h8 = L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(a, a), Nat.add(Nat.add(T, T), Nat.add(T, T))), z) == True{} : Bool}, Nat.add(Nat.mul(a, a), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n)), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n))), Nat.mul(2n, 2n)), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n))), Nat.mul(2n, 2n)), Nat.add(Nat.mul(a, a), Nat.add(Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n)), NA.add_assoc(Nat.mul(a, a), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n)), 4n)), h7)
  L.subst(Nat, z => {Nat.is_lt(Nat.add(Nat.mul(a, a), Nat.add(Nat.add(T, T), Nat.add(T, T))), z) == True{} : Bool}, Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n))), Nat.mul(2n, 2n)), Nat.mul(Nat.add(a, 2n), Nat.add(a, 2n)), Equal.sym(Nat, Nat.mul(Nat.add(a, 2n), Nat.add(a, 2n)), Nat.add(Nat.add(Nat.mul(a, a), Nat.add(Nat.mul(a, 2n), Nat.mul(a, 2n))), Nat.mul(2n, 2n)), sqa(a, 2n)), h8)

def k_hi_c(+X: Nat, +T: Nat, +S: Nat, +hlt: {Nat.is_lt(Nat.mul(S, S), Nat.add(Nat.mul(1n+T, 1n+T), Nat.add(Nat.add(T, T), Nat.add(T, T)))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(S, Nat.add(T, 2n)) == c : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +h1 = N.lt_succ_le_succ(Nat.add(T, 2n), S, N.not_le_lt(S, Nat.add(T, 2n), hc))
      +h2 = AQ.sqmono(Nat.add(1n+T, 2n), S, h1)
      +h3 = N.lt_le_trans(Nat.mul(S, S), Nat.mul(Nat.add(1n+T, 2n), Nat.add(1n+T, 2n)), Nat.mul(S, S), N.lt_trans(Nat.mul(S, S), Nat.add(Nat.mul(1n+T, 1n+T), Nat.add(Nat.add(T, T), Nat.add(T, T))), Nat.mul(Nat.add(1n+T, 2n), Nat.add(1n+T, 2n)), hlt, t3(T)), h2)
      Empty.absurd({False{} == True{} : Bool}, DM.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(Nat.mul(S, S), Nat.mul(S, S)), False{}, Equal.sym(Bool, Nat.is_lt(Nat.mul(S, S), Nat.mul(S, S)), True{}, h3), N.lt_irrefl(Nat.mul(S, S)))))

# from above: S0 <= isqrt(n 2^64) + 2, for isqrt(n 2^64) >= 2^62
