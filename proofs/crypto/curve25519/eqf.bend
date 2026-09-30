import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../src/crypto/curve25519/field.bend as F
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/word.bend as WD
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/natural/arith.bend as NR
import ./limbs.bend as LM
import ./fieldops.bend as FO
import ./canon.bend as CN
import ./cong.bend as G

# F.eq(a, b) = is_zero(sub(a, b)) decides a == b mod p. With A, B the
# reduced values, w = (A + p) - B is in [1, 2p), and w mod p == 0 iff w == p
# iff A == B.

def pw(+pp: Nat, +A: Nat, +B: Nat) -> Nat:
  Nat.sub(Nat.add(A, 1n+pp), B)

def w_eq(+pp: Nat, +A: Nat, +B: Nat, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}) -> {Nat.add(pw(pp, A, B), B) == Nat.add(A, 1n+pp) : Nat}:
  +P = {1n+pp : Nat}
  +le = N.le_trans(B, P, Nat.add(A, P), N.lt_le(B, P, hB), G.le_add_l(A, P))
  Equal.trans(Nat, Nat.add(pw(pp, A, B), B), Nat.add(B, pw(pp, A, B)), Nat.add(A, P), NA.add_comm(pw(pp, A, B), B), N.sub_add(Nat.add(A, P), B, le))

def w_zero(+pp: Nat, +A: Nat, +B: Nat, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}, +e: {A == B : Nat}) -> {Nat.mod(pw(pp, A, B), 1n+pp) == 0n : Nat}:
  +P = {1n+pp : Nat}
  +w = pw(pp, A, B)
  +e2 = L.subst(Nat, z => {Nat.add(w, z) == Nat.add(A, P) : Nat}, B, A, Equal.sym(Nat, A, B, e), w_eq(pp, A, B, hB))
  +e3 = NR.add_cancel(A, w, P, Equal.trans(Nat, Nat.add(A, w), Nat.add(w, A), Nat.add(A, P), NA.add_comm(A, w), e2))
  +e4 = Equal.trans(Nat, P, Nat.mul(1n, P), Nat.add(Nat.mul(1n, P), 0n), Equal.sym(Nat, Nat.mul(1n, P), P, NA.add_zero(P)), Equal.sym(Nat, Nat.add(Nat.mul(1n, P), 0n), Nat.mul(1n, P), N.add_zero(Nat.mul(1n, P))))
  Equal.trans(Nat, Nat.mod(w, P), Nat.mod(Nat.add(Nat.mul(1n, P), 0n), P), 0n, G.c_eq(pp, w, Nat.add(Nat.mul(1n, P), 0n), Equal.trans(Nat, w, P, Nat.add(Nat.mul(1n, P), 0n), e3, e4)), NR.mod_of(1n, pp, 0n, {==}))

# w mod p == 0 gives A == B: the quotient q has w == q p, and q is 1
def q_one(+pp: Nat, +A: Nat, +B: Nat, +q: Nat, +hA: {Nat.is_lt(A, 1n+pp) == True{} : Bool}, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}, +hw: {Nat.add(Nat.mul(q, 1n+pp), B) == Nat.add(A, 1n+pp) : Nat}) -> {A == B : Nat}:
  match q:
    case 0n:
      +P = {1n+pp : Nat}
      +c = L.subst(Nat, z => {Nat.is_le(P, z) == True{} : Bool}, Nat.add(A, P), B, Equal.sym(Nat, B, Nat.add(A, P), hw), G.le_add_l(A, P))
      Empty.absurd({A == B : Nat}, L.true_not_false(Nat.is_lt(B, P), hB, N.le_not_lt(B, P, c)))
    case 1n:
      +P = {1n+pp : Nat}
      +h2 = Equal.trans(Nat, Nat.add(P, B), Nat.add(Nat.mul(1n, P), B), Nat.add(A, P), Equal.cong(Nat, Nat, z => Nat.add(z, B), P, Nat.mul(1n, P), Equal.sym(Nat, Nat.mul(1n, P), P, NA.add_zero(P))), hw)
      NR.add_cancel(P, A, B, Equal.sym(Nat, Nat.add(P, B), Nat.add(P, A), Equal.trans(Nat, Nat.add(P, B), Nat.add(A, P), Nat.add(P, A), h2, NA.add_comm(A, P))))
    case 2n+ +r:
      +P = {1n+pp : Nat}
      +big = Nat.add(P, Nat.add(P, Nat.add(Nat.mul(r, P), B)))
      +h2 = Equal.trans(Nat, big, Nat.add(Nat.mul(2n+r, P), B), Nat.add(A, P), Equal.sym(Nat, Nat.add(Nat.mul(2n+r, P), B), big, Equal.trans(Nat, Nat.add(Nat.add(P, Nat.add(P, Nat.mul(r, P))), B), Nat.add(P, Nat.add(Nat.add(P, Nat.mul(r, P)), B)), big, NA.add_assoc(P, Nat.add(P, Nat.mul(r, P)), B), Equal.cong(Nat, Nat, z => Nat.add(P, z), Nat.add(Nat.add(P, Nat.mul(r, P)), B), Nat.add(P, Nat.add(Nat.mul(r, P), B)), NA.add_assoc(P, Nat.mul(r, P), B)))), hw)
      +l1 = N.le_add_left(P, Nat.add(P, Nat.add(Nat.mul(r, P), B)), P, N.le_add_right(P, Nat.add(Nat.mul(r, P), B)))
      +l2 = L.subst(Nat, z => {Nat.is_le(Nat.add(P, P), z) == True{} : Bool}, big, Nat.add(A, P), h2, l1)
      +l3 = N.lt_le_trans(Nat.add(A, P), Nat.add(P, P), Nat.add(A, P), N.lt_add_r2(A, P, P, hA), l2)
      Empty.absurd({A == B : Nat}, L.true_not_false(Nat.is_lt(Nat.add(A, P), Nat.add(A, P)), l3, N.lt_irrefl(Nat.add(A, P))))

def w_ne(+pp: Nat, +A: Nat, +B: Nat, +hA: {Nat.is_lt(A, 1n+pp) == True{} : Bool}, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}, +h: {Nat.mod(pw(pp, A, B), 1n+pp) == 0n : Nat}) -> {A == B : Nat}:
  +P = {1n+pp : Nat}
  +w = pw(pp, A, B)
  +q = Nat.div(w, P)
  +e1 = NR.dm_eq(pp, w)
  +e2 = Equal.trans(Nat, w, Nat.add(Nat.mul(q, P), Nat.mod(w, P)), Nat.add(Nat.mul(q, P), 0n), e1, Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(q, P), z), Nat.mod(w, P), 0n, h))
  +e3 = Equal.trans(Nat, w, Nat.add(Nat.mul(q, P), 0n), Nat.mul(q, P), e2, N.add_zero(Nat.mul(q, P)))
  +e4 = Equal.trans(Nat, Nat.add(Nat.mul(q, P), B), Nat.add(w, B), Nat.add(A, P), Equal.cong(Nat, Nat, z => Nat.add(z, B), Nat.mul(q, P), w, Equal.sym(Nat, w, Nat.mul(q, P), e3)), w_eq(pp, A, B, hB))
  q_one(pp, A, B, q, hA, hB, e4)

def eq_false(+pp: Nat, +A: Nat, +B: Nat, +hA: {Nat.is_lt(A, 1n+pp) == True{} : Bool}, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}, +hb: {Nat.is_eq(A, B) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(Nat.mod(pw(pp, A, B), 1n+pp), 0n) == c : Bool}) -> {Nat.is_eq(Nat.mod(pw(pp, A, B), 1n+pp), 0n) == Nat.is_eq(A, B) : Bool}:
  match c:
    case True{}:
      +m = Nat.mod(pw(pp, A, B), 1n+pp)
      +e = w_ne(pp, A, B, hA, hB, N.eq_from_is_eq(m, 0n, hc))
      Empty.absurd({Nat.is_eq(m, 0n) == Nat.is_eq(A, B) : Bool}, L.true_not_false(Nat.is_eq(A, B), L.subst(Nat, z => {Nat.is_eq(A, z) == True{} : Bool}, A, B, e, N.is_eq_refl(A)), hb))
    case False{}:
      +m = Nat.mod(pw(pp, A, B), 1n+pp)
      Equal.trans(Bool, Nat.is_eq(m, 0n), False{}, Nat.is_eq(A, B), hc, Equal.sym(Bool, Nat.is_eq(A, B), False{}, hb))

def eq_bool(+pp: Nat, +A: Nat, +B: Nat, +hA: {Nat.is_lt(A, 1n+pp) == True{} : Bool}, +hB: {Nat.is_lt(B, 1n+pp) == True{} : Bool}, +b: Bool, +hb: {Nat.is_eq(A, B) == b : Bool}) -> {Nat.is_eq(Nat.mod(pw(pp, A, B), 1n+pp), 0n) == Nat.is_eq(A, B) : Bool}:
  match b:
    case True{}:
      +e = N.eq_from_is_eq(A, B, hb)
      Equal.trans(Bool, Nat.is_eq(Nat.mod(pw(pp, A, B), 1n+pp), 0n), True{}, Nat.is_eq(A, B), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(pw(pp, A, B), 1n+pp), 0n, w_zero(pp, A, B, hB, e)), Equal.sym(Bool, Nat.is_eq(A, B), True{}, hb))
    case False{}:
      eq_false(pp, A, B, hA, hB, hb, Nat.is_eq(Nat.mod(pw(pp, A, B), 1n+pp), 0n), {==})

def eq_val(+one: Nat, +h1: {one == 1n : Nat}, +pp: Nat, +hP: {Nat.add(1n+pp, 19n) == WD.sc(255n, one) : Nat}, +a: List<&2, U32>, +b: List<&2, U32>, +ha: {LM.okb(32n, a, 255n) == True{} : Bool}, +hb: {LM.okb(32n, b, 255n) == True{} : Bool}) -> {F.eq(a, b) == Nat.is_eq(Nat.mod(FS.value(a), 1n+pp), Nat.mod(FS.value(b), 1n+pp)) : Bool}:
  +P = {1n+pp : Nat}
  +A = Nat.mod(FS.value(a), P)
  +B = Nat.mod(FS.value(b), P)
  +d = F.sub(a, b)
  +e1 = CN.is_zero_val(one, h1, pp, hP, d, FO.sub_okb(one, h1, a, b, ha, hb))
  +e2 = FO.sub_mod(one, h1, pp, hP, a, b, ha, hb)
  +e3 = G.c_subm(pp, FS.value(a), A, B, G.c_sym(pp, A, FS.value(a), G.c_mod(pp, FS.value(a))), N.lt_le(B, P, NR.dm_lt(pp, FS.value(b))))
  +e4 = Equal.trans(Nat, Nat.mod(FS.value(d), P), Nat.mod(Nat.sub(Nat.add(FS.value(a), P), B), P), Nat.mod(pw(pp, A, B), P), e2, e3)
  +e5 = Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(FS.value(d), P), Nat.mod(pw(pp, A, B), P), e4)
  Equal.trans(Bool, F.eq(a, b), Nat.is_eq(Nat.mod(FS.value(d), P), 0n), Nat.is_eq(A, B), e1, Equal.trans(Bool, Nat.is_eq(Nat.mod(FS.value(d), P), 0n), Nat.is_eq(Nat.mod(pw(pp, A, B), P), 0n), Nat.is_eq(A, B), e5, eq_bool(pp, A, B, NR.dm_lt(pp, FS.value(a)), NR.dm_lt(pp, FS.value(b)), Nat.is_eq(A, B), {==})))
