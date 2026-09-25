import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A
import ../../lib/u32.bend as U
import ../../../spec/lib/common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./buckets.bend as B
import ./state.bend as ST

# Tools for the updates: finding the bucket that holds a key, distinct full
# buckets have distinct links, and reading a slot list after an update.

def Holder(+bs: List<&2, B.Bk>, +key: String, +m: Nat) -> Type:
  Sigma<&1, &1, Nat, j => {Nat.is_lt(j, m) == True{} : Bool} & {B.hold(key, B.at(bs, j)) == True{} : Bool}>

def hold_up(+bs: List<&2, B.Bk>, +key: String, +q: Nat, e: Holder(bs, key, q)) -> Holder(bs, key, 1n+q):
  match e:
    case Tuple{+j, Tuple{hj, hk}}:
      (j, (N.lt_trans(j, q, 1n+q, hj, N.lt_succ(q)), hk))

def fh_c(+bs: List<&2, B.Bk>, +key: String, +q: Nat, +c: Bool, +hc: {Bool.not(B.hold(key, B.at(bs, q))) == c : Bool}, +h: {Bool.and(c, B.all_lt(B.PNo{bs, key}, q)) == False{} : Bool}, rec: @hq: {B.all_lt(B.PNo{bs, key}, q) == False{} : Bool} -> Holder(bs, key, q)) -> Holder(bs, key, 1n+q):
  match c:
    case False{}:
      (q, (N.lt_succ(q), K.not_true_eq2(B.hold(key, B.at(bs, q)), hc)))
    case True{}:
      hold_up(bs, key, q, rec(h))

# not every bucket is free of key: one holds it
def find_hold(+bs: List<&2, B.Bk>, +key: String, +m: Nat, +h: {B.all_lt(B.PNo{bs, key}, m) == False{} : Bool}) -> Holder(bs, key, m):
  match m:
    case 0n:
      Empty.absurd(Holder(bs, key, 0n), L.true_false(h))
    case 1n+q:
      fh_c(bs, key, q, Bool.not(B.hold(key, B.at(bs, q))), {==}, h, hq => find_hold(bs, key, q, hq))

# ---- links ----

# slot(l) = l - 1 is injective
def slot_inj(+a: U32, +b: U32, +h: {UD.v(H.slot(a)) == UD.v(H.slot(b)) : Nat}) -> {a == b : U32}:
  +e = U.injective(H.slot(a), H.slot(b), h)
  Equal.trans(U32, a, U32.add(U32.sub(a, 1), 1), b, Equal.sym(U32, U32.add(U32.sub(a, 1), 1), a, A.sub_add(a, 1)), Equal.trans(U32, U32.add(U32.sub(a, 1), 1), U32.add(U32.sub(b, 1), 1), b, Equal.cong(U32, U32, z => U32.add(z, 1), U32.sub(a, 1), U32.sub(b, 1), e), A.sub_add(b, 1)))

def nolb_c(+bs: List<&2, B.Bk>, +l: U32, +q: Nat, +h: {Bool.and(Bool.not(Bool.and(B.occ(B.at(bs, q)), U32.is_eq(B.lnk(B.at(bs, q)), l))), B.nolb(bs, l, q)) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hlt: {Nat.is_lt(j, q) == True{} : Bool} -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.not(Bool.and(B.occ(B.at(bs, z)), U32.is_eq(B.lnk(B.at(bs, z)), l))) == True{} : Bool}, q, j, Equal.sym(Nat, j, q, N.eq_from_is_eq(j, q, hc)), L.and_left(Bool.not(Bool.and(B.occ(B.at(bs, q)), U32.is_eq(B.lnk(B.at(bs, q)), l))), B.nolb(bs, l, q), h))
    case False{}:
      rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc))

def nolb_inst(+bs: List<&2, B.Bk>, +l: U32, +m: Nat, +h: {B.nolb(bs, l, m) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      nolb_c(bs, l, q, h, j, hj, Nat.is_eq(j, q), {==}, hlt => nolb_inst(bs, l, q, L.and_right(Bool.not(Bool.and(B.occ(B.at(bs, q)), U32.is_eq(B.lnk(B.at(bs, q)), l))), B.nolb(bs, l, q), h), j, hlt))

# the full bucket b at index i and the full bucket at j < i have different links
def link_ne_b(+bs: List<&2, B.Bk>, +i: Nat, +j: Nat, +hji: {Nat.is_lt(j, i) == True{} : Bool}, +b: B.Bk, +hu: {B.uq_b(bs, i, b) == True{} : Bool}, +hob: {B.occ(b) == True{} : Bool}, +hoj: {B.occ(B.at(bs, j)) == True{} : Bool}) -> {U32.is_eq(B.lnk(B.at(bs, j)), B.lnk(b)) == False{} : Bool}:
  match b:
    case B.BE{}:
      Empty.absurd({U32.is_eq(B.lnk(B.at(bs, j)), B.lnk(B.BE{})) == False{} : Bool}, L.false_true(hob))
    case B.BF{w, +l, +k}:
      +nl = nolb_inst(bs, l, i, L.and_right(B.nohb(bs, k, i), B.nolb(bs, l, i), hu), j, hji)
      K.not_true_eq(U32.is_eq(B.lnk(B.at(bs, j)), l), L.subst(Bool, z => {Bool.not(Bool.and(z, U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}, B.occ(B.at(bs, j)), True{}, hoj, nl))

def slots_ne_of(+a: U32, +b: U32, +h: {U32.is_eq(a, b) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(b))) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +eab = slot_inj(a, b, N.eq_from_is_eq(UD.v(H.slot(a)), UD.v(H.slot(b)), hc))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_eq(a, b), False{}, L.subst(U32, z => {True{} == U32.is_eq(a, z) : Bool}, a, b, eab, Equal.sym(Bool, U32.is_eq(a, a), True{}, U.u32_eq_refl(a))), h)))

def slot_ne_lt(+bs: List<&2, B.Bk>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hji: {Nat.is_lt(j, i) == True{} : Bool}, +oi: {B.occ(B.at(bs, i)) == True{} : Bool}, +oj: {B.occ(B.at(bs, j)) == True{} : Bool}) -> {Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), UD.v(H.slot(B.lnk(B.at(bs, i))))) == False{} : Bool}:
  slots_ne_of(B.lnk(B.at(bs, j)), B.lnk(B.at(bs, i)), link_ne_b(bs, i, j, hji, B.at(bs, i), B.all_inst(B.PUniq{bs}, n, huq, i, hi), oi, oj), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), UD.v(H.slot(B.lnk(B.at(bs, i))))), {==})

def slot_ne_c(+bs: List<&2, B.Bk>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +hne: {Nat.is_eq(j, i) == False{} : Bool}, +oi: {B.occ(B.at(bs, i)) == True{} : Bool}, +oj: {B.occ(B.at(bs, j)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(j, i) == c : Bool}) -> {Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), UD.v(H.slot(B.lnk(B.at(bs, i))))) == False{} : Bool}:
  match c:
    case True{}:
      slot_ne_lt(bs, n, huq, i, j, hi, hc, oi, oj)
    case False{}:
      N.is_eq_sym_false(UD.v(H.slot(B.lnk(B.at(bs, i)))), UD.v(H.slot(B.lnk(B.at(bs, j)))), slot_ne_lt(bs, n, huq, j, i, hj, N.lt_or_eq(i, j, N.not_lt_le(j, i, hc), N.is_eq_sym_false(j, i, hne)), oj, oi))

# THEOREM: distinct full buckets use distinct slots
def slot_ne(+bs: List<&2, B.Bk>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +hne: {Nat.is_eq(j, i) == False{} : Bool}, +oi: {B.occ(B.at(bs, i)) == True{} : Bool}, +oj: {B.occ(B.at(bs, j)) == True{} : Bool}) -> {Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), UD.v(H.slot(B.lnk(B.at(bs, i))))) == False{} : Bool}:
  slot_ne_c(bs, n, huq, i, j, hi, hj, hne, oi, oj, Nat.is_lt(j, i), {==})

# ---- slot lists after an update ----

def nthm_upd_same(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +s: Nat, +m: Maybe<&2, V>, +h: {Nat.is_lt(s, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}) -> {ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, m), s) == m : Maybe<&2, V>}:
  match vsl s:
    case Nil{} _:
      Empty.absurd({ST.nthm(~V, SC.update(Maybe<&2, V>, Nil{}, s, m), s) == m : Maybe<&2, V>}, N.lt_zero_absurd(s, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nthm_upd_same(~V, t, p, m, h)

def nthm_upd_other(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +s: Nat, +t: Nat, +m: Maybe<&2, V>, +h: {Nat.is_eq(s, t) == False{} : Bool}) -> {ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, m), t) == ST.nthm(~V, vsl, t) : Maybe<&2, V>}:
  match vsl s t:
    case Nil{} _ _:
      {==}
    case Con{x, r} 0n 0n:
      Empty.absurd({ST.nthm(~V, SC.update(Maybe<&2, V>, Con{x, r}, 0n, m), 0n) == ST.nthm(~V, Con{x, r}, 0n) : Maybe<&2, V>}, L.true_false(h))
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      nthm_upd_other(~V, r, p, q, m, h)
