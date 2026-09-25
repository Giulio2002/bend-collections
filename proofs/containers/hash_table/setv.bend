import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/hash_table.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./buckets.bend as B
import ./state.bend as ST
import ./lookup.bend as LK
import ./speclem.bend as SL
import ./tools.bend as T

# Replacing the value in the slot of the bucket that holds key: for every
# key q, the new entries look q up as the specification's set does.

def hold_trans(+key: String, +q: String, +b: B.Bk, +hk: {B.hold(key, b) == True{} : Bool}, +hq: {S.str_eq(key, q) == True{} : Bool}) -> {B.hold(q, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      Empty.absurd({B.hold(q, B.BE{}) == True{} : Bool}, L.false_true(hk))
    case B.BF{w, l, +k}:
      SL.eq_tr(k, key, q, hk, True{}, hq)

# a bucket holding key does not hold a key different from it
def hold_diff(+key: String, +q: String, +b: B.Bk, +hk: {B.hold(key, b) == True{} : Bool}, +hq: {S.str_eq(key, q) == False{} : Bool}) -> {B.hold(q, b) == False{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, l, +k}:
      SL.eq_tr(k, key, q, hk, False{}, hq)

def neq_hold(+bs: List<&2, B.Bk>, +key: String, +q: String, +i: Nat, +j: Nat, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +hq: {S.str_eq(key, q) == False{} : Bool}, +hkj: {B.hold(q, B.at(bs, j)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, i) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +hqi = L.subst(Nat, z => {B.hold(q, B.at(bs, z)) == True{} : Bool}, j, i, N.eq_from_is_eq(j, i, hc), hkj)
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, B.hold(q, B.at(bs, i)), False{}, Equal.sym(Bool, B.hold(q, B.at(bs, i)), True{}, hqi), hold_diff(key, q, B.at(bs, i), hki, hq))))

def luv_q(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +key: String, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +x: V, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, e: T.Holder(bs, q, n)) -> {S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q) == S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q) : Maybe<&2, V>}:
  match e:
    case Tuple{+j, Tuple{+hj, +hkj}}:
      +s = UD.v(H.slot(B.lnk(B.at(bs, i))))
      +sj = UD.v(H.slot(B.lnk(B.at(bs, j))))
      +hji = neq_hold(bs, key, q, i, j, hki, hq, hkj, Nat.is_eq(j, i), {==})
      +hne = N.is_eq_sym_false(sj, s, T.slot_ne(bs, n, huq, i, j, hi, hj, hji, B.hold_occ(key, B.at(bs, i), hki), B.hold_occ(q, B.at(bs, j), hkj)))
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, s, Some{x}), n, 0n), q), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), sj), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q),
        LK.lookup_hit(~V, bs, SC.update(Maybe<&2, V>, vsl, s, Some{x}), q, n, huq, j, hj, hkj),
        Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), sj), ST.nthm(~V, vsl, sj), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), T.nthm_upd_other(~V, vsl, s, sj, Some{x}, hne), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), ST.nthm(~V, vsl, sj), LK.lookup_hit(~V, bs, vsl, q, n, huq, j, hj, hkj))))

def luv_no(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +key: String, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +x: V, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +d: Bool, +hd: {B.all_lt(B.PNo{bs, q}, n) == d : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q) == S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q) : Maybe<&2, V>}:
  match d:
    case True{}:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q), None{}, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), LK.lookup_none(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), q, n, hd), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), None{}, LK.lookup_none(~V, bs, vsl, q, n, hd)))
    case False{}:
      luv_q(~V, bs, vsl, n, huq, i, hi, key, hki, x, q, hq, T.find_hold(bs, q, n, hd))

def luv_c(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +key: String, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(B.lnk(B.at(bs, i)))), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +x: V, +q: String, +c: Bool, +hc: {S.str_eq(key, q) == c : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q) == S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q) : Maybe<&2, V>}:
  match c:
    case True{}:
      +s = UD.v(H.slot(B.lnk(B.at(bs, i))))
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, s, Some{x}), n, 0n), q), Some{x}, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q),
        Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, s, Some{x}), n, 0n), q), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), s), Some{x}, LK.lookup_hit(~V, bs, SC.update(Maybe<&2, V>, vsl, s, Some{x}), q, n, huq, i, hi, hold_trans(key, q, B.at(bs, i), hki, hc)), T.nthm_upd_same(~V, vsl, s, Some{x}, hs)),
        Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), Some{x}, SL.lookup_set_same(~V, ST.absm(~V, bs, vsl, n, 0n), key, x, q, hc)))
    case False{}:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q),
        luv_no(~V, bs, vsl, n, huq, i, hi, key, hki, x, q, hc, B.all_lt(B.PNo{bs, q}, n), {==}),
        Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), SL.lookup_set_other(~V, ST.absm(~V, bs, vsl, n, 0n), key, x, q, hc)))

# THEOREM: writing x into the slot of the bucket holding key agrees, for every
# key q, with the specification's set.
def lookup_upd(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +key: String, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(B.lnk(B.at(bs, i)))), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +x: V, +q: String) -> {S.lookup(~V, ST.absm(~V, bs, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(bs, i)))), Some{x}), n, 0n), q) == S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q) : Maybe<&2, V>}:
  luv_c(~V, bs, vsl, n, huq, i, hi, key, hki, hs, x, q, S.str_eq(key, q), {==})

# ---- liveness after writing Some x into slot s ----

def lv_c(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +s: Nat, +t: Nat, +x: V, +hs: {Nat.is_lt(s, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +h: {B.nthb(ST.lvs(~V, vsl), t) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(s, t) == c : Bool}) -> {B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), t) == True{} : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(s, t, hc)
      Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), t), ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t)), True{}, ST.lvs_nth(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t), L.subst(Nat, z => {ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), z)) == True{} : Bool}, s, t, e, Equal.cong(Maybe<&2, V>, Bool, m => ST.some_b(~V, m), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), s), Some{x}, T.nthm_upd_same(~V, vsl, s, Some{x}, hs))))
    case False{}:
      Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), t), ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t)), True{}, ST.lvs_nth(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t),
        Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t)), ST.some_b(~V, ST.nthm(~V, vsl, t)), True{}, Equal.cong(Maybe<&2, V>, Bool, m => ST.some_b(~V, m), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x}), t), ST.nthm(~V, vsl, t), T.nthm_upd_other(~V, vsl, s, t, Some{x}, hc)), Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, vsl, t)), B.nthb(ST.lvs(~V, vsl), t), True{}, Equal.sym(Bool, B.nthb(ST.lvs(~V, vsl), t), ST.some_b(~V, ST.nthm(~V, vsl, t)), ST.lvs_nth(~V, vsl, t)), h)))

def lv_b(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +s: Nat, +x: V, +fr: Nat, +hs: {Nat.is_lt(s, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +b: B.Bk, +h: {B.live_b(ST.lvs(~V, vsl), fr, b) == True{} : Bool}) -> {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), fr, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, k}:
      +t = UD.v(H.slot(l))
      L.and_intro(B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), t), Nat.is_lt(t, fr), lv_c(~V, vsl, s, t, x, hs, L.and_left(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, fr), h), Nat.is_eq(s, t), {==}), L.and_right(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, fr), h))

def live_upd(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +n: Nat, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +s: Nat, +x: V, +hs: {Nat.is_lt(s, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PLive{bs, ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), fr}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), fr, B.at(bs, q)), B.all_lt(B.PLive{bs, ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, Some{x})), fr}, q), lv_b(~V, vsl, s, x, fr, hs, B.at(bs, q), B.all_inst(B.PLive{bs, ST.lvs(~V, vsl), fr}, n, hl, q, hq)), live_upd(~V, bs, vsl, fr, n, hl, s, x, hs, q, N.lt_le(q, n, hq)))
