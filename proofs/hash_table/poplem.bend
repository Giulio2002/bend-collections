import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./state.bend as ST
import ./lookup.bend as LK
import ./tools.bend as T
import ./speclem.bend as SL
import ./setv.bend as SV
import ./insm.bend as IM
import ./insa.bend as IA
import ./insf.bend as IF
import ./rehash.bend as RH
import ./delmv.bend as DM
import ./keysw.bend as KW
import ../lib/nat_list.bend as NL
import ../lib/words32.bend as W32

# Facts for pop: after emptying the bucket i that holds key, the other keys
# look up as before, key is held nowhere, the model's keys have no repeats,
# and the vacated slot is free.


# ---- the emptied bucket, for a property true of every empty bucket ----

def at_v0(+O: List<&2, B.Bk>, +i: Nat, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +j: Nat, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {B.at(IM.bupd(O, i, B.BE{}), j) == Bool.pick(B.Bk, c, B.BE{}, B.at(O, j)) : B.Bk}:
  match c:
    case True{}:
      IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)
    case False{}:
      IM.at_bupd_other(O, i, B.BE{}, j, hc)

def well_rm_i(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +sd: Nat, +hw: {B.all_lt(B.PWell{O, sd}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {B.wb(sd, B.at(IM.bupd(O, i, B.BE{}), j)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.wb(sd, y) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      L.subst(B.Bk, y => {B.wb(sd, y) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), IM.at_bupd_other(O, i, B.BE{}, j, hc)), B.all_inst(B.PWell{O, sd}, n, hw, j, hj))

def well_rm(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +sd: Nat, +hw: {B.all_lt(B.PWell{O, sd}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PWell{IM.bupd(O, i, B.BE{}), sd}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.wb(sd, B.at(IM.bupd(O, i, B.BE{}), q)), B.all_lt(B.PWell{IM.bupd(O, i, B.BE{}), sd}, q), well_rm_i(O, n, i, hi, hlen, sd, hw, q, hq, Nat.is_eq(i, q), {==}), well_rm(O, n, i, hi, hlen, sd, hw, q, N.lt_le(q, n, hq)))

def wl_at(+obs: List<&2, B.Bk>, +sd: Nat, +j: Nat, +hw: {B.all_lt(B.PWell{obs, sd}, j) == True{} : Bool}, +b: B.Bk, e: RH.EqAt(obs, j, b)) -> {B.wb(sd, b) == True{} : Bool}:
  match e:
    case Tuple{+x, Tuple{+hx, +hb}}:
      L.subst(B.Bk, y => {B.wb(sd, y) == True{} : Bool}, B.at(obs, x), b, hb, B.all_inst(B.PWell{obs, sd}, j, hw, x, hx))

def wb_empty(+sd: Nat, +b: B.Bk, +h: {B.occ(b) == False{} : Bool}) -> {B.wb(sd, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, l, k}:
      Empty.absurd({B.wb(sd, B.BF{w, l, k}) == True{} : Bool}, L.true_false(h))

def wlf_c(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +sd: Nat, +hw: {B.all_lt(B.PWell{obs, sd}, j) == True{} : Bool}, +x: Nat, +hx: {Nat.is_lt(x, n2) == True{} : Bool}, +c: Bool, +hc: {B.occ(B.at(nbs, x)) == c : Bool}) -> {B.wb(sd, B.at(nbs, x)) == True{} : Bool}:
  match c:
    case False{}:
      wb_empty(sd, B.at(nbs, x), hc)
    case True{}:
      wl_at(obs, sd, j, hw, B.at(nbs, x), RH.from_at(nbs, obs, j, n2, hf, x, hx, hc))

# THEOREM: copies of well-formed buckets are well formed
def well_from(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +sd: Nat, +hw: {B.all_lt(B.PWell{obs, sd}, j) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {B.all_lt(B.PWell{nbs, sd}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      L.and_intro(B.wb(sd, B.at(nbs, q)), B.all_lt(B.PWell{nbs, sd}, q), wlf_c(nbs, obs, j, n2, hf, sd, hw, q, hq, B.occ(B.at(nbs, q)), {==}), well_from(nbs, obs, j, n2, hf, sd, hw, q, N.lt_le(q, n2, hq)))

# ---- slots ----

def nsb_i(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +t: Nat, +h: {ST.noslot(O, t, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(IM.bupd(O, i, B.BE{}), j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(IM.bupd(O, i, B.BE{}), j)))), t))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), t))) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), t))) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), IM.at_bupd_other(O, i, B.BE{}, j, hc)), IM.noslot_inst(O, t, n, h, j, hj))

# THEOREM: emptying a bucket frees no slot another bucket was using
def ns_be(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +t: Nat, +h: {ST.noslot(O, t, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {ST.noslot(IM.bupd(O, i, B.BE{}), t, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(IM.bupd(O, i, B.BE{}), q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(IM.bupd(O, i, B.BE{}), q)))), t))), ST.noslot(IM.bupd(O, i, B.BE{}), t, q), nsb_i(O, n, i, hi, hlen, t, h, q, hq, Nat.is_eq(i, q), {==}), ns_be(O, n, i, hi, hlen, t, h, q, N.lt_le(q, n, hq)))


def pno_be_i(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +q: String, +hno: {B.all_lt(B.PNo{O, q}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {Bool.not(B.hold(q, B.at(IM.bupd(O, i, B.BE{}), j))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(B.hold(q, y)) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      L.subst(B.Bk, y => {Bool.not(B.hold(q, y)) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), IM.at_bupd_other(O, i, B.BE{}, j, hc)), B.all_inst(B.PNo{O, q}, n, hno, j, hj))

def pno_be(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +q: String, +hno: {B.all_lt(B.PNo{O, q}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PNo{IM.bupd(O, i, B.BE{}), q}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hp = N.succ_le_lt(p, n, hm)
      L.and_intro(Bool.not(B.hold(q, B.at(IM.bupd(O, i, B.BE{}), p))), B.all_lt(B.PNo{IM.bupd(O, i, B.BE{}), q}, p), pno_be_i(O, n, i, hi, hlen, q, hno, p, hp, Nat.is_eq(i, p), {==}), pno_be(O, n, i, hi, hlen, q, hno, p, N.lt_le(p, n, hp)))

def hold_eqk(+b: B.Bk, +key: String, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}) -> {B.hold(key, b) == B.hold(q, b) : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, l, +k}:
      SL.eq_tr2(k, key, q, hq)

def pnq_i(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{O}, n) == True{} : Bool}, +key: String, +hk: {B.hold(key, B.at(O, i)) == True{} : Bool}, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {Bool.not(B.hold(q, B.at(IM.bupd(O, i, B.BE{}), j))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(B.hold(q, y)) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      +o = LK.other(O, n, key, huq, i, hi, hk, j, hj, N.is_eq_sym_false(i, j, hc))
      L.subst(B.Bk, y => {Bool.not(B.hold(q, y)) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), IM.at_bupd_other(O, i, B.BE{}, j, hc)), L.subst(Bool, x => {Bool.not(x) == True{} : Bool}, B.hold(key, B.at(O, j)), B.hold(q, B.at(O, j)), hold_eqk(B.at(O, j), key, q, hq), o))

# THEOREM: once its bucket is emptied, the removed key is held nowhere
def pno_rmq(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{O}, n) == True{} : Bool}, +key: String, +hk: {B.hold(key, B.at(O, i)) == True{} : Bool}, +q: String, +hq: {S.str_eq(key, q) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PNo{IM.bupd(O, i, B.BE{}), q}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hp = N.succ_le_lt(p, n, hm)
      L.and_intro(Bool.not(B.hold(q, B.at(IM.bupd(O, i, B.BE{}), p))), B.all_lt(B.PNo{IM.bupd(O, i, B.BE{}), q}, p), pnq_i(O, n, i, hi, hlen, huq, key, hk, q, hq, p, hp, Nat.is_eq(i, p), {==}), pno_rmq(O, n, i, hi, hlen, huq, key, hk, q, hq, p, N.lt_le(p, n, hp)))

def lkr_h(~V: Data, +O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{O}, n) == True{} : Bool}, +key: String, +hk: {B.hold(key, B.at(O, i)) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +mm: Maybe<&2, V>, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, e0: T.Holder(O, q, n)) -> {S.lookup(~V, ST.absm(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), n, 0n), q) == S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q) : Maybe<&2, V>}:
  match e0:
    case Tuple{+j, Tuple{+hj, +hkj}}:
      +hji = SV.neq_hold(O, key, q, i, j, hk, hq, hkj, Nat.is_eq(j, i), {==})
      +eat = IM.at_bupd_other(O, i, B.BE{}, j, N.is_eq_sym_false(j, i, hji))
      +hkj2 = L.subst(B.Bk, y => {B.hold(q, y) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), eat), hkj)
      +sj = UD.v(H.slot(B.lnk(B.at(O, j))))
      +hne = N.is_eq_sym_false(sj, UD.v(H.slot(B.lnk(B.at(O, i)))), T.slot_ne(O, n, huq, i, j, hi, hj, hji, B.hold_occ(key, B.at(O, i), hk), B.hold_occ(q, B.at(O, j), hkj)))
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), n, 0n), q), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), UD.v(H.slot(B.lnk(B.at(IM.bupd(O, i, B.BE{}), j))))), S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), LK.lookup_hit(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), q, n, DM.uq_rm(O, i, hlen, n, huq, n, N.le_refl(n)), j, hj, hkj2), Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), UD.v(H.slot(B.lnk(B.at(IM.bupd(O, i, B.BE{}), j))))), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), sj), S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), Equal.cong(B.Bk, Maybe<&2, V>, y => ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), UD.v(H.slot(B.lnk(y)))), B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), eat), Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), sj), ST.nthm(~V, vsl, sj), S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), T.nthm_upd_other(~V, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), sj, mm, hne), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), ST.nthm(~V, vsl, sj), LK.lookup_hit(~V, O, vsl, q, n, huq, j, hj, hkj)))))

def lkr_c(~V: Data, +O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{O}, n) == True{} : Bool}, +key: String, +hk: {B.hold(key, B.at(O, i)) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +mm: Maybe<&2, V>, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +d: Bool, +hd: {B.all_lt(B.PNo{O, q}, n) == d : Bool}) -> {S.lookup(~V, ST.absm(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), n, 0n), q) == S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q) : Maybe<&2, V>}:
  match d:
    case True{}:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), n, 0n), q), None{}, S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), LK.lookup_none(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), q, n, pno_be(O, n, i, hi, hlen, q, hd, n, N.le_refl(n))), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q), None{}, LK.lookup_none(~V, O, vsl, q, n, hd)))
    case False{}:
      lkr_h(~V, O, n, i, hi, hlen, huq, key, hk, vsl, mm, q, hq, T.find_hold(O, q, n, hd))

# THEOREM: emptying key's bucket and its slot leaves every other key's lookup
def lk_rm(~V: Data, +O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{O}, n) == True{} : Bool}, +key: String, +hk: {B.hold(key, B.at(O, i)) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +mm: Maybe<&2, V>, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}) -> {S.lookup(~V, ST.absm(~V, IM.bupd(O, i, B.BE{}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(B.lnk(B.at(O, i)))), mm), n, 0n), q) == S.lookup(~V, ST.absm(~V, O, vsl, n, 0n), q) : Maybe<&2, V>}:
  lkr_c(~V, O, n, i, hi, hlen, huq, key, hk, vsl, mm, q, hq, B.all_lt(B.PNo{O, q}, n), {==})

# ---- liveness with the slot vacated ----

def lvr_b(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +s: Nat, +fr: Nat, +b: B.Bk, +h: {B.live_b(ST.lvs(~V, vsl), fr, b) == True{} : Bool}, +hne: {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), s))) == True{} : Bool}) -> {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, k}:
      +t = UD.v(H.slot(l))
      +ne = N.is_eq_sym_false(t, s, K.not_true_eq(Nat.is_eq(t, s), hne))
      +e = Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), t), ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, None{}), t)), B.nthb(ST.lvs(~V, vsl), t), ST.lvs_nth(~V, SC.update(Maybe<&2, V>, vsl, s, None{}), t), Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, None{}), t)), ST.some_b(~V, ST.nthm(~V, vsl, t)), B.nthb(ST.lvs(~V, vsl), t), Equal.cong(Maybe<&2, V>, Bool, m => ST.some_b(~V, m), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, s, None{}), t), ST.nthm(~V, vsl, t), T.nthm_upd_other(~V, vsl, s, t, None{}, ne)), Equal.sym(Bool, B.nthb(ST.lvs(~V, vsl), t), ST.some_b(~V, ST.nthm(~V, vsl, t)), ST.lvs_nth(~V, vsl, t))))
      L.and_intro(B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), t), Nat.is_lt(t, fr), Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), t), B.nthb(ST.lvs(~V, vsl), t), True{}, e, L.and_left(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, fr), h)), L.and_right(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, fr), h))

def lvr_i(~V: Data, +O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +hl: {B.all_lt(B.PLive{O, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +s: Nat, +hns: {ST.noslot(IM.bupd(O, i, B.BE{}), s, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr, B.at(IM.bupd(O, i, B.BE{}), j)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr, y) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      +eat = IM.at_bupd_other(O, i, B.BE{}, j, hc)
      +hne = L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), s))) == True{} : Bool}, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), eat, IM.noslot_inst(IM.bupd(O, i, B.BE{}), s, n, hns, j, hj))
      L.subst(B.Bk, y => {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr, y) == True{} : Bool}, B.at(O, j), B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.at(O, j), eat), lvr_b(~V, vsl, s, fr, B.at(O, j), B.all_inst(B.PLive{O, ST.lvs(~V, vsl), fr}, n, hl, j, hj), hne))

# THEOREM: the other buckets stay live once the removed slot is vacant
def live_rm(~V: Data, +O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +hl: {B.all_lt(B.PLive{O, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +s: Nat, +hns: {ST.noslot(IM.bupd(O, i, B.BE{}), s, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PLive{IM.bupd(O, i, B.BE{}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr, B.at(IM.bupd(O, i, B.BE{}), q)), B.all_lt(B.PLive{IM.bupd(O, i, B.BE{}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, s, None{})), fr}, q), lvr_i(~V, O, n, i, hi, hlen, vsl, fr, hl, s, hns, q, hq, Nat.is_eq(i, q), {==}), live_rm(~V, O, n, i, hi, hlen, vsl, fr, hl, s, hns, q, N.lt_le(q, n, hq)))

# ---- the free list after pushing the vacated slot ----

def subl_refl(+xs: List<&2, Nat>) -> {IF.subl(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{x, t}), IF.subl(t, Con{x, t}), L.subst(Bool, b => {Bool.or(b, NL.memn(x, t)) == True{} : Bool}, True{}, Nat.is_eq(x, x), Equal.sym(Bool, Nat.is_eq(x, x), True{}, N.is_eq_refl(x)), {==}), IF.subl_cons(t, t, x, subl_refl(t)))

def mem_self(+t: Nat, +xs: List<&2, Nat>) -> {NL.memn(t, Con{t, xs}) == True{} : Bool}:
  L.subst(Bool, b => {Bool.or(b, NL.memn(t, xs)) == True{} : Bool}, True{}, Nat.is_eq(t, t), Equal.sym(Bool, Nat.is_eq(t, t), True{}, N.is_eq_refl(t)), {==})


# the two orders of visiting s and t
def subl_sw(+s: Nat, +t: Nat, +seen: List<&2, Nat>) -> {IF.subl(Con{t, Con{s, seen}}, Con{s, Con{t, seen}}) == True{} : Bool}:
  L.and_intro(NL.memn(t, Con{s, Con{t, seen}}), IF.subl(Con{s, seen}, Con{s, Con{t, seen}}), IF.mem_cons(t, s, Con{t, seen}, mem_self(t, seen)), L.and_intro(NL.memn(s, Con{s, Con{t, seen}}), IF.subl(seen, Con{s, Con{t, seen}}), mem_self(s, Con{t, seen}), IF.subl_cons(seen, Con{t, seen}, s, IF.subl_cons(seen, seen, t, subl_refl(seen)))))


# THEOREM: the old free list is still valid after pushing the vacated slot
def fl_pr(+O: List<&2, B.Bk>, +n: Nat, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +Vf: List<&2, B.Bk>, +hf: {B.all_lt(B.PFrom{Vf, IM.bupd(O, i, B.BE{}), n}, n) == True{} : Bool}, +hoi: {B.occ(B.at(O, i)) == True{} : Bool}, +nxl: List<&2, U32>, +fv: U32, +cnt: Nat, +f: U32, +fr: Nat, +seen: List<&2, Nat>, +h: {ST.fl_ok(O, n, nxl, cnt, f, fr, seen) == True{} : Bool}) -> {ST.fl_ok(Vf, n, SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), cnt, f, fr, Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen}) == True{} : Bool}:
  match cnt:
    case 0n:
      h
    case 1n+p:
      +x1 = Bool.not(U32.is_eq(f, 0))
      +y = Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(O, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), seen))))
      +tl = ST.fl_ok(O, n, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen})
      +z = Bool.and(ST.noslot(O, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))
      +a2 = L.and_left(y, tl, L.and_right(x1, Bool.and(y, tl), h))
      +a5 = L.and_right(y, tl, L.and_right(x1, Bool.and(y, tl), h))
      +ns = L.and_left(ST.noslot(O, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2))
      +nm = L.and_right(ST.noslot(O, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2))
      +ne = IM.slot_other(B.at(O, i), UD.v(H.slot(f)), hoi, IM.noslot_inst(O, UD.v(H.slot(f)), n, ns, i, hi))
      +ns2 = RH.ns_from(Vf, IM.bupd(O, i, B.BE{}), n, n, hf, UD.v(H.slot(f)), ns_be(O, n, i, hi, hlen, UD.v(H.slot(f)), ns, n, N.le_refl(n)), n, N.le_refl(n))
      +nm2 = L.subst(Bool, b => {Bool.not(Bool.or(b, NL.memn(UD.v(H.slot(f)), seen))) == True{} : Bool}, False{}, Nat.is_eq(UD.v(H.slot(B.lnk(B.at(O, i)))), UD.v(H.slot(f))), Equal.sym(Bool, Nat.is_eq(UD.v(H.slot(B.lnk(B.at(O, i)))), UD.v(H.slot(f))), False{}, ne), nm)
      +enx = W32.nth0_upd_other(nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), UD.v(H.slot(f)), fv, ne)
      +r0 = fl_pr(O, n, i, hi, hlen, Vf, hf, hoi, nxl, fv, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}, a5)
      +r1 = L.subst(U32, g => {ST.fl_ok(Vf, n, SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), p, g, fr, Con{UD.v(H.slot(B.lnk(B.at(O, i)))), Con{UD.v(H.slot(f)), seen}}) == True{} : Bool}, W32.nth0(nxl, UD.v(H.slot(f))), W32.nth0(SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), UD.v(H.slot(f))), Equal.sym(U32, W32.nth0(SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), UD.v(H.slot(f))), W32.nth0(nxl, UD.v(H.slot(f))), enx), r0)
      +r2 = IF.fl_weak(Vf, n, SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), p, W32.nth0(SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), UD.v(H.slot(f))), fr, Con{UD.v(H.slot(B.lnk(B.at(O, i)))), Con{UD.v(H.slot(f)), seen}}, Con{UD.v(H.slot(f)), Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen}}, subl_sw(UD.v(H.slot(B.lnk(B.at(O, i)))), UD.v(H.slot(f)), seen), r1)
      +y2 = Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(Vf, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen}))))
      +tl2 = ST.fl_ok(Vf, n, SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), p, W32.nth0(SC.update(U32, nxl, UD.v(H.slot(B.lnk(B.at(O, i)))), fv), UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen}})
      L.and_intro(x1, Bool.and(y2, tl2), L.and_left(x1, Bool.and(y, tl), h), L.and_intro(y2, tl2, L.and_intro(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(Vf, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen}))), L.and_left(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2), L.and_intro(ST.noslot(Vf, UD.v(H.slot(f)), n), Bool.not(NL.memn(UD.v(H.slot(f)), Con{UD.v(H.slot(B.lnk(B.at(O, i)))), seen})), ns2, nm2)), r2))

# ---- the model's keys have no repeats ----

def mk_b(+key: String, +b: B.Bk, +r: List<&2, String>, +hnh: {Bool.not(B.hold(key, b)) == True{} : Bool}, +hr: {S.mem(key, r) == False{} : Bool}) -> {S.mem(key, SC.append(String, KW.kof(b), r)) == False{} : Bool}:
  match b:
    case B.BE{}:
      hr
    case B.BF{w, l, +k}:
      L.subst(Bool, x => {Bool.or(x, S.mem(key, r)) == False{} : Bool}, False{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), False{}, K.not_true_eq(S.str_eq(k, key), hnh)), hr)

def mem_kb(+bs: List<&2, B.Bk>, +key: String, +m: Nat, +j: Nat, +h: {LK.nob(bs, key, m, j) == True{} : Bool}) -> {S.mem(key, KW.kb(bs, m, j)) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      mk_b(key, B.at(bs, j), KW.kb(bs, p, 1n+j), L.and_left(Bool.not(B.hold(key, B.at(bs, j))), LK.nob(bs, key, p, 1n+j), h), mem_kb(bs, key, p, 1n+j, L.and_right(Bool.not(B.hold(key, B.at(bs, j))), LK.nob(bs, key, p, 1n+j), h)))

def nd_b(+bs: List<&2, B.Bk>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +p: Nat, +hjm: {Nat.is_le(Nat.add(1n+j, p), n) == True{} : Bool}, +b: B.Bk, +hb: {B.at(bs, j) == b : B.Bk}, +hr: {S.nodup(KW.kb(bs, p, 1n+j)) == True{} : Bool}) -> {S.nodup(SC.append(String, KW.kof(b), KW.kb(bs, p, 1n+j))) == True{} : Bool}:
  match b:
    case B.BE{}:
      hr
    case B.BF{w, l, +k}:
      +hk = L.subst(B.Bk, y => {B.hold(k, y) == True{} : Bool}, B.BF{w, l, k}, B.at(bs, j), Equal.sym(B.Bk, B.at(bs, j), B.BF{w, l, k}, hb), K.str_refl(k))
      +nm = mem_kb(bs, k, p, 1n+j, LK.nob_past(bs, n, k, huq, j, hj, hk, p, 1n+j, hjm, N.lt_succ(j)))
      L.and_intro(Bool.not(S.mem(k, KW.kb(bs, p, 1n+j))), S.nodup(KW.kb(bs, p, 1n+j)), IM.not_f(S.mem(k, KW.kb(bs, p, 1n+j)), nm), hr)

def nodup_kb(+bs: List<&2, B.Bk>, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +m: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, m), n) == True{} : Bool}) -> {S.nodup(KW.kb(bs, m, j)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hj = IA.idx_lt(j, p, n, hjm)
      +hjm2 = IA.idx_next(j, p, n, hjm)
      nd_b(bs, n, huq, j, hj, p, hjm2, B.at(bs, j), {==}, nodup_kb(bs, n, huq, p, 1n+j, hjm2))

# THEOREM: the model of a table with unique keys has no repeated key
def nodup_model(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +fr: Nat, +n: Nat, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}) -> {S.nodup(S.keys(~V, ST.absm(~V, bs, vsl, n, 0n))) == True{} : Bool}:
  L.subst(List<&2, String>, z => {S.nodup(z) == True{} : Bool}, KW.kb(bs, n, 0n), S.keys(~V, ST.absm(~V, bs, vsl, n, 0n)), Equal.sym(List<&2, String>, S.keys(~V, ST.absm(~V, bs, vsl, n, 0n)), KW.kb(bs, n, 0n), KW.keys_absm(~V, bs, vsl, fr, n, hl, n, 0n, N.le_refl(n))), nodup_kb(bs, n, huq, n, 0n, N.le_refl(n)))

# ---- a key cell no bucket uses ----

def kd_i(+tb: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), s, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(TB.dec(tb, kl, i)), Nat.is_eq(UD.v(H.slot(B.lnk(TB.dec(tb, kl, i)))), s))) == True{} : Bool}:
  L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), s))) == True{} : Bool}, B.at(TB.buckets(tb, kl, n), i), TB.dec(tb, kl, i), TB.at_buckets(tb, kl, n, i, hi), IM.noslot_inst(TB.buckets(tb, kl, n), s, n, hns, i, hi))

def kd(+tb: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), s, n) == True{} : Bool}, +m: Nat, +i: Nat, +hmi: {Nat.is_le(Nat.add(i, m), n) == True{} : Bool}) -> {TB.dlist(tb, SC.update(String, kl, s, sk), m, i) == TB.dlist(tb, kl, m, i) : List<&2, B.Bk>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hi = IA.idx_lt(i, p, n, hmi)
      IA.con_eq(TB.dec(tb, SC.update(String, kl, s, sk), i), TB.dec(tb, kl, i), TB.dlist(tb, SC.update(String, kl, s, sk), p, 1n+i), TB.dlist(tb, kl, p, 1n+i), IA.dec_same_c(W32.nth0(tb, Nat.double(i)), W32.nth0(tb, 1n+Nat.double(i)), kl, s, sk, U32.is_eq(W32.nth0(tb, Nat.double(i)), 0), kd_i(tb, kl, s, n, hns, i, hi)), kd(tb, kl, s, sk, n, hns, p, 1n+i, IA.idx_next(i, p, n, hmi)))

# THEOREM: rewriting a key cell no bucket uses leaves every bucket
def bs_key(+tb: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +sk: String, +n: Nat, +hns: {ST.noslot(TB.buckets(tb, kl, n), s, n) == True{} : Bool}) -> {TB.buckets(tb, SC.update(String, kl, s, sk), n) == TB.buckets(tb, kl, n) : List<&2, B.Bk>}:
  kd(tb, kl, s, sk, n, hns, n, 0n, N.le_refl(n))
