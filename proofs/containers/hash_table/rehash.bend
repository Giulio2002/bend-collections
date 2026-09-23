import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./words.bend as WR
import ./buckets.bend as B
import ./state.bend as ST
import ./lookup.bend as LK
import ./tools.bend as T
import ./insm.bend as IM
import ./tools.bend as TL
import ../../lib/u32.bend as UW

# Moving buckets from an old table into a new one: the new table's full
# buckets are copies of old ones, and the moved old ones all have copies.


def bk_refl(+b: B.Bk) -> {B.bk_eq(b, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      L.and_intro(U32.is_eq(w, w), Bool.and(U32.is_eq(l, l), S.str_eq(k, k)), UW.u32_eq_refl(w), L.and_intro(U32.is_eq(l, l), S.str_eq(k, k), UW.u32_eq_refl(l), K.str_refl(k)))

def bk_eq_of(+a: B.Bk, +b: B.Bk, +h: {B.bk_eq(a, b) == True{} : Bool}) -> {a == b : B.Bk}:
  match a b:
    case B.BE{} B.BE{}:
      {==}
    case B.BE{} B.BF{w, l, k}:
      Empty.absurd({B.BE{} == B.BF{w, l, k} : B.Bk}, L.false_true(h))
    case B.BF{w, l, k} B.BE{}:
      Empty.absurd({B.BF{w, l, k} == B.BE{} : B.Bk}, L.false_true(h))
    case B.BF{+w, +l, +k} B.BF{+w2, +l2, +k2}:
      +r = Bool.and(U32.is_eq(l, l2), S.str_eq(k, k2))
      +ew = A.eq_of(w, w2, L.and_left(U32.is_eq(w, w2), r, h))
      +el = A.eq_of(l, l2, L.and_left(U32.is_eq(l, l2), S.str_eq(k, k2), L.and_right(U32.is_eq(w, w2), r, h)))
      +ek = K.str_eq_of(k, k2, L.and_right(U32.is_eq(l, l2), S.str_eq(k, k2), L.and_right(U32.is_eq(w, w2), r, h)))
      Equal.trans(B.Bk, B.BF{w, l, k}, B.BF{w2, l, k}, B.BF{w2, l2, k2}, Equal.cong(U32, B.Bk, z => B.BF{z, l, k}, w, w2, ew), Equal.trans(B.Bk, B.BF{w2, l, k}, B.BF{w2, l2, k}, B.BF{w2, l2, k2}, Equal.cong(U32, B.Bk, z => B.BF{w2, z, k}, l, l2, el), Equal.cong(String, B.Bk, z => B.BF{w2, l2, z}, k, k2, ek)))

def ai_c(+bs: List<&2, B.Bk>, +q: Nat, +b: B.Bk, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +h: {B.bk_eq(B.at(bs, j), b) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hlt: {Nat.is_lt(j, q) == True{} : Bool} -> {B.anyeq(bs, q, b) == True{} : Bool}) -> {B.anyeq(bs, 1n+q, b) == True{} : Bool}:
  match c:
    case True{}:
      +h2 = L.subst(Nat, z => {B.bk_eq(B.at(bs, z), b) == True{} : Bool}, j, q, N.eq_from_is_eq(j, q, hc), h)
      L.subst(Bool, x => {Bool.or(x, B.anyeq(bs, q, b)) == True{} : Bool}, True{}, B.bk_eq(B.at(bs, q), b), Equal.sym(Bool, B.bk_eq(B.at(bs, q), b), True{}, h2), {==})
    case False{}:
      L.subst(Bool, x => {Bool.or(B.bk_eq(B.at(bs, q), b), x) == True{} : Bool}, True{}, B.anyeq(bs, q, b), Equal.sym(Bool, B.anyeq(bs, q, b), True{}, rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc))), WR.or_true(B.bk_eq(B.at(bs, q), b)))

# a bucket equal to b below m: some bucket below m equals b
def anyeq_intro(+bs: List<&2, B.Bk>, +m: Nat, +b: B.Bk, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}, +h: {B.bk_eq(B.at(bs, j), b) == True{} : Bool}) -> {B.anyeq(bs, m, b) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({B.anyeq(bs, 0n, b) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      ai_c(bs, q, b, j, hj, h, Nat.is_eq(j, q), {==}, hlt => anyeq_intro(bs, q, b, j, hlt, h))

def anyeq_up(+bs: List<&2, B.Bk>, +m: Nat, +b: B.Bk, +h: {B.anyeq(bs, m, b) == True{} : Bool}) -> {B.anyeq(bs, 1n+m, b) == True{} : Bool}:
  L.subst(Bool, x => {Bool.or(B.bk_eq(B.at(bs, m), b), x) == True{} : Bool}, True{}, B.anyeq(bs, m, b), Equal.sym(Bool, B.anyeq(bs, m, b), True{}, h), WR.or_true(B.bk_eq(B.at(bs, m), b)))

def EqAt(+bs: List<&2, B.Bk>, +m: Nat, +b: B.Bk) -> Type:
  Sigma<&1, &1, Nat, j => {Nat.is_lt(j, m) == True{} : Bool} & {B.at(bs, j) == b : B.Bk}>

def eqat_up(+bs: List<&2, B.Bk>, +q: Nat, +b: B.Bk, e: EqAt(bs, q, b)) -> EqAt(bs, 1n+q, b):
  match e:
    case Tuple{+j, Tuple{+hj, +hb}}:
      (j, (N.lt_trans(j, q, 1n+q, hj, N.lt_succ(q)), hb))

def fe_c(+bs: List<&2, B.Bk>, +q: Nat, +b: B.Bk, +c: Bool, +hc: {B.bk_eq(B.at(bs, q), b) == c : Bool}, +h: {Bool.or(c, B.anyeq(bs, q, b)) == True{} : Bool}, rec: @hq: {B.anyeq(bs, q, b) == True{} : Bool} -> EqAt(bs, q, b)) -> EqAt(bs, 1n+q, b):
  match c:
    case True{}:
      (q, (N.lt_succ(q), bk_eq_of(B.at(bs, q), b, hc)))
    case False{}:
      eqat_up(bs, q, b, rec(h))

# THEOREM: some bucket below m equals b: one is found
def find_eq(+bs: List<&2, B.Bk>, +m: Nat, +b: B.Bk, +h: {B.anyeq(bs, m, b) == True{} : Bool}) -> EqAt(bs, m, b):
  match m:
    case 0n:
      Empty.absurd(EqAt(bs, 0n, b), L.false_true(h))
    case 1n+q:
      fe_c(bs, q, b, B.bk_eq(B.at(bs, q), b), {==}, h, hq => find_eq(bs, q, b, hq))

# ---- properties carried by copies ----


def from_at(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n2) == True{} : Bool}, +ho: {B.occ(B.at(nbs, i)) == True{} : Bool}) -> EqAt(obs, j, B.at(nbs, i)):
  find_eq(obs, j, B.at(nbs, i), B.imp_elim(B.occ(B.at(nbs, i)), B.anyeq(obs, j, B.at(nbs, i)), B.all_inst(B.PFrom{nbs, obs, j}, n2, hf, i, hi), ho))

def pf_at(+obs: List<&2, B.Bk>, +key: String, +j: Nat, +hno: {B.nohb(obs, key, j) == True{} : Bool}, +b: B.Bk, e: EqAt(obs, j, b)) -> {Bool.not(B.hold(key, b)) == True{} : Bool}:
  match e:
    case Tuple{+i, Tuple{+hi, +hb}}:
      L.subst(B.Bk, y => {Bool.not(B.hold(key, y)) == True{} : Bool}, B.at(obs, i), b, hb, LK.nohb_inst(obs, key, j, hno, i, hi))

def pno_c(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +key: String, +hno: {B.nohb(obs, key, j) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n2) == True{} : Bool}, +c: Bool, +hc: {B.hold(key, B.at(nbs, i)) == c : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      e = from_at(nbs, obs, j, n2, hf, i, hi, B.hold_occ(key, B.at(nbs, i), hc))
      L.subst(Bool, x => {Bool.not(x) == True{} : Bool}, B.hold(key, B.at(nbs, i)), True{}, hc, pf_at(obs, key, j, hno, B.at(nbs, i), e))

# THEOREM: a key held by no moved bucket is held by no copy
def pno_from(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +key: String, +hno: {B.nohb(obs, key, j) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {B.all_lt(B.PNo{nbs, key}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      L.and_intro(Bool.not(B.hold(key, B.at(nbs, q))), B.all_lt(B.PNo{nbs, key}, q), L.subst(Bool, x => {Bool.not(x) == True{} : Bool}, B.hold(key, B.at(nbs, q)), B.hold(key, B.at(nbs, q)), {==}, pno_c(nbs, obs, j, n2, hf, key, hno, q, hq, B.hold(key, B.at(nbs, q)), {==})), pno_from(nbs, obs, j, n2, hf, key, hno, q, N.lt_le(q, n2, hq)))

def ns_at(+obs: List<&2, B.Bk>, +t: Nat, +j: Nat, +hns: {ST.noslot(obs, t, j) == True{} : Bool}, +b: B.Bk, e: EqAt(obs, j, b)) -> {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), t))) == True{} : Bool}:
  match e:
    case Tuple{+i, Tuple{+hi, +hb}}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), t))) == True{} : Bool}, B.at(obs, i), b, hb, IM.noslot_inst(obs, t, j, hns, i, hi))

def ns_c(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +t: Nat, +hns: {ST.noslot(obs, t, j) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n2) == True{} : Bool}, +c: Bool, +hc: {B.occ(B.at(nbs, i)) == c : Bool}) -> {Bool.not(Bool.and(c, Nat.is_eq(UD.v(H.slot(B.lnk(B.at(nbs, i)))), t))) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      L.subst(Bool, x => {Bool.not(Bool.and(x, Nat.is_eq(UD.v(H.slot(B.lnk(B.at(nbs, i)))), t))) == True{} : Bool}, B.occ(B.at(nbs, i)), True{}, hc, ns_at(obs, t, j, hns, B.at(nbs, i), from_at(nbs, obs, j, n2, hf, i, hi, hc)))

# THEOREM: a slot used by no moved bucket is used by no copy
def ns_from(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +t: Nat, +hns: {ST.noslot(obs, t, j) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {ST.noslot(nbs, t, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      +x = Bool.not(Bool.and(B.occ(B.at(nbs, q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(nbs, q)))), t)))
      L.and_intro(x, ST.noslot(nbs, t, q), ns_c(nbs, obs, j, n2, hf, t, hns, q, hq, B.occ(B.at(nbs, q)), {==}), ns_from(nbs, obs, j, n2, hf, t, hns, q, N.lt_le(q, n2, hq)))

def lv_at(+obs: List<&2, B.Bk>, +lv: List<&2, Bool>, +fr: Nat, +j: Nat, +hl: {B.all_lt(B.PLive{obs, lv, fr}, j) == True{} : Bool}, +b: B.Bk, e: EqAt(obs, j, b)) -> {B.live_b(lv, fr, b) == True{} : Bool}:
  match e:
    case Tuple{+i, Tuple{+hi, +hb}}:
      L.subst(B.Bk, y => {B.live_b(lv, fr, y) == True{} : Bool}, B.at(obs, i), b, hb, B.all_inst(B.PLive{obs, lv, fr}, j, hl, i, hi))

def live_empty(+lv: List<&2, Bool>, +fr: Nat, +b: B.Bk, +h: {B.occ(b) == False{} : Bool}) -> {B.live_b(lv, fr, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, l, k}:
      Empty.absurd({B.live_b(lv, fr, B.BF{w, l, k}) == True{} : Bool}, L.true_false(h))

def lvf_c(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +lv: List<&2, Bool>, +fr: Nat, +hl: {B.all_lt(B.PLive{obs, lv, fr}, j) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n2) == True{} : Bool}, +c: Bool, +hc: {B.occ(B.at(nbs, i)) == c : Bool}) -> {B.live_b(lv, fr, B.at(nbs, i)) == True{} : Bool}:
  match c:
    case False{}:
      live_empty(lv, fr, B.at(nbs, i), hc)
    case True{}:
      lv_at(obs, lv, fr, j, hl, B.at(nbs, i), from_at(nbs, obs, j, n2, hf, i, hi, hc))

# THEOREM: copies of live buckets are live
def live_from(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +lv: List<&2, Bool>, +fr: Nat, +hl: {B.all_lt(B.PLive{obs, lv, fr}, j) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {B.all_lt(B.PLive{nbs, lv, fr}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      L.and_intro(B.live_b(lv, fr, B.at(nbs, q)), B.all_lt(B.PLive{nbs, lv, fr}, q), lvf_c(nbs, obs, j, n2, hf, lv, fr, hl, q, hq, B.occ(B.at(nbs, q)), {==}), live_from(nbs, obs, j, n2, hf, lv, fr, hl, q, N.lt_le(q, n2, hq)))

# ---- distinct links have distinct slots ----

def nsl_bit(+o: Bool, +a: U32, +l: U32, +h: {Bool.not(Bool.and(o, U32.is_eq(a, l))) == True{} : Bool}) -> {Bool.not(Bool.and(o, Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      IM.not_f(Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))), T.slots_ne_of(a, l, K.not_true_eq(U32.is_eq(a, l), h), Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))), {==}))

# THEOREM: no bucket below m has link l: none uses slot(l)
def noslot_nolb(+bs: List<&2, B.Bk>, +l: U32, +m: Nat, +h: {B.nolb(bs, l, m) == True{} : Bool}) -> {ST.noslot(bs, UD.v(H.slot(l)), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +x = Bool.not(Bool.and(B.occ(B.at(bs, q)), U32.is_eq(B.lnk(B.at(bs, q)), l)))
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bs, q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, q)))), UD.v(H.slot(l))))), ST.noslot(bs, UD.v(H.slot(l)), q), nsl_bit(B.occ(B.at(bs, q)), B.lnk(B.at(bs, q)), l, L.and_left(x, B.nolb(bs, l, q), h)), noslot_nolb(bs, l, q, L.and_right(x, B.nolb(bs, l, q), h)))

# ---- one more old bucket moved ----

def imp_true(+a: Bool, +x: Bool, +h: {x == True{} : Bool}) -> {B.implies(a, x) == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def imp_up(+a: Bool, +bs: List<&2, B.Bk>, +m: Nat, +b: B.Bk, +h: {B.implies(a, B.anyeq(bs, m, b)) == True{} : Bool}) -> {B.implies(a, B.anyeq(bs, 1n+m, b)) == True{} : Bool}:
  match a:
    case True{}:
      anyeq_up(bs, m, b, h)
    case False{}:
      {==}

# copies stay copies of the longer prefix
def from_skip(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {B.all_lt(B.PFrom{nbs, obs, 1n+j}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      L.and_intro(B.eval(B.PFrom{nbs, obs, 1n+j}, q), B.all_lt(B.PFrom{nbs, obs, 1n+j}, q), imp_up(B.occ(B.at(nbs, q)), obs, j, B.at(nbs, q), B.all_inst(B.PFrom{nbs, obs, j}, n2, hf, q, hq)), from_skip(nbs, obs, j, n2, hf, q, N.lt_le(q, n2, hq)))


def from_mv_i(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, nbs)) == True{} : Bool}, +b: B.Bk, +hb: {B.at(obs, j) == b : B.Bk}, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n2) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, i) == c : Bool}) -> {B.eval(B.PFrom{IM.bupd(nbs, e, b), obs, 1n+j}, i) == True{} : Bool}:
  match c:
    case True{}:
      +hq = L.subst(B.Bk, y => {B.bk_eq(y, b) == True{} : Bool}, b, B.at(obs, j), Equal.sym(B.Bk, B.at(obs, j), b, hb), bk_refl(b))
      +r = imp_true(B.occ(b), B.anyeq(obs, 1n+j, b), anyeq_intro(obs, 1n+j, b, j, N.lt_succ(j), hq))
      L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(obs, 1n+j, y)) == True{} : Bool}, b, B.at(IM.bupd(nbs, e, b), i), Equal.sym(B.Bk, B.at(IM.bupd(nbs, e, b), i), b, IM.at_bu_eq(nbs, e, b, he, i, hc)), r)
    case False{}:
      L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(obs, 1n+j, y)) == True{} : Bool}, B.at(nbs, i), B.at(IM.bupd(nbs, e, b), i), Equal.sym(B.Bk, B.at(IM.bupd(nbs, e, b), i), B.at(nbs, i), IM.at_bupd_other(nbs, e, b, i, hc)), imp_up(B.occ(B.at(nbs, i)), obs, j, B.at(nbs, i), B.all_inst(B.PFrom{nbs, obs, j}, n2, hf, i, hi)))

# THEOREM: after moving old bucket j into e, every full new bucket is a copy
def from_mv(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, nbs)) == True{} : Bool}, +b: B.Bk, +hb: {B.at(obs, j) == b : B.Bk}, +hf: {B.all_lt(B.PFrom{nbs, obs, j}, n2) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n2) == True{} : Bool}) -> {B.all_lt(B.PFrom{IM.bupd(nbs, e, b), obs, 1n+j}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n2, hm)
      L.and_intro(B.eval(B.PFrom{IM.bupd(nbs, e, b), obs, 1n+j}, q), B.all_lt(B.PFrom{IM.bupd(nbs, e, b), obs, 1n+j}, q), from_mv_i(nbs, obs, j, n2, e, he, b, hb, hf, q, hq, Nat.is_eq(e, q), {==}), from_mv(nbs, obs, j, n2, e, he, b, hb, hf, q, N.lt_le(q, n2, hq)))

def ne_occ(+bs: List<&2, B.Bk>, +e: Nat, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +i: Nat, +ho: {B.occ(B.at(bs, i)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, i) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +h1 = L.subst(Nat, z => {B.occ(B.at(bs, z)) == True{} : Bool}, i, e, Equal.sym(Nat, e, i, N.eq_from_is_eq(e, i, hc)), ho)
      Empty.absurd({True{} == False{} : Bool}, B.occ_at_be(bs, e, hz, h1))

def to_w(+nbs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(nbs, e) == B.BE{} : B.Bk}, +n2: Nat, +x: B.Bk, +hox: {B.occ(x) == True{} : Bool}, w0: EqAt(nbs, n2, x)) -> {B.anyeq(IM.bupd(nbs, e, b), n2, x) == True{} : Bool}:
  match w0:
    case Tuple{+i, Tuple{+hi, +hat}}:
      +ho = L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, x, B.at(nbs, i), Equal.sym(B.Bk, B.at(nbs, i), x, hat), hox)
      +ne = ne_occ(nbs, e, hz, i, ho, Nat.is_eq(e, i), {==})
      +hq = L.subst(B.Bk, y => {B.bk_eq(y, x) == True{} : Bool}, x, B.at(IM.bupd(nbs, e, b), i), Equal.sym(B.Bk, B.at(IM.bupd(nbs, e, b), i), x, Equal.trans(B.Bk, B.at(IM.bupd(nbs, e, b), i), B.at(nbs, i), x, IM.at_bupd_other(nbs, e, b, i, ne), hat)), bk_refl(x))
      anyeq_intro(IM.bupd(nbs, e, b), n2, x, i, hi, hq)

def to_i(+nbs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(nbs, e) == B.BE{} : B.Bk}, +n2: Nat, +x: B.Bk, +h: {B.implies(B.occ(x), B.anyeq(nbs, n2, x)) == True{} : Bool}, +c: Bool, +hc: {B.occ(x) == c : Bool}) -> {B.implies(c, B.anyeq(IM.bupd(nbs, e, b), n2, x)) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      to_w(nbs, e, b, hz, n2, x, hc, find_eq(nbs, n2, x, B.imp_elim(B.occ(x), B.anyeq(nbs, n2, x), h, hc)))

def to_old(+obs: List<&2, B.Bk>, +nbs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(nbs, e) == B.BE{} : B.Bk}, +n2: Nat, +j: Nat, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, j) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, j) == True{} : Bool}) -> {B.all_lt(B.PTo{obs, IM.bupd(nbs, e, b), n2}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, j, hm)
      +x = B.at(obs, q)
      L.and_intro(B.eval(B.PTo{obs, IM.bupd(nbs, e, b), n2}, q), B.all_lt(B.PTo{obs, IM.bupd(nbs, e, b), n2}, q), L.subst(Bool, c => {B.implies(c, B.anyeq(IM.bupd(nbs, e, b), n2, x)) == True{} : Bool}, B.occ(x), B.occ(x), {==}, to_i(nbs, e, b, hz, n2, x, B.all_inst(B.PTo{obs, nbs, n2}, j, ht, q, hq), B.occ(x), {==})), to_old(obs, nbs, e, b, hz, n2, j, ht, q, N.lt_le(q, j, hq)))

# THEOREM: after moving old bucket j into e, every moved old bucket has a copy
def to_mv(+nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, nbs)) == True{} : Bool}, +b: B.Bk, +hb: {B.at(obs, j) == b : B.Bk}, +hz: {B.at(nbs, e) == B.BE{} : B.Bk}, +hen: {Nat.is_lt(e, n2) == True{} : Bool}, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, j) == True{} : Bool}) -> {B.all_lt(B.PTo{obs, IM.bupd(nbs, e, b), n2}, 1n+j) == True{} : Bool}:
  +hq = L.subst(B.Bk, y => {B.bk_eq(y, B.at(obs, j)) == True{} : Bool}, B.at(obs, j), B.at(IM.bupd(nbs, e, b), e), Equal.sym(B.Bk, B.at(IM.bupd(nbs, e, b), e), B.at(obs, j), Equal.trans(B.Bk, B.at(IM.bupd(nbs, e, b), e), b, B.at(obs, j), IM.at_bupd_same(nbs, e, b, he), Equal.sym(B.Bk, B.at(obs, j), b, hb))), bk_refl(B.at(obs, j)))
  L.and_intro(B.eval(B.PTo{obs, IM.bupd(nbs, e, b), n2}, j), B.all_lt(B.PTo{obs, IM.bupd(nbs, e, b), n2}, j), imp_true(B.occ(B.at(obs, j)), B.anyeq(IM.bupd(nbs, e, b), n2, B.at(obs, j)), anyeq_intro(IM.bupd(nbs, e, b), n2, B.at(obs, j), e, hen, hq)), to_old(obs, nbs, e, b, hz, n2, j, ht, j, N.le_refl(j)))

# THEOREM: skipping an empty old bucket keeps every moved one copied
def to_skip(+obs: List<&2, B.Bk>, +nbs: List<&2, B.Bk>, +j: Nat, +n2: Nat, +ho: {B.occ(B.at(obs, j)) == False{} : Bool}, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, j) == True{} : Bool}) -> {B.all_lt(B.PTo{obs, nbs, n2}, 1n+j) == True{} : Bool}:
  L.and_intro(B.eval(B.PTo{obs, nbs, n2}, j), B.all_lt(B.PTo{obs, nbs, n2}, j), L.subst(Bool, c => {B.implies(c, B.anyeq(nbs, n2, B.at(obs, j))) == True{} : Bool}, False{}, B.occ(B.at(obs, j)), Equal.sym(Bool, B.occ(B.at(obs, j)), False{}, ho), {==}), ht)

# ---- the copies look keys up as the originals ----

def lkc_held(~V: Data, +nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +no: Nat, +n2: Nat, +huqn: {B.all_lt(B.PUniq{nbs}, n2) == True{} : Bool}, +huqo: {B.all_lt(B.PUniq{obs}, no) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +q: String, +i: Nat, +hi: {Nat.is_lt(i, no) == True{} : Bool}, +hk: {B.hold(q, B.at(obs, i)) == True{} : Bool}, w0: EqAt(nbs, n2, B.at(obs, i))) -> {S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q) == S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q) : Maybe<&2, V>}:
  match w0:
    case Tuple{+j, Tuple{+hj, +hat}}:
      +hk2 = L.subst(B.Bk, y => {B.hold(q, y) == True{} : Bool}, B.at(obs, i), B.at(nbs, j), Equal.sym(B.Bk, B.at(nbs, j), B.at(obs, i), hat), hk)
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q), ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(nbs, j))))), S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q), LK.lookup_hit(~V, nbs, vsl, q, n2, huqn, j, hj, hk2), Equal.trans(Maybe<&2, V>, ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(nbs, j))))), ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(obs, i))))), S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q), Equal.cong(B.Bk, Maybe<&2, V>, y => ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(y)))), B.at(nbs, j), B.at(obs, i), hat), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q), ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(obs, i))))), LK.lookup_hit(~V, obs, vsl, q, no, huqo, i, hi, hk))))


def lkc_h(~V: Data, +nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +no: Nat, +n2: Nat, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, no) == True{} : Bool}, +huqn: {B.all_lt(B.PUniq{nbs}, n2) == True{} : Bool}, +huqo: {B.all_lt(B.PUniq{obs}, no) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +q: String, e0: TL.Holder(obs, q, no)) -> {S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q) == S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q) : Maybe<&2, V>}:
  match e0:
    case Tuple{+i, Tuple{+hi, +hk}}:
      +ho = B.hold_occ(q, B.at(obs, i), hk)
      lkc_held(~V, nbs, obs, no, n2, huqn, huqo, vsl, q, i, hi, hk, find_eq(nbs, n2, B.at(obs, i), B.imp_elim(B.occ(B.at(obs, i)), B.anyeq(nbs, n2, B.at(obs, i)), B.all_inst(B.PTo{obs, nbs, n2}, no, ht, i, hi), ho)))

def lkc_c(~V: Data, +nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +no: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, no}, n2) == True{} : Bool}, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, no) == True{} : Bool}, +huqn: {B.all_lt(B.PUniq{nbs}, n2) == True{} : Bool}, +huqo: {B.all_lt(B.PUniq{obs}, no) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +q: String, +d: Bool, +hd: {B.all_lt(B.PNo{obs, q}, no) == d : Bool}) -> {S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q) == S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q) : Maybe<&2, V>}:
  match d:
    case True{}:
      +hn2 = pno_from(nbs, obs, no, n2, hf, q, IM.nohb_pno(obs, q, no, hd, no, N.le_refl(no)), n2, N.le_refl(n2))
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q), None{}, S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q), LK.lookup_none(~V, nbs, vsl, q, n2, hn2), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q), None{}, LK.lookup_none(~V, obs, vsl, q, no, hd)))
    case False{}:
      lkc_h(~V, nbs, obs, no, n2, ht, huqn, huqo, vsl, q, TL.find_hold(obs, q, no, hd))

# THEOREM: a table of copies of all the old full buckets looks every key up
# as the old table does
def lookup_copy(~V: Data, +nbs: List<&2, B.Bk>, +obs: List<&2, B.Bk>, +no: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nbs, obs, no}, n2) == True{} : Bool}, +ht: {B.all_lt(B.PTo{obs, nbs, n2}, no) == True{} : Bool}, +huqn: {B.all_lt(B.PUniq{nbs}, n2) == True{} : Bool}, +huqo: {B.all_lt(B.PUniq{obs}, no) == True{} : Bool}, +vsl: List<&2, Maybe<&2, V>>, +q: String) -> {S.lookup(~V, ST.absm(~V, nbs, vsl, n2, 0n), q) == S.lookup(~V, ST.absm(~V, obs, vsl, no, 0n), q) : Maybe<&2, V>}:
  lkc_c(~V, nbs, obs, no, n2, hf, ht, huqn, huqo, vsl, q, B.all_lt(B.PNo{obs, q}, no), {==})
