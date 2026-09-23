import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LI
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/hash_table.bend as H
import ../hash_table/buckets.bend as B
import ../hash_table/state.bend as HT
import ../hash_table/table.bend as TB
import ../hash_table/insm.bend as IM
import ../hash_table/insa.bend as IA
import ./state.bend as ST
import ./dll.bend as DL
import ./lists.bend as LS
import ./tabsl.bend as TS
import ./walk.bend as WL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../hash_table/arr.bend as AX
import ../lib/nat_list.bend as NL
import ../lib/links.bend as LK

# Facts for placing a new entry in a slot off the recency list.


# ---- no bucket uses a slot off the list ----

def nsb_of(+sl: List<&2, Nat>, +ll: List<&2, U32>, +s: Nat, +hs: {NL.memn(s, sl) == False{} : Bool}, +b: B.Bk, +h: {ST.bslb(sl, ll, b) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), s))) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +hm = L.and_left(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(ST.lw(ll, UD.v(H.slot(l)), 2n), w), h)
      +ne = NL.ne_mem(s, UD.v(H.slot(l)), sl, NL.not_f(NL.memn(s, sl), hs), hm)
      L.subst(Bool, z => {Bool.not(Bool.and(True{}, z)) == True{} : Bool}, False{}, Nat.is_eq(UD.v(H.slot(l)), s), Equal.sym(Bool, Nat.is_eq(UD.v(H.slot(l)), s), False{}, ne), {==})

def noslot_bsl(+bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +ll: List<&2, U32>, +s: Nat, +hs: {NL.memn(s, sl) == False{} : Bool}, +m: Nat, +h: {ST.bsl(bs, sl, ll, m) == True{} : Bool}) -> {HT.noslot(bs, s, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +h1 = L.and_left(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h)
      +h2 = L.and_right(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h)
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), s))), HT.noslot(bs, s, j), nsb_of(sl, ll, s, hs, B.at(bs, j), h1), noslot_bsl(bs, sl, ll, s, hs, j, h2))

# ---- writes to a slot no bucket uses ----

def bslb_ns(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +sl: List<&2, Nat>, +b: B.Bk, +hb: {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), y))) == True{} : Bool}) -> {ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), b) == ST.bslb(sl, ll, b) : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +hx = NL.ne_sym(UD.v(H.slot(l)), y, NL.not_t_f(Nat.is_eq(UD.v(H.slot(l)), y), hb))
      Equal.cong(U32, Bool, z => Bool.and(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(z, w)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), UD.v(H.slot(l)), 2n), ST.lw(ll, UD.v(H.slot(l)), 2n), DL.lw_other(ll, y, o, v, ho, UD.v(H.slot(l)), 2n, {==}, DL.ne_slot(y, UD.v(H.slot(l)), o, 2n, hx)))

def bsl_ns(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +m: Nat, +hns: {HT.noslot(bs, y, m) == True{} : Bool}) -> {ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), m) == ST.bsl(bs, sl, ll, m) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hb = L.and_left(Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), y))), HT.noslot(bs, y, j), hns)
      +hr = L.and_right(Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), y))), HT.noslot(bs, y, j), hns)
      Equal.trans(Bool, Bool.and(ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bslb(sl, ll, B.at(bs, j)), bslb_ns(ll, y, o, v, ho, sl, B.at(bs, j), hb)), Equal.cong(Bool, Bool, z => Bool.and(ST.bslb(sl, ll, B.at(bs, j)), z), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j), ST.bsl(bs, sl, ll, j), bsl_ns(ll, y, o, v, ho, bs, sl, j, hr)))

# ---- the table with one more bucket ----

def bu_c(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +sl: List<&2, Nat>, +ll: List<&2, U32>, +j: Nat, +hj: {ST.bslb(sl, ll, B.at(bs, j)) == True{} : Bool}, +hb: {ST.bslb(sl, ll, b) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {ST.bslb(sl, ll, B.at(IM.bupd(bs, e, b), j)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, z => {ST.bslb(sl, ll, z) == True{} : Bool}, b, B.at(IM.bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(IM.bupd(bs, e, b), j), b, IM.at_bu_eq(bs, e, b, he, j, hc)), hb)
    case False{}:
      L.subst(B.Bk, z => {ST.bslb(sl, ll, z) == True{} : Bool}, B.at(bs, j), B.at(IM.bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(IM.bupd(bs, e, b), j), B.at(bs, j), IM.at_bupd_other(bs, e, b, j, hc)), hj)

def bsl_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +sl: List<&2, Nat>, +ll: List<&2, U32>, +hb: {ST.bslb(sl, ll, b) == True{} : Bool}, +m: Nat, +h: {ST.bsl(bs, sl, ll, m) == True{} : Bool}) -> {ST.bsl(IM.bupd(bs, e, b), sl, ll, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +h1 = L.and_left(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h)
      +h2 = L.and_right(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h)
      L.and_intro(ST.bslb(sl, ll, B.at(IM.bupd(bs, e, b), j)), ST.bsl(IM.bupd(bs, e, b), sl, ll, j), bu_c(bs, e, b, he, sl, ll, j, h1, hb, Nat.is_eq(e, j), {==}), bsl_up(bs, e, b, he, sl, ll, hb, j, h2))

def isbf_be(+w: U32, +l: U32) -> {ST.isbf(B.BE{}, w, l) == False{} : Bool}:
  {==}

def ab_c(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +l: U32, +w: U32, +m: Nat, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}, +hb: {ST.isbf(B.at(bs, j), w, l) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {ST.anyb(IM.bupd(bs, e, b), m, l, w) == True{} : Bool}:
  match c:
    case True{}:
      +ej = N.eq_from_is_eq(e, j, hc)
      +hb2 = L.subst(Nat, z => {ST.isbf(B.at(bs, z), w, l) == True{} : Bool}, j, e, Equal.sym(Nat, e, j, ej), hb)
      Empty.absurd({ST.anyb(IM.bupd(bs, e, b), m, l, w) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, ST.isbf(B.at(bs, e), w, l), True{}, L.subst(B.Bk, z => {False{} == ST.isbf(z, w, l) : Bool}, B.BE{}, B.at(bs, e), Equal.sym(B.Bk, B.at(bs, e), B.BE{}, hz), {==}), hb2)))
    case False{}:
      +hb2 = L.subst(B.Bk, z => {ST.isbf(z, w, l) == True{} : Bool}, B.at(bs, j), B.at(IM.bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(IM.bupd(bs, e, b), j), B.at(bs, j), IM.at_bupd_other(bs, e, b, j, hc)), hb)
      TS.anyb_intro(IM.bupd(bs, e, b), m, l, w, j, hj, hb2)

def ab_w(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +l: U32, +w: U32, +m: Nat, a: TS.AnybAt(bs, m, l, w)) -> {ST.anyb(IM.bupd(bs, e, b), m, l, w) == True{} : Bool}:
  match a:
    case Tuple{+j, Tuple{+hj, hb}}:
      ab_c(bs, e, b, hz, l, w, m, j, hj, hb, Nat.is_eq(e, j), {==})

# filling an empty bucket keeps every bucket of a slot
def anyb_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +l: U32, +w: U32, +m: Nat, +h: {ST.anyb(bs, m, l, w) == True{} : Bool}) -> {ST.anyb(IM.bupd(bs, e, b), m, l, w) == True{} : Bool}:
  ab_w(bs, e, b, hz, l, w, m, TS.find_anyb(bs, m, l, w, h))

def has_up(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +m: Nat, +ll: List<&2, U32>, +xs: List<&2, Nat>, +h: {ST.hasall(~V, bs, m, ll, xs) == True{} : Bool}) -> {ST.hasall(~V, IM.bupd(bs, e, b), m, ll, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h1 = L.and_left(ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, m, ll, t), h)
      +h2 = L.and_right(ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, m, ll, t), h)
      L.and_intro(ST.anyb(IM.bupd(bs, e, b), m, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, IM.bupd(bs, e, b), m, ll, t), anyb_up(bs, e, b, hz, LK.lnk(x), ST.lw(ll, x, 2n), m, h1), has_up(~V, bs, e, b, hz, m, ll, t, h2))

# ---- writes to a slot off the list: its buckets ----

def has_fs(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +bs: List<&2, B.Bk>, +m: Nat, +xs: List<&2, Nat>, +hy: {NL.memn(y, xs) == False{} : Bool}) -> {ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), xs) == ST.hasall(~V, bs, m, ll, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hys = NL.ne_sym(s, y, NL.or_ff_l(Nat.is_eq(s, y), NL.memn(y, t), hy))
      +e = Equal.cong(U32, Bool, z => ST.anyb(bs, m, LK.lnk(s), z), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n), ST.lw(ll, s, 2n), DL.lw_other(ll, y, o, v, ho, s, 2n, {==}, DL.ne_slot(y, s, o, 2n, hys)))
      Equal.trans(Bool, Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, ll, t)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), ST.anyb(bs, m, LK.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), e), Equal.cong(Bool, Bool, z => Bool.and(ST.anyb(bs, m, LK.lnk(s), ST.lw(ll, s, 2n)), z), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t), ST.hasall(~V, bs, m, ll, t), has_fs(~V, ll, y, o, v, ho, bs, m, t, NL.or_ff_r(Nat.is_eq(s, y), NL.memn(y, t), hy))))

# ---- a key written to a slot off the list ----


def skey_ks(+ll: List<&2, U32>, +kl: List<&2, String>, +y: Nat, +kk: String, +x: Nat, +h: {Nat.is_eq(y, x) == False{} : Bool}) -> {ST.skey(ll, SC.update(String, kl, y, kk), x) == ST.skey(ll, kl, x) : String}:
  Equal.cong(String, String, z => TB.keyof(ST.lw(ll, x, 2n), z), TB.nths(SC.update(String, kl, y, kk), x), TB.nths(kl, x), IA.nths_upd_other(kl, y, x, kk, h))

def sent_ks(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +y: Nat, +kk: String, +x: Nat, +h: {Nat.is_eq(y, x) == False{} : Bool}, +m: Maybe<&2, V>) -> {ST.sent_m(~V, ll, SC.update(String, kl, y, kk), x, m) == ST.sent_m(~V, ll, kl, x, m) : List<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Equal.cong(String, List<&2, SP.Ent<V>>, z => Con{SP.LE{z, w, ST.lw(ll, x, 3n), W.U64{ST.lw(ll, x, 4n), ST.lw(ll, x, 5n)}}, Nil{}}, ST.skey(ll, SC.update(String, kl, y, kk), x), ST.skey(ll, kl, x), skey_ks(ll, kl, y, kk, x, h))

def es_ks(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +y: Nat, +kk: String, +el: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +hy: {NL.memn(y, xs) == False{} : Bool}) -> {ST.es(~V, ll, SC.update(String, kl, y, kk), el, xs) == ST.es(~V, ll, kl, el, xs) : List<&2, SP.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hys = NL.ne_sym(s, y, NL.or_ff_l(Nat.is_eq(s, y), NL.memn(y, t), hy))
      +m = HT.nthm(~V, el, s)
      +a = Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, ll, SC.update(String, kl, y, kk), el, t)), ST.sent_m(~V, ll, SC.update(String, kl, y, kk), s, m), ST.sent_m(~V, ll, kl, s, m), sent_ks(~V, ll, kl, y, kk, s, hys, m))
      Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, SC.update(String, kl, y, kk), s, m), ST.es(~V, ll, SC.update(String, kl, y, kk), el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, ll, SC.update(String, kl, y, kk), el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, ll, kl, el, t)), a, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), z), ST.es(~V, ll, SC.update(String, kl, y, kk), el, t), ST.es(~V, ll, kl, el, t), es_ks(~V, ll, kl, y, kk, el, t, NL.or_ff_r(Nat.is_eq(s, y), NL.memn(y, t), hy))))

# ---- lists ----

def slok_mono(~V: Data, +xs: List<&2, Nat>, +fr: Nat, +fr2: Nat, +el: List<&2, Maybe<&2, V>>, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}) -> {ST.slok(~V, xs, fr2, el) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)
      +hx = N.lt_le_trans(x, fr, fr2, L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), h0), hle)
      L.and_intro(Bool.and(Nat.is_lt(x, fr2), ST.live(~V, el, x)), ST.slok(~V, t, fr2, el), L.and_intro(Nat.is_lt(x, fr2), ST.live(~V, el, x), hx, L.and_right(Nat.is_lt(x, fr), ST.live(~V, el, x), h0)), slok_mono(~V, t, fr, fr2, el, hle, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)))

def len_snoc(+xs: List<&2, Nat>, +s: Nat) -> {SC.length(Nat, SC.append(Nat, xs, Con{s, Nil{}})) == 1n+SC.length(Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(Nat, SC.append(Nat, t, Con{s, Nil{}})), 1n+SC.length(Nat, t), len_snoc(t, s))


def nd_snoc(+xs: List<&2, Nat>, +s: Nat, +hnd: {NL.nodupn(xs) == True{} : Bool}, +hs: {NL.memn(s, xs) == False{} : Bool}) -> {NL.nodupn(SC.append(Nat, xs, Con{s, Nil{}})) == True{} : Bool}:
  +ea = LI.append_nil(Nat, xs)
  +h1 = L.subst(List<&2, Nat>, z => {NL.nodupn(z) == True{} : Bool}, xs, SC.append(Nat, xs, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, xs, Nil{}), xs, ea), hnd)
  +h2 = L.subst(List<&2, Nat>, z => {Bool.not(NL.memn(s, z)) == True{} : Bool}, xs, SC.append(Nat, xs, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, xs, Nil{}), xs, ea), NL.not_f(NL.memn(s, xs), hs))
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(NL.nodupn(SC.append(Nat, xs, Nil{})), Bool.not(NL.memn(s, SC.append(Nat, xs, Nil{})))), NL.nodupn(SC.append(Nat, xs, Con{s, Nil{}})), Equal.sym(Bool, NL.nodupn(SC.append(Nat, xs, Con{s, Nil{}})), Bool.and(NL.nodupn(SC.append(Nat, xs, Nil{})), Bool.not(NL.memn(s, SC.append(Nat, xs, Nil{})))), NL.nd_mid(xs, s, Nil{})), L.and_intro(NL.nodupn(SC.append(Nat, xs, Nil{})), Bool.not(NL.memn(s, SC.append(Nat, xs, Nil{}))), h1, h2))


def nds_snoc(+ks: List<&2, String>, +kk: String, +hnd: {S.nodup(ks) == True{} : Bool}, +hs: {S.mem(kk, ks) == False{} : Bool}) -> {S.nodup(SC.append(String, ks, Con{kk, Nil{}})) == True{} : Bool}:
  +ea = LI.append_nil(String, ks)
  +h1 = L.subst(List<&2, String>, z => {S.nodup(z) == True{} : Bool}, ks, SC.append(String, ks, Nil{}), Equal.sym(List<&2, String>, SC.append(String, ks, Nil{}), ks, ea), hnd)
  +h2 = L.subst(List<&2, String>, z => {Bool.not(S.mem(kk, z)) == True{} : Bool}, ks, SC.append(String, ks, Nil{}), Equal.sym(List<&2, String>, SC.append(String, ks, Nil{}), ks, ea), NL.not_f(S.mem(kk, ks), hs))
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(S.nodup(SC.append(String, ks, Nil{})), Bool.not(S.mem(kk, SC.append(String, ks, Nil{})))), S.nodup(SC.append(String, ks, Con{kk, Nil{}})), Equal.sym(Bool, S.nodup(SC.append(String, ks, Con{kk, Nil{}})), Bool.and(S.nodup(SC.append(String, ks, Nil{})), Bool.not(S.mem(kk, SC.append(String, ks, Nil{})))), LS.nd_mid_s(ks, kk, Nil{})), L.and_intro(S.nodup(SC.append(String, ks, Nil{})), Bool.not(S.mem(kk, SC.append(String, ks, Nil{}))), h1, h2))

# a key no listed slot holds is not among their keys
def nokey_nm(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +xs: List<&2, Nat>, +key: String, +h: {ST.nokey(~V, ll, kl, xs, key) == True{} : Bool}) -> {S.mem(key, WL.mapk(ll, kl, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h1 = NL.not_t_f(S.str_eq(ST.skey(ll, kl, x), key), L.and_left(Bool.not(S.str_eq(ST.skey(ll, kl, x), key)), ST.nokey(~V, ll, kl, t, key), h))
      +ih = nokey_nm(~V, ll, kl, t, key, L.and_right(Bool.not(S.str_eq(ST.skey(ll, kl, x), key)), ST.nokey(~V, ll, kl, t, key), h))
      +r1 = L.subst(Bool, z => {Bool.or(z, False{}) == False{} : Bool}, False{}, S.str_eq(ST.skey(ll, kl, x), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, x), key), False{}, h1), {==})
      L.subst(Bool, z => {Bool.or(S.str_eq(ST.skey(ll, kl, x), key), z) == False{} : Bool}, False{}, S.mem(key, WL.mapk(ll, kl, t)), Equal.sym(Bool, S.mem(key, WL.mapk(ll, kl, t)), False{}, ih), r1)

# ---- the bucket written at 2e, 2e + 1 ----


def tp_ev(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {UD.v(U32.from_nat(e)) == e : Nat}:
  U.to_nat_from_nat(e, k, N.lt_le(k, 32n, N.lt_trans(k, 30n, 32n, hk30, {==})), he)

def tp_h(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {Nat.is_lt(1n+Nat.double(UD.v(U32.from_nat(e))), SC.pow2(1n+k)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(1n+Nat.double(z), SC.pow2(1n+k)) == True{} : Bool}, e, UD.v(U32.from_nat(e)), Equal.sym(Nat, UD.v(U32.from_nat(e)), e, tp_ev(k, hk30, tabT, pt, e, he, w, l)), N.double_lt_bit(True{}, e, SC.pow2(k), he))

def tp_i1(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {UD.v(U32.shl(U32.from_nat(e))) == Nat.double(e) : Nat}:
  Equal.trans(Nat, UD.v(U32.shl(U32.from_nat(e))), Nat.double(UD.v(U32.from_nat(e))), Nat.double(e), AX.ix_w(U32.from_nat(e), 1n+k, N.lt_trans(1n+k, 31n, 32n, hk30, {==}), tp_h(k, hk30, tabT, pt, e, he, w, l)), Equal.cong(Nat, Nat, z => Nat.double(z), UD.v(U32.from_nat(e)), e, tp_ev(k, hk30, tabT, pt, e, he, w, l)))

def tp_i2(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {UD.v(U32.inc(U32.shl(U32.from_nat(e)))) == 1n+Nat.double(e) : Nat}:
  Equal.trans(Nat, UD.v(U32.inc(U32.shl(U32.from_nat(e)))), 1n+Nat.double(UD.v(U32.from_nat(e))), 1n+Nat.double(e), AX.ix_l(U32.from_nat(e), 1n+k, N.lt_trans(1n+k, 31n, 32n, hk30, {==}), tp_h(k, hk30, tabT, pt, e, he, w, l)), Equal.cong(Nat, Nat, z => 1n+Nat.double(z), UD.v(U32.from_nat(e)), e, tp_ev(k, hk30, tabT, pt, e, he, w, l)))

def tp_p(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {AR.perfect(U32, 1n+k, AR.upd(U32, 1n+k, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l)) == True{} : Bool}:
  AR.upd_perfect(U32, 1n+k, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l, AR.upd_perfect(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w, pt))

# the written table's slots
def tp_sl(+k: Nat, +hk30: {Nat.is_lt(k, 30n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32) -> {AR.slots(U32, AR.upd(U32, 1n+k, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l)) == SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), 1n+Nat.double(e), l) : List<&2, U32>}:
  +i1 = tp_i1(k, hk30, tabT, pt, e, he, w, l)
  +i2 = tp_i2(k, hk30, tabT, pt, e, he, w, l)
  +h1 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, Nat.double(e), UD.v(U32.shl(U32.from_nat(e))), Equal.sym(Nat, UD.v(U32.shl(U32.from_nat(e))), Nat.double(e), i1), N.double_lt(e, SC.pow2(k), he))
  +h2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(e), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(U32.from_nat(e)))), 1n+Nat.double(e), i2), N.double_lt_bit(True{}, e, SC.pow2(k), he))
  +p1 = AR.upd_perfect(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w, pt)
  +e1 = AR.upd_slots(U32, 1n+k, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l, h2, p1)
  +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), AR.slots(U32, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w)), SC.update(U32, AR.slots(U32, tabT), UD.v(U32.shl(U32.from_nat(e))), w), AR.upd_slots(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w, h1, pt))
  +e3 = Equal.cong(Nat, List<&2, U32>, z => SC.update(U32, SC.update(U32, AR.slots(U32, tabT), z, w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), UD.v(U32.shl(U32.from_nat(e))), Nat.double(e), i1)
  +e4 = Equal.cong(Nat, List<&2, U32>, z => SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), z, l), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), 1n+Nat.double(e), i2)
  Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, 1n+k, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l)), SC.update(U32, AR.slots(U32, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w)), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), 1n+Nat.double(e), l), e1, Equal.trans(List<&2, U32>, SC.update(U32, AR.slots(U32, AR.upd(U32, 1n+k, tabT, UD.v(U32.shl(U32.from_nat(e))), w)), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), SC.update(U32, SC.update(U32, AR.slots(U32, tabT), UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), 1n+Nat.double(e), l), e2, Equal.trans(List<&2, U32>, SC.update(U32, SC.update(U32, AR.slots(U32, tabT), UD.v(U32.shl(U32.from_nat(e))), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), UD.v(U32.inc(U32.shl(U32.from_nat(e)))), l), SC.update(U32, SC.update(U32, AR.slots(U32, tabT), Nat.double(e), w), 1n+Nat.double(e), l), e3, e4)))

# the table index e is below the table's length
def tp_len(+tb: List<&2, U32>, +kl: List<&2, String>, +k: Nat, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}) -> {Nat.is_lt(e, SC.length(B.Bk, TB.buckets(tb, kl, SC.pow2(k)))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(e, z) == True{} : Bool}, SC.pow2(k), SC.length(B.Bk, TB.buckets(tb, kl, SC.pow2(k))), Equal.sym(Nat, SC.length(B.Bk, TB.buckets(tb, kl, SC.pow2(k))), SC.pow2(k), IA.len_dlist(tb, kl, SC.pow2(k), 0n)), he)
