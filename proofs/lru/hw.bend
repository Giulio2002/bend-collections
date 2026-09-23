import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/hash_table.bend as H
import ../hash_table/buckets.bend as B
import ../hash_table/state.bend as HT
import ../hash_table/table.bend as TB
import ../hash_table/tools.bend as TL
import ./state.bend as ST
import ./dll.bend as DL
import ./elfr.bend as EF
import ./walk.bend as WL

# Writes to a slot's data words (o >= 3: the lifetime and deadline) keep its
# links and its stored hash word; a value written to a slot keeps it live.


def ne_hi(+o2: Nat, +o: Nat, +h: {Nat.is_lt(o2, 3n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}) -> {Nat.is_eq(o, o2) == False{} : Bool}:
  DL.ne_sym(o2, o, N.is_eq_lt(o2, o, N.lt_le_trans(o2, 3n, o, h, h3)))

def lw_lo3(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +x: Nat, +o2: Nat, +ho2: {Nat.is_lt(o2, 8n) == True{} : Bool}, +h: {Nat.is_lt(o2, 3n) == True{} : Bool}) -> {ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, o2) == ST.lw(ll, x, o2) : U32}:
  DL.lw_other(ll, y, o, v, ho, x, o2, ho2, DL.ne_word(y, x, o, o2, ne_hi(o2, o, h, h3)))

def seg_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +sl: List<&2, Nat>, +p: U32, +q: U32) -> {ST.seg(SC.update(U32, ll, ST.off(y, o), v), sl, p, q) == ST.seg(ll, sl, p, q) : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      DL.seg_c(SC.update(U32, ll, ST.off(y, o), v), ll, s, t, p, q, lw_lo3(ll, y, o, v, ho, h3, s, 0n, {==}, {==}), lw_lo3(ll, y, o, v, ho, h3, s, 1n, {==}, {==}), seg_hw(ll, y, o, v, ho, h3, t, ST.lnk(s), q))

def fll_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +fl: List<&2, Nat>) -> {ST.fll(SC.update(U32, ll, ST.off(y, o), v), fl) == ST.fll(ll, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +e1 = lw_lo3(ll, y, o, v, ho, h3, s, 1n, {==}, {==})
      +ih = fll_hw(ll, y, o, v, ho, h3, t)
      +r1 = L.subst(U32, z => {Bool.and(U32.is_eq(z, ST.fst_or(t, 0)), ST.fll(ll, t)) == ST.fll(ll, Con{s, t}) : Bool}, ST.lw(ll, s, 1n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), Equal.sym(U32, ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), ST.lw(ll, s, 1n), e1), {==})
      L.subst(Bool, z => {Bool.and(U32.is_eq(ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 1n), ST.fst_or(t, 0)), z) == ST.fll(ll, Con{s, t}) : Bool}, ST.fll(ll, t), ST.fll(SC.update(U32, ll, ST.off(y, o), v), t), Equal.sym(Bool, ST.fll(SC.update(U32, ll, ST.off(y, o), v), t), ST.fll(ll, t), ih), r1)

def skey_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +kl: List<&2, String>, +x: Nat) -> {ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x) == ST.skey(ll, kl, x) : String}:
  Equal.cong(U32, String, z => TB.keyof(z, TB.nths(kl, x)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 2n), ST.lw(ll, x, 2n), lw_lo3(ll, y, o, v, ho, h3, x, 2n, {==}, {==}))

def has_hw(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +bs: List<&2, B.Bk>, +m: Nat, +sl: List<&2, Nat>) -> {ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), sl) == ST.hasall(~V, bs, m, ll, sl) : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +e = Equal.cong(U32, Bool, z => ST.anyb(bs, m, ST.lnk(s), z), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n), ST.lw(ll, s, 2n), lw_lo3(ll, y, o, v, ho, h3, s, 2n, {==}, {==}))
      Equal.trans(Bool, Bool.and(ST.anyb(bs, m, ST.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, ST.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), Bool.and(ST.anyb(bs, m, ST.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, bs, m, ll, t)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t)), ST.anyb(bs, m, ST.lnk(s), ST.lw(SC.update(U32, ll, ST.off(y, o), v), s, 2n)), ST.anyb(bs, m, ST.lnk(s), ST.lw(ll, s, 2n)), e), Equal.cong(Bool, Bool, z => Bool.and(ST.anyb(bs, m, ST.lnk(s), ST.lw(ll, s, 2n)), z), ST.hasall(~V, bs, m, SC.update(U32, ll, ST.off(y, o), v), t), ST.hasall(~V, bs, m, ll, t), has_hw(~V, ll, y, o, v, ho, h3, bs, m, t)))

def bslb_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +sl: List<&2, Nat>, +b: B.Bk) -> {ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), b) == ST.bslb(sl, ll, b) : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      Equal.cong(U32, Bool, z => Bool.and(HT.memn(UD.v(H.slot(l)), sl), U32.is_eq(z, w)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), UD.v(H.slot(l)), 2n), ST.lw(ll, UD.v(H.slot(l)), 2n), lw_lo3(ll, y, o, v, ho, h3, UD.v(H.slot(l)), 2n, {==}, {==}))

def bsl_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +m: Nat) -> {ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), m) == ST.bsl(bs, sl, ll, m) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Bool, Bool.and(ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j)), ST.bslb(sl, SC.update(U32, ll, ST.off(y, o), v), B.at(bs, j)), ST.bslb(sl, ll, B.at(bs, j)), bslb_hw(ll, y, o, v, ho, h3, sl, B.at(bs, j))), Equal.cong(Bool, Bool, z => Bool.and(ST.bslb(sl, ll, B.at(bs, j)), z), ST.bsl(bs, sl, SC.update(U32, ll, ST.off(y, o), v), j), ST.bsl(bs, sl, ll, j), bsl_hw(ll, y, o, v, ho, h3, bs, sl, j)))

def mapk_hw(+ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +h3: {Nat.is_le(3n, o) == True{} : Bool}, +kl: List<&2, String>, +xs: List<&2, Nat>) -> {WL.mapk(SC.update(U32, ll, ST.off(y, o), v), kl, xs) == WL.mapk(ll, kl, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(List<&2, String>, Con{ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x), WL.mapk(SC.update(U32, ll, ST.off(y, o), v), kl, t)}, Con{ST.skey(ll, kl, x), WL.mapk(SC.update(U32, ll, ST.off(y, o), v), kl, t)}, Con{ST.skey(ll, kl, x), WL.mapk(ll, kl, t)}, Equal.cong(String, List<&2, String>, z => Con{z, WL.mapk(SC.update(U32, ll, ST.off(y, o), v), kl, t)}, ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x), ST.skey(ll, kl, x), skey_hw(ll, y, o, v, ho, h3, kl, x)), Equal.cong(List<&2, String>, List<&2, String>, z => Con{ST.skey(ll, kl, x), z}, WL.mapk(SC.update(U32, ll, ST.off(y, o), v), kl, t), WL.mapk(ll, kl, t), mapk_hw(ll, y, o, v, ho, h3, kl, t)))

# ---- a value written to a slot ----


# the written slot is live
def live_same(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +w: V, +hlen: {Nat.is_lt(y, SC.length(Maybe<&2, V>, el)) == True{} : Bool}) -> {ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), y) == True{} : Bool}:
  Equal.cong(Maybe<&2, V>, Bool, z => HT.some_b(~V, z), HT.nthm(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), y), Some{w}, TL.nthm_upd_same(~V, el, y, Some{w}, hlen))

def sl_c(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +w: V, +fr: Nat, +x: Nat, +t: List<&2, Nat>, +hlen: {Nat.is_lt(y, SC.length(Maybe<&2, V>, el)) == True{} : Bool}, +h: {ST.slok(~V, Con{x, t}, fr, el) == True{} : Bool}, +ih: {ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, Some{w})) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(y, x) == c : Bool}) -> {ST.slok(~V, Con{x, t}, fr, SC.update(Maybe<&2, V>, el, y, Some{w})) == True{} : Bool}:
  match c:
    case True{}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)
      +hx = L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), h0)
      +hl = L.and_right(Nat.is_lt(x, fr), ST.live(~V, el, x), h0)
      +lv = L.subst(Nat, z => {ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), z) == True{} : Bool}, y, x, N.eq_from_is_eq(y, x, hc), live_same(~V, el, y, w, hlen))
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), x)), ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, Some{w})), L.and_intro(Nat.is_lt(x, fr), ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), x), hx, lv), ih)
    case False{}:
      +h0 = L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)
      +hx = L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), h0)
      +hl = L.and_right(Nat.is_lt(x, fr), ST.live(~V, el, x), h0)
      +lv = Equal.trans(Bool, ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), x), ST.live(~V, el, x), True{}, EF.live_el(~V, el, y, Some{w}, x, hc), hl)
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), x)), ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, Some{w})), L.and_intro(Nat.is_lt(x, fr), ST.live(~V, SC.update(Maybe<&2, V>, el, y, Some{w}), x), hx, lv), ih)

# a value written anywhere keeps every listed slot live
def slok_live(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +w: V, +fr: Nat, +xs: List<&2, Nat>, +hlen: {Nat.is_lt(y, SC.length(Maybe<&2, V>, el)) == True{} : Bool}, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}) -> {ST.slok(~V, xs, fr, SC.update(Maybe<&2, V>, el, y, Some{w})) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      sl_c(~V, el, y, w, fr, x, t, hlen, h, slok_live(~V, el, y, w, fr, t, hlen, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), Nat.is_eq(y, x), {==})

# ---- writes to a slot off the list ----


def sent_fs(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +hyx: {Nat.is_eq(y, x) == False{} : Bool}, +m: Maybe<&2, V>) -> {ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, m) == ST.sent_m(~V, ll, kl, x, m) : List<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      +ek = Equal.cong(U32, String, z => TB.keyof(z, TB.nths(kl, x)), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 2n), ST.lw(ll, x, 2n), DL.lw_other(ll, y, o, v, ho, x, 2n, {==}, DL.ne_slot(y, x, o, 2n, hyx)))
      +r1 = L.subst(String, z => {Con{SP.LE{z, w, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 3n), W.U64{ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.skey(SC.update(U32, ll, ST.off(y, o), v), kl, x), ST.skey(ll, kl, x), ek, {==})
      +r2 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, z, W.U64{ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 3n), ST.lw(ll, x, 3n), DL.lw_other(ll, y, o, v, ho, x, 3n, {==}, DL.ne_slot(y, x, o, 3n, hyx)), r1)
      +r3 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{z, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 4n), ST.lw(ll, x, 4n), DL.lw_other(ll, y, o, v, ho, x, 4n, {==}, DL.ne_slot(y, x, o, 4n, hyx)), r2)
      +r4 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{ST.lw(ll, x, 4n), z}}, Nil{}} == ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.update(U32, ll, ST.off(y, o), v), x, 5n), ST.lw(ll, x, 5n), DL.lw_other(ll, y, o, v, ho, x, 5n, {==}, DL.ne_slot(y, x, o, 5n, hyx)), r3)
      Equal.sym(List<&2, SP.Ent<V>>, ST.sent_m(~V, ll, kl, x, Some{w}), ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, x, Some{w}), r4)

# a write to a slot off xs leaves the entries of xs
def es_fs(~V: Data, +ll: List<&2, U32>, +y: Nat, +o: Nat, +v: U32, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +xs: List<&2, Nat>, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, xs) == ST.es(~V, ll, kl, el, xs) : List<&2, SP.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hyx = DL.ne_sym(s, y, DL.or_ff_l(Nat.is_eq(s, y), HT.memn(y, t), hy))
      +m = HT.nthm(~V, el, s)
      +a = Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, s, m), ST.sent_m(~V, ll, kl, s, m), sent_fs(~V, ll, y, o, v, ho, kl, s, hyx, m))
      Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.sent_m(~V, SC.update(U32, ll, ST.off(y, o), v), kl, s, m), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), ST.es(~V, ll, kl, el, t)), a, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), z), ST.es(~V, SC.update(U32, ll, ST.off(y, o), v), kl, el, t), ST.es(~V, ll, kl, el, t), es_fs(~V, ll, y, o, v, ho, kl, el, t, DL.or_ff_r(Nat.is_eq(s, y), HT.memn(y, t), hy))))
