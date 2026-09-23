import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../spec/lru.bend as SP
import ../../src/math/u64.bend as W
import ../hash_table/state.bend as HT
import ../hash_table/tools.bend as TL
import ./state.bend as ST
import ./lists.bend as LS
import ./dll.bend as DL
import ./touch.bend as TO

# Writes to a value cell off the list, and the model after a removal.


def live_el(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +m: Maybe<&2, V>, +x: Nat, +h: {Nat.is_eq(y, x) == False{} : Bool}) -> {ST.live(~V, SC.update(Maybe<&2, V>, el, y, m), x) == ST.live(~V, el, x) : Bool}:
  Equal.cong(Maybe<&2, V>, Bool, z => HT.some_b(~V, z), HT.nthm(~V, SC.update(Maybe<&2, V>, el, y, m), x), HT.nthm(~V, el, x), TL.nthm_upd_other(~V, el, y, x, m, h))

def slok_el(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +m: Maybe<&2, V>, +fr: Nat, +xs: List<&2, Nat>, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.slok(~V, xs, fr, SC.update(Maybe<&2, V>, el, y, m)) == ST.slok(~V, xs, fr, el) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hyx = DL.ne_sym(x, y, DL.or_ff_l(Nat.is_eq(x, y), HT.memn(y, t), hy))
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), z), ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m))), ST.live(~V, SC.update(Maybe<&2, V>, el, y, m), x), ST.live(~V, el, x), live_el(~V, el, y, m, x, hyx))
      Equal.trans(Bool, ST.slok(~V, Con{x, t}, fr, SC.update(Maybe<&2, V>, el, y, m)), Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m))), ST.slok(~V, Con{x, t}, fr, el), e1, Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), z), ST.slok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m)), ST.slok(~V, t, fr, el), slok_el(~V, el, y, m, fr, t, DL.or_ff_r(Nat.is_eq(x, y), HT.memn(y, t), hy))))

def flok_el(~V: Data, +el: List<&2, Maybe<&2, V>>, +y: Nat, +m: Maybe<&2, V>, +fr: Nat, +xs: List<&2, Nat>, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.flok(~V, xs, fr, SC.update(Maybe<&2, V>, el, y, m)) == ST.flok(~V, xs, fr, el) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hyx = DL.ne_sym(x, y, DL.or_ff_l(Nat.is_eq(x, y), HT.memn(y, t), hy))
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), Bool.not(z)), ST.flok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m))), ST.live(~V, SC.update(Maybe<&2, V>, el, y, m), x), ST.live(~V, el, x), live_el(~V, el, y, m, x, hyx))
      Equal.trans(Bool, ST.flok(~V, Con{x, t}, fr, SC.update(Maybe<&2, V>, el, y, m)), Bool.and(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(~V, el, x))), ST.flok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m))), ST.flok(~V, Con{x, t}, fr, el), e1, Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Nat.is_lt(x, fr), Bool.not(ST.live(~V, el, x))), z), ST.flok(~V, t, fr, SC.update(Maybe<&2, V>, el, y, m)), ST.flok(~V, t, fr, el), flok_el(~V, el, y, m, fr, t, DL.or_ff_r(Nat.is_eq(x, y), HT.memn(y, t), hy))))

def es_el(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +y: Nat, +m: Maybe<&2, V>, +xs: List<&2, Nat>, +hy: {HT.memn(y, xs) == False{} : Bool}) -> {ST.es(~V, ll, kl, SC.update(Maybe<&2, V>, el, y, m), xs) == ST.es(~V, ll, kl, el, xs) : List<&2, SP.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hyx = DL.ne_sym(x, y, DL.or_ff_l(Nat.is_eq(x, y), HT.memn(y, t), hy))
      +e1 = Equal.cong(Maybe<&2, V>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, z), ST.es(~V, ll, kl, SC.update(Maybe<&2, V>, el, y, m), t)), HT.nthm(~V, SC.update(Maybe<&2, V>, el, y, m), x), HT.nthm(~V, el, x), TL.nthm_upd_other(~V, el, y, x, m, hyx))
      Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, SC.update(Maybe<&2, V>, el, y, m), Con{x, t}), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), ST.es(~V, ll, kl, SC.update(Maybe<&2, V>, el, y, m), t)), ST.es(~V, ll, kl, el, Con{x, t}), e1, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), z), ST.es(~V, ll, kl, SC.update(Maybe<&2, V>, el, y, m), t), ST.es(~V, ll, kl, el, t), es_el(~V, ll, kl, el, y, m, t, DL.or_ff_r(Nat.is_eq(x, y), HT.memn(y, t), hy))))

# THEOREM (model side of a removal): dropping key's entry is the model of a ++ b
def spec_drop(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +hnd: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})))) == True{} : Bool}) -> {SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key) == ST.es(~V, ll, kl, el, SC.append(Nat, a, b)) : List<&2, SP.Ent<V>>}:
  +E = TO.ev(~V, ll, kl, s, v)
  +hl = L.subst(Maybe<&2, V>, z => {HT.some_b(~V, z) == True{} : Bool}, Some{v}, HT.nthm(~V, el, s), Equal.sym(Maybe<&2, V>, HT.nthm(~V, el, s), Some{v}, hm), {==})
  +e1 = Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{E, ST.es(~V, ll, kl, el, b)}), LS.es_app(~V, ll, kl, el, a, Con{s, b}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), z), ST.es(~V, ll, kl, el, Con{s, b}), Con{E, ST.es(~V, ll, kl, el, b)}, TO.es_cons(~V, ll, kl, el, s, v, hm, b)))
  +d1 = LS.drop_app(~V, ST.es(~V, ll, kl, el, a), Con{E, ST.es(~V, ll, kl, el, b)}, key, TO.enk_a(~V, ll, kl, el, a, s, b, hl, key, hk, hnd))
  +d2 = L.subst(Bool, z => {Bool.pick(List<&2, SP.Ent<V>>, z, ST.es(~V, ll, kl, el, b), Con{E, SP.drop(~V, ST.es(~V, ll, kl, el, b), key)}) == ST.es(~V, ll, kl, el, b) : List<&2, SP.Ent<V>>}, True{}, S.str_eq(ST.skey(ll, kl, s), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s), key), True{}, hk), {==})
  +d3 = Equal.trans(List<&2, SP.Ent<V>>, SP.drop(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{E, ST.es(~V, ll, kl, el, b)}), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), SP.drop(~V, Con{E, ST.es(~V, ll, kl, el, b)}, key)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), d1, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), z), SP.drop(~V, Con{E, ST.es(~V, ll, kl, el, b)}, key), ST.es(~V, ll, kl, el, b), d2))
  Equal.trans(List<&2, SP.Ent<V>>, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), Equal.trans(List<&2, SP.Ent<V>>, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SP.drop(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{E, ST.es(~V, ll, kl, el, b)}), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SP.drop(~V, z, key), ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{E, ST.es(~V, ll, kl, el, b)}), e1), d3), Equal.sym(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), LS.es_app(~V, ll, kl, el, a, b)))
