import Base
import ../../lib/logic.bend as L
import ../../lib/spec_common.bend as SC
import ../hash_table/spec.bend as S
import ./spec.bend as SP
import ../../../src/math/u64.bend as W
import ../hash_table/keys.bend as K
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ./lists.bend as LS
import ../../lib/nat_list.bend as NL

# The recency list and the model when a slot moves to the newest end.


# ---- splitting a list at a member ----





# ---- the model ----

# the entry of a live slot
def ent(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, m: Maybe<&2, V>) -> List<&2, SP.Ent<V>>:
  ST.sent_m(~V, ll, kl, s, m)

def enk_of(~V: Data, +x: String, +key: String, +hx: {S.str_eq(x, key) == True{} : Bool}, +xs: List<&2, SP.Ent<V>>, +h: {S.mem(x, SP.keys_of(~V, xs)) == False{} : Bool}) -> {LS.enk(~V, xs, key) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{SP.LE{+k, +v, +t, +d}, +r}:
      +h1 = NL.or_ff_l(S.str_eq(k, x), S.mem(x, SP.keys_of(~V, r)), h)
      +ex = K.str_eq_of(x, key, hx)
      +h2 = L.subst(String, z => {S.str_eq(k, z) == False{} : Bool}, x, key, ex, h1)
      L.and_intro(Bool.not(S.str_eq(k, key)), LS.enk(~V, r, key), NL.not_f(S.str_eq(k, key), h2), enk_of(~V, x, key, hx, r, NL.or_ff_r(S.str_eq(k, x), S.mem(x, SP.keys_of(~V, r)), h)))

def drop_here(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +m: Maybe<&2, V>, +hm: {HT.some_b(~V, m) == True{} : Bool}, +r: List<&2, SP.Ent<V>>, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}) -> {SP.drop(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), r), key) == r : List<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      Empty.absurd({SP.drop(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, None{}), r), key) == r : List<&2, SP.Ent<V>>}, L.false_true(hm))
    case Some{v}:
      L.subst(Bool, z => {Bool.pick(List<&2, SP.Ent<V>>, z, r, Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, SP.drop(~V, r, key)}) == r : List<&2, SP.Ent<V>>}, True{}, S.str_eq(ST.skey(ll, kl, s), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s), key), True{}, hk), {==})

def keys_here(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +m: Maybe<&2, V>, +hm: {HT.some_b(~V, m) == True{} : Bool}, +r: List<&2, SP.Ent<V>>) -> {SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), r)) == Con{ST.skey(ll, kl, s), SP.keys_of(~V, r)} : List<&2, String>}:
  match m:
    case None{}:
      Empty.absurd({SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, None{}), r)) == Con{ST.skey(ll, kl, s), SP.keys_of(~V, r)} : List<&2, String>}, L.false_true(hm))
    case Some{v}:
      {==}

# keys unique and s holding key: no slot of a holds it
def enk_a(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hl: {ST.live(~V, el, s) == True{} : Bool}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +hnd: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})))) == True{} : Bool}) -> {LS.enk(~V, ST.es(~V, ll, kl, el, a), key) == True{} : Bool}:
  +ka = SP.keys_of(~V, ST.es(~V, ll, kl, el, a))
  +kb = SP.keys_of(~V, ST.es(~V, ll, kl, el, b))
  +e1 = Equal.trans(List<&2, String>, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b}))), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b}))), SC.append(String, ka, Con{ST.skey(ll, kl, s), kb}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, String>, z => SP.keys_of(~V, z), ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b})), LS.es_app(~V, ll, kl, el, a, Con{s, b})), Equal.trans(List<&2, String>, SP.keys_of(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b}))), SC.append(String, ka, SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s, b}))), SC.append(String, ka, Con{ST.skey(ll, kl, s), kb}), LS.keys_app(~V, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b})), Equal.cong(List<&2, String>, List<&2, String>, z => SC.append(String, ka, z), SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s, b})), Con{ST.skey(ll, kl, s), kb}, keys_here(~V, ll, kl, el, s, HT.nthm(~V, el, s), hl, ST.es(~V, ll, kl, el, b)))))
  +h2 = L.subst(List<&2, String>, z => {S.nodup(z) == True{} : Bool}, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b}))), SC.append(String, ka, Con{ST.skey(ll, kl, s), kb}), e1, hnd)
  +h3 = L.and_right(S.nodup(SC.append(String, ka, kb)), Bool.not(S.mem(ST.skey(ll, kl, s), SC.append(String, ka, kb))), L.subst(Bool, z => {z == True{} : Bool}, S.nodup(SC.append(String, ka, Con{ST.skey(ll, kl, s), kb})), Bool.and(S.nodup(SC.append(String, ka, kb)), Bool.not(S.mem(ST.skey(ll, kl, s), SC.append(String, ka, kb)))), LS.nd_mid_s(ka, ST.skey(ll, kl, s), kb), h2))
  +h4 = NL.or_f_l(S.mem(ST.skey(ll, kl, s), ka), S.mem(ST.skey(ll, kl, s), kb), L.subst(Bool, z => {z == False{} : Bool}, S.mem(ST.skey(ll, kl, s), SC.append(String, ka, kb)), Bool.or(S.mem(ST.skey(ll, kl, s), ka), S.mem(ST.skey(ll, kl, s), kb)), LS.mem_app_s(ST.skey(ll, kl, s), ka, kb), L.not_true(S.mem(ST.skey(ll, kl, s), SC.append(String, ka, kb)), h3)))
  enk_of(~V, ST.skey(ll, kl, s), key, hk, ST.es(~V, ll, kl, el, a), h4)


# the model entry of slot s holding value v
def ev(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +v: V) -> SP.Ent<V>:
  SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}

def es_cons(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}, +b: List<&2, Nat>) -> {ST.es(~V, ll, kl, el, Con{s, b}) == Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)} : List<&2, SP.Ent<V>>}:
  Equal.cong(Maybe<&2, V>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, z), ST.es(~V, ll, kl, el, b)), HT.nthm(~V, el, s), Some{v}, hm)

# THEOREM (model side of a touch): dropping the key's entry and appending it
# is the model of the list a ++ b ++ [s]
def spec_touch(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +hnd: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})))) == True{} : Bool}) -> {SP.snoc(~V, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}) == ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})) : List<&2, SP.Ent<V>>}:
  +hl = L.subst(Maybe<&2, V>, z => {HT.some_b(~V, z) == True{} : Bool}, Some{v}, HT.nthm(~V, el, s), Equal.sym(Maybe<&2, V>, HT.nthm(~V, el, s), Some{v}, hm), {==})
  +ea = LS.es_app(~V, ll, kl, el, a, Con{s, b})
  +ec = es_cons(~V, ll, kl, el, s, v, hm, b)
  +e1 = Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}), ea, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), z), ST.es(~V, ll, kl, el, Con{s, b}), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}, ec))
  +hen = enk_a(~V, ll, kl, el, a, s, b, hl, key, hk, hnd)
  +d1 = LS.drop_app(~V, ST.es(~V, ll, kl, el, a), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}, key, hen)
  +d2 = L.subst(Bool, z => {Bool.pick(List<&2, SP.Ent<V>>, z, ST.es(~V, ll, kl, el, b), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, SP.drop(~V, ST.es(~V, ll, kl, el, b), key)}) == ST.es(~V, ll, kl, el, b) : List<&2, SP.Ent<V>>}, True{}, S.str_eq(ST.skey(ll, kl, s), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s), key), True{}, hk), {==})
  +dr = Equal.trans(List<&2, SP.Ent<V>>, SP.drop(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), SP.drop(~V, Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}, key)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), d1, Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), z), SP.drop(~V, Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}, key), ST.es(~V, ll, kl, el, b), d2))
  +d3 = Equal.trans(List<&2, SP.Ent<V>>, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SP.drop(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SP.drop(~V, z, key), ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, b)}), e1), dr)
  +sn = Equal.trans(List<&2, SP.Ent<V>>, SP.snoc(~V, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}), SP.snoc(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SP.snoc(~V, z, SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}), SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), d3), LS.snoc_app(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}))
  +r1 = Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}), LS.es_app(~V, ll, kl, el, SC.append(Nat, a, b), Con{s, Nil{}}), Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, ll, kl, el, Con{s, Nil{}})), ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), LS.es_app(~V, ll, kl, el, a, b)), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), z), ST.es(~V, ll, kl, el, Con{s, Nil{}}), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}, es_cons(~V, ll, kl, el, s, v, hm, Nil{}))))
  Equal.trans(List<&2, SP.Ent<V>>, SP.snoc(~V, SP.drop(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), key), SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}), ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), sn, Equal.sym(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, Nil{}}), r1))
