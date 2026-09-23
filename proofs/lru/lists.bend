import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../spec/lru.bend as SP
import ../../src/math/u64.bend as W
import ../hash_table/keys.bend as K
import ../hash_table/state.bend as HT
import ./state.bend as ST

# List algebra for the recency list and the model's keys: membership,
# duplicate-freedom and the per-slot predicates over appends.


# ---- Bool algebra ----

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_comm(+a: Bool, +b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# not (x or y) and (z and not w)  ==  (not x and z) and not (y or w)
def bt_mid(+x: Bool, +y: Bool, +z: Bool, +w: Bool) -> {Bool.and(Bool.not(Bool.or(x, y)), Bool.and(z, Bool.not(w))) == Bool.and(Bool.and(Bool.not(x), z), Bool.not(Bool.or(y, w))) : Bool}:
  match x y z w:
    case True{} y2 z2 w2:
      {==}
    case False{} True{} z2 w2:
      +e = and_comm(z2, False{})
      Equal.trans(Bool, Bool.and(False{}, Bool.and(z2, Bool.not(w2))), False{}, Bool.and(z2, False{}), {==}, Equal.sym(Bool, Bool.and(z2, False{}), False{}, Equal.trans(Bool, Bool.and(z2, False{}), Bool.and(False{}, z2), False{}, e, {==})))
    case False{} False{} True{} w2:
      {==}
    case False{} False{} False{} w2:
      {==}

def is_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_eq_sym(p, q)

# ---- slot lists ----

def memn_app(+x: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {HT.memn(x, SC.append(Nat, a, b)) == Bool.or(HT.memn(x, a), HT.memn(x, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(h, x), HT.memn(x, SC.append(Nat, t, b))), Bool.or(Nat.is_eq(h, x), Bool.or(HT.memn(x, t), HT.memn(x, b))), Bool.or(Bool.or(Nat.is_eq(h, x), HT.memn(x, t)), HT.memn(x, b)), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(h, x), z), HT.memn(x, SC.append(Nat, t, b)), Bool.or(HT.memn(x, t), HT.memn(x, b)), memn_app(x, t, b)), or_assoc(Nat.is_eq(h, x), HT.memn(x, t), HT.memn(x, b)))

def memn_mid(+x: Nat, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {HT.memn(x, SC.append(Nat, a, Con{s, b})) == Bool.or(HT.memn(x, SC.append(Nat, a, b)), Nat.is_eq(s, x)) : Bool}:
  match a:
    case Nil{}:
      or_comm(Nat.is_eq(s, x), HT.memn(x, b))
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(h, x), HT.memn(x, SC.append(Nat, t, Con{s, b}))), Bool.or(Nat.is_eq(h, x), Bool.or(HT.memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x))), Bool.or(Bool.or(Nat.is_eq(h, x), HT.memn(x, SC.append(Nat, t, b))), Nat.is_eq(s, x)), Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(h, x), z), HT.memn(x, SC.append(Nat, t, Con{s, b})), Bool.or(HT.memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x)), memn_mid(x, t, s, b)), or_assoc(Nat.is_eq(h, x), HT.memn(x, SC.append(Nat, t, b)), Nat.is_eq(s, x)))

def nd_mid(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {ST.nodupn(SC.append(Nat, a, Con{s, b})) == Bool.and(ST.nodupn(SC.append(Nat, a, b)), Bool.not(HT.memn(s, SC.append(Nat, a, b)))) : Bool}:
  match a:
    case Nil{}:
      and_comm(Bool.not(HT.memn(s, b)), ST.nodupn(b))
    case Con{+h, +t}:
      +X = HT.memn(h, SC.append(Nat, t, b))
      +Z = ST.nodupn(SC.append(Nat, t, b))
      +Wm = HT.memn(s, SC.append(Nat, t, b))
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), ST.nodupn(SC.append(Nat, t, Con{s, b}))), HT.memn(h, SC.append(Nat, t, Con{s, b})), Bool.or(X, Nat.is_eq(s, h)), memn_mid(h, t, s, b))
      +e2 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), z), ST.nodupn(SC.append(Nat, t, Con{s, b})), Bool.and(Z, Bool.not(Wm)), nd_mid(t, s, b))
      +e3 = bt_mid(X, Nat.is_eq(s, h), Z, Wm)
      +e4 = Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(z, Wm))), Nat.is_eq(s, h), Nat.is_eq(h, s), is_eq_sym(s, h))
      Equal.trans(Bool, ST.nodupn(SC.append(Nat, Con{h, t}, Con{s, b})), Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), ST.nodupn(SC.append(Nat, t, Con{s, b}))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e1, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), ST.nodupn(SC.append(Nat, t, Con{s, b}))), Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e2, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, Nat.is_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(s, h), Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(Nat.is_eq(h, s), Wm))), e3, e4)))

# ---- key lists ----


def mem_mid_s(+x: String, +a: List<&2, String>, +s: String, +b: List<&2, String>) -> {S.mem(x, SC.append(String, a, Con{s, b})) == Bool.or(S.mem(x, SC.append(String, a, b)), S.str_eq(s, x)) : Bool}:
  match a:
    case Nil{}:
      or_comm(S.str_eq(s, x), S.mem(x, b))
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.or(S.str_eq(h, x), S.mem(x, SC.append(String, t, Con{s, b}))), Bool.or(S.str_eq(h, x), Bool.or(S.mem(x, SC.append(String, t, b)), S.str_eq(s, x))), Bool.or(Bool.or(S.str_eq(h, x), S.mem(x, SC.append(String, t, b))), S.str_eq(s, x)), Equal.cong(Bool, Bool, z => Bool.or(S.str_eq(h, x), z), S.mem(x, SC.append(String, t, Con{s, b})), Bool.or(S.mem(x, SC.append(String, t, b)), S.str_eq(s, x)), mem_mid_s(x, t, s, b)), or_assoc(S.str_eq(h, x), S.mem(x, SC.append(String, t, b)), S.str_eq(s, x)))

def nd_mid_s(+a: List<&2, String>, +s: String, +b: List<&2, String>) -> {S.nodup(SC.append(String, a, Con{s, b})) == Bool.and(S.nodup(SC.append(String, a, b)), Bool.not(S.mem(s, SC.append(String, a, b)))) : Bool}:
  match a:
    case Nil{}:
      and_comm(Bool.not(S.mem(s, b)), S.nodup(b))
    case Con{+h, +t}:
      +X = S.mem(h, SC.append(String, t, b))
      +Z = S.nodup(SC.append(String, t, b))
      +Wm = S.mem(s, SC.append(String, t, b))
      +e1 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), S.nodup(SC.append(String, t, Con{s, b}))), S.mem(h, SC.append(String, t, Con{s, b})), Bool.or(X, S.str_eq(s, h)), mem_mid_s(h, t, s, b))
      +e2 = Equal.cong(Bool, Bool, z => Bool.and(Bool.not(Bool.or(X, S.str_eq(s, h))), z), S.nodup(SC.append(String, t, Con{s, b})), Bool.and(Z, Bool.not(Wm)), nd_mid_s(t, s, b))
      +e3 = bt_mid(X, S.str_eq(s, h), Z, Wm)
      +e4 = Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(z, Wm))), S.str_eq(s, h), S.str_eq(h, s), K.str_sym(s, h))
      Equal.trans(Bool, S.nodup(SC.append(String, Con{h, t}, Con{s, b})), Bool.and(Bool.not(Bool.or(X, S.str_eq(s, h))), S.nodup(SC.append(String, t, Con{s, b}))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(S.str_eq(h, s), Wm))), e1, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, S.str_eq(s, h))), S.nodup(SC.append(String, t, Con{s, b}))), Bool.and(Bool.not(Bool.or(X, S.str_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(S.str_eq(h, s), Wm))), e2, Equal.trans(Bool, Bool.and(Bool.not(Bool.or(X, S.str_eq(s, h))), Bool.and(Z, Bool.not(Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(S.str_eq(s, h), Wm))), Bool.and(Bool.and(Bool.not(X), Z), Bool.not(Bool.or(S.str_eq(h, s), Wm))), e3, e4)))

# ---- slot predicates ----

def sall_app(~V: Data, +p: ST.SP1<V>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.sall(~V, p, SC.append(Nat, a, b)) == Bool.and(ST.sall(~V, p, a), ST.sall(~V, p, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Bool, Bool.and(ST.sev(~V, p, h), ST.sall(~V, p, SC.append(Nat, t, b))), Bool.and(ST.sev(~V, p, h), Bool.and(ST.sall(~V, p, t), ST.sall(~V, p, b))), Bool.and(Bool.and(ST.sev(~V, p, h), ST.sall(~V, p, t)), ST.sall(~V, p, b)), Equal.cong(Bool, Bool, z => Bool.and(ST.sev(~V, p, h), z), ST.sall(~V, p, SC.append(Nat, t, b)), Bool.and(ST.sall(~V, p, t), ST.sall(~V, p, b)), sall_app(~V, p, t, b)), and_assoc(ST.sev(~V, p, h), ST.sall(~V, p, t), ST.sall(~V, p, b)))

def sa_c(~V: Data, +p: ST.SP1<V>, +x: Nat, +s0: Nat, +t: List<&2, Nat>, +h: {Bool.and(ST.sev(~V, p, s0), ST.sall(~V, p, t)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(s0, x) == c : Bool}, +hm: {Bool.or(c, HT.memn(x, t)) == True{} : Bool}, rec: @hs: {ST.sall(~V, p, t) == True{} : Bool} -> @hm2: {HT.memn(x, t) == True{} : Bool} -> {ST.sev(~V, p, x) == True{} : Bool}) -> {ST.sev(~V, p, x) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {ST.sev(~V, p, z) == True{} : Bool}, s0, x, N.eq_from_is_eq(s0, x, hc), L.and_left(ST.sev(~V, p, s0), ST.sall(~V, p, t), h))
    case False{}:
      rec(L.and_right(ST.sev(~V, p, s0), ST.sall(~V, p, t), h), hm)

# p holds at a member
def sall_mem(~V: Data, +p: ST.SP1<V>, +x: Nat, +xs: List<&2, Nat>, +h: {ST.sall(~V, p, xs) == True{} : Bool}, +hm: {HT.memn(x, xs) == True{} : Bool}) -> {ST.sev(~V, p, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({ST.sev(~V, p, x) == True{} : Bool}, L.false_true(hm))
    case Con{+s0, +t}:
      sa_c(~V, p, x, s0, t, h, Nat.is_eq(s0, x), {==}, hm, hs => hm2 => sall_mem(~V, p, x, t, hs, hm2))

# ---- the model's entries ----


def es_app(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.es(~V, ll, kl, el, SC.append(Nat, a, b)) == SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)) : List<&2, SP.Ent<V>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +x = ST.sent_m(~V, ll, kl, h, HT.nthm(~V, el, h))
      Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, x, ST.es(~V, ll, kl, el, SC.append(Nat, t, b))), SC.append(SP.Ent<V>, x, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, t), ST.es(~V, ll, kl, el, b))), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, x, ST.es(~V, ll, kl, el, t)), ST.es(~V, ll, kl, el, b)), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, x, z), ST.es(~V, ll, kl, el, SC.append(Nat, t, b)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, t), ST.es(~V, ll, kl, el, b)), es_app(~V, ll, kl, el, t, b)), Equal.sym(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, x, ST.es(~V, ll, kl, el, t)), ST.es(~V, ll, kl, el, b)), SC.append(SP.Ent<V>, x, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, t), ST.es(~V, ll, kl, el, b))), LL.append_assoc(SP.Ent<V>, x, ST.es(~V, ll, kl, el, t), ST.es(~V, ll, kl, el, b))))

def keys_app(~V: Data, +a: List<&2, SP.Ent<V>>, +b: List<&2, SP.Ent<V>>) -> {SP.keys_of(~V, SC.append(SP.Ent<V>, a, b)) == SC.append(String, SP.keys_of(~V, a), SP.keys_of(~V, b)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{SP.LE{+k, +v, +t, +d}, +r}:
      LL.cons_cong(String, k, SP.keys_of(~V, SC.append(SP.Ent<V>, r, b)), SC.append(String, SP.keys_of(~V, r), SP.keys_of(~V, b)), keys_app(~V, r, b))

def snoc_app(~V: Data, +a: List<&2, SP.Ent<V>>, +e: SP.Ent<V>) -> {SP.snoc(~V, a, e) == SC.append(SP.Ent<V>, a, Con{e, Nil{}}) : List<&2, SP.Ent<V>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(SP.Ent<V>, h, SP.snoc(~V, t, e), SC.append(SP.Ent<V>, t, Con{e, Nil{}}), snoc_app(~V, t, e))

# no entry of a has key
def enk(~V: Data, a: List<&2, SP.Ent<V>>, +key: String) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{SP.LE{+k, v, t, d}, r}:
      Bool.and(Bool.not(S.str_eq(k, key)), enk(~V, r, key))

def drop_c(~V: Data, +k: String, +v: V, +t: U32, +d: W.U64, +r: List<&2, SP.Ent<V>>, +b: List<&2, SP.Ent<V>>, +key: String, +c: Bool, +hc: {S.str_eq(k, key) == c : Bool}, +h: {Bool.not(c) == True{} : Bool}, +ih: {SP.drop(~V, SC.append(SP.Ent<V>, r, b), key) == SC.append(SP.Ent<V>, r, SP.drop(~V, b, key)) : List<&2, SP.Ent<V>>}) -> {SP.drop(~V, SC.append(SP.Ent<V>, Con{SP.LE{k, v, t, d}, r}, b), key) == SC.append(SP.Ent<V>, Con{SP.LE{k, v, t, d}, r}, SP.drop(~V, b, key)) : List<&2, SP.Ent<V>>}:
  match c:
    case True{}:
      Empty.absurd({SP.drop(~V, SC.append(SP.Ent<V>, Con{SP.LE{k, v, t, d}, r}, b), key) == SC.append(SP.Ent<V>, Con{SP.LE{k, v, t, d}, r}, SP.drop(~V, b, key)) : List<&2, SP.Ent<V>>}, L.false_true(h))
    case False{}:
      L.subst(Bool, z => {Bool.pick(List<&2, SP.Ent<V>>, z, SC.append(SP.Ent<V>, r, b), Con{SP.LE{k, v, t, d}, SP.drop(~V, SC.append(SP.Ent<V>, r, b), key)}) == SC.append(SP.Ent<V>, Con{SP.LE{k, v, t, d}, r}, SP.drop(~V, b, key)) : List<&2, SP.Ent<V>>}, False{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), False{}, hc), LL.cons_cong(SP.Ent<V>, SP.LE{k, v, t, d}, SP.drop(~V, SC.append(SP.Ent<V>, r, b), key), SC.append(SP.Ent<V>, r, SP.drop(~V, b, key)), ih))

# drop skips a prefix without key
def drop_app(~V: Data, +a: List<&2, SP.Ent<V>>, +b: List<&2, SP.Ent<V>>, +key: String, +h: {enk(~V, a, key) == True{} : Bool}) -> {SP.drop(~V, SC.append(SP.Ent<V>, a, b), key) == SC.append(SP.Ent<V>, a, SP.drop(~V, b, key)) : List<&2, SP.Ent<V>>}:
  match a:
    case Nil{}:
      {==}
    case Con{SP.LE{+k, +v, +t, +d}, +r}:
      drop_c(~V, k, v, t, d, r, b, key, S.str_eq(k, key), {==}, L.and_left(Bool.not(S.str_eq(k, key)), enk(~V, r, key), h), drop_app(~V, r, b, key, L.and_right(Bool.not(S.str_eq(k, key)), enk(~V, r, key), h)))
