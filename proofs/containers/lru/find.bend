import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../hash_table/spec.bend as S
import ./spec.bend as SP
import ../../../src/math/u64.bend as W
import ../hash_table/keys.bend as K
import ../hash_table/words.bend as WR
import ../hash_table/state.bend as HT
import ./state.bend as ST
import ../../lib/nat_list.bend as NL

# The model's entries along the recency list: find, membership of keys.


# slot s's entry as find returns it (m is its value cell)
def fnd(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s: Nat, m: Maybe<&2, V>) -> Maybe<&2, SP.Ent<V>>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}}

def or_r(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(a, z) == True{} : Bool}, True{}, b, Equal.sym(Bool, b, True{}, h), WR.or_true(a))

# ---- membership of keys ----

def mk_here(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +m: Maybe<&2, V>, +hm: {HT.some_b(~V, m) == True{} : Bool}, +r: List<&2, SP.Ent<V>>) -> {S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), r))) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, None{}), r))) == True{} : Bool}, L.false_true(hm))
    case Some{v}:
      L.subst(Bool, z => {Bool.or(z, S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, r))) == True{} : Bool}, True{}, S.str_eq(ST.skey(ll, kl, s), ST.skey(ll, kl, s)), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s), ST.skey(ll, kl, s)), True{}, K.str_refl(ST.skey(ll, kl, s))), {==})

def mk_there(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +x: String, +s0: Nat, +m: Maybe<&2, V>, +r: List<&2, SP.Ent<V>>, +h: {S.mem(x, SP.keys_of(~V, r)) == True{} : Bool}) -> {S.mem(x, SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s0, m), r))) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{v}:
      L.subst(Bool, z => {Bool.or(S.str_eq(ST.skey(ll, kl, s0), x), z) == True{} : Bool}, True{}, S.mem(x, SP.keys_of(~V, r)), Equal.sym(Bool, S.mem(x, SP.keys_of(~V, r)), True{}, h), WR.or_true(S.str_eq(ST.skey(ll, kl, s0), x)))

def mk_c(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +s0: Nat, +t: List<&2, Nat>, +hl: {ST.live(~V, el, s) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(s0, s) == c : Bool}, +hm: {Bool.or(c, NL.memn(s, t)) == True{} : Bool}, rec: @h: {NL.memn(s, t) == True{} : Bool} -> {S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, t))) == True{} : Bool}) -> {S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s0, t}))) == True{} : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(s0, s, hc)
      L.subst(Nat, z => {S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, z, HT.nthm(~V, el, z)), ST.es(~V, ll, kl, el, t)))) == True{} : Bool}, s, s0, Equal.sym(Nat, s0, s, e), mk_here(~V, ll, kl, s, HT.nthm(~V, el, s), hl, ST.es(~V, ll, kl, el, t)))
    case False{}:
      mk_there(~V, ll, kl, ST.skey(ll, kl, s), s0, HT.nthm(~V, el, s0), ST.es(~V, ll, kl, el, t), rec(hm))

# a live slot on the list has its key among the model's keys
def mem_keys(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +hl: {ST.live(~V, el, s) == True{} : Bool}, +sl: List<&2, Nat>, +hm: {NL.memn(s, sl) == True{} : Bool}) -> {S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, sl))) == True{} : Bool}:
  match sl:
    case Nil{}:
      Empty.absurd({S.mem(ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, Nil{}))) == True{} : Bool}, L.false_true(hm))
    case Con{+s0, +t}:
      mk_c(~V, ll, kl, el, s, s0, t, hl, Nat.is_eq(s0, s), {==}, hm, h => mem_keys(~V, ll, kl, el, s, hl, t, h))

# ---- find ----

def not_true_f(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  K.not_true_eq(b, h)

# an entry whose key is not key is skipped
def find_skip(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s0: Nat, +m: Maybe<&2, V>, +r: List<&2, SP.Ent<V>>, +key: String, +hk: {Bool.or(Bool.not(HT.some_b(~V, m)), Bool.not(S.str_eq(ST.skey(ll, kl, s0), key))) == True{} : Bool}) -> {SP.find(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s0, m), r), key) == SP.find(~V, r, key) : Maybe<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      +ef = not_true_f(S.str_eq(ST.skey(ll, kl, s0), key), hk)
      L.subst(Bool, z => {Bool.pick(Maybe<&2, SP.Ent<V>>, z, Some{SP.LE{ST.skey(ll, kl, s0), v, ST.lw(ll, s0, 3n), W.U64{ST.lw(ll, s0, 4n), ST.lw(ll, s0, 5n)}}}, SP.find(~V, r, key)) == SP.find(~V, r, key) : Maybe<&2, SP.Ent<V>>}, False{}, S.str_eq(ST.skey(ll, kl, s0), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s0), key), False{}, ef), {==})

# the entry holding key is found
def find_here(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +m: Maybe<&2, V>, +hm: {HT.some_b(~V, m) == True{} : Bool}, +r: List<&2, SP.Ent<V>>, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}) -> {SP.find(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), r), key) == fnd(~V, ll, kl, s, m) : Maybe<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      Empty.absurd({SP.find(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, None{}), r), key) == fnd(~V, ll, kl, s, None{}) : Maybe<&2, SP.Ent<V>>}, L.false_true(hm))
    case Some{v}:
      L.subst(Bool, z => {Bool.pick(Maybe<&2, SP.Ent<V>>, z, Some{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}}, SP.find(~V, r, key)) == Some{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}} : Maybe<&2, SP.Ent<V>>}, True{}, S.str_eq(ST.skey(ll, kl, s), key), Equal.sym(Bool, S.str_eq(ST.skey(ll, kl, s), key), True{}, hk), {==})

# the key of an earlier slot differs (keys are unique), and the rest of the
# keys are unique
def split_d(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +hl: {ST.live(~V, el, s) == True{} : Bool}, +t: List<&2, Nat>, +hmt: {NL.memn(s, t) == True{} : Bool}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +s0: Nat, +d: Bool, +hd: {S.str_eq(ST.skey(ll, kl, s0), key) == d : Bool}, +hn: {Bool.not(S.mem(ST.skey(ll, kl, s0), SP.keys_of(~V, ST.es(~V, ll, kl, el, t)))) == True{} : Bool}) -> {Bool.not(d) == True{} : Bool}:
  match d:
    case False{}:
      {==}
    case True{}:
      +e0 = K.str_eq_of(ST.skey(ll, kl, s0), key, hd)
      +e1 = K.str_eq_of(ST.skey(ll, kl, s), key, hk)
      +e = Equal.trans(String, ST.skey(ll, kl, s), key, ST.skey(ll, kl, s0), e1, Equal.sym(String, ST.skey(ll, kl, s0), key, e0))
      +hin = L.subst(String, z => {S.mem(z, SP.keys_of(~V, ST.es(~V, ll, kl, el, t))) == True{} : Bool}, ST.skey(ll, kl, s), ST.skey(ll, kl, s0), e, mem_keys(~V, ll, kl, el, s, hl, t, hmt))
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, L.false_true(L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, S.mem(ST.skey(ll, kl, s0), SP.keys_of(~V, ST.es(~V, ll, kl, el, t))), True{}, hin, hn)))

def split_m1(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +hl: {ST.live(~V, el, s) == True{} : Bool}, +t: List<&2, Nat>, +hmt: {NL.memn(s, t) == True{} : Bool}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +s0: Nat, +m: Maybe<&2, V>, +hnd: {S.nodup(SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s0, m), ST.es(~V, ll, kl, el, t)))) == True{} : Bool}) -> {Bool.or(Bool.not(HT.some_b(~V, m)), Bool.not(S.str_eq(ST.skey(ll, kl, s0), key))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      +hn = L.and_left(Bool.not(S.mem(ST.skey(ll, kl, s0), SP.keys_of(~V, ST.es(~V, ll, kl, el, t)))), S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, t))), hnd)
      split_d(~V, ll, kl, el, s, hl, t, hmt, key, hk, s0, S.str_eq(ST.skey(ll, kl, s0), key), {==}, hn)

# the keys after an entry are unique
def nd_tail(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +t: List<&2, Nat>, +s0: Nat, +m: Maybe<&2, V>, +hnd: {S.nodup(SP.keys_of(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s0, m), ST.es(~V, ll, kl, el, t)))) == True{} : Bool}) -> {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, t))) == True{} : Bool}:
  match m:
    case None{}:
      hnd
    case Some{v}:
      L.and_right(Bool.not(S.mem(ST.skey(ll, kl, s0), SP.keys_of(~V, ST.es(~V, ll, kl, el, t)))), S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, t))), hnd)

def fh_c(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +hl: {ST.live(~V, el, s) == True{} : Bool}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +s0: Nat, +t: List<&2, Nat>, +hnd: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s0, t}))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(s0, s) == c : Bool}, +hm: {Bool.or(c, NL.memn(s, t)) == True{} : Bool}, rec: @h: {NL.memn(s, t) == True{} : Bool} -> @hn: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, t))) == True{} : Bool} -> {SP.find(~V, ST.es(~V, ll, kl, el, t), key) == fnd(~V, ll, kl, s, HT.nthm(~V, el, s)) : Maybe<&2, SP.Ent<V>>}) -> {SP.find(~V, ST.es(~V, ll, kl, el, Con{s0, t}), key) == fnd(~V, ll, kl, s, HT.nthm(~V, el, s)) : Maybe<&2, SP.Ent<V>>}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(s0, s, hc)
      L.subst(Nat, z => {SP.find(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, z, HT.nthm(~V, el, z)), ST.es(~V, ll, kl, el, t)), key) == fnd(~V, ll, kl, s, HT.nthm(~V, el, s)) : Maybe<&2, SP.Ent<V>>}, s, s0, Equal.sym(Nat, s0, s, e), find_here(~V, ll, kl, s, HT.nthm(~V, el, s), hl, ST.es(~V, ll, kl, el, t), key, hk))
    case False{}:
      Equal.trans(Maybe<&2, SP.Ent<V>>, SP.find(~V, ST.es(~V, ll, kl, el, Con{s0, t}), key), SP.find(~V, ST.es(~V, ll, kl, el, t), key), fnd(~V, ll, kl, s, HT.nthm(~V, el, s)), find_skip(~V, ll, kl, s0, HT.nthm(~V, el, s0), ST.es(~V, ll, kl, el, t), key, split_m1(~V, ll, kl, el, s, hl, t, hm, key, hk, s0, HT.nthm(~V, el, s0), hnd)), rec(hm, nd_tail(~V, ll, kl, el, t, s0, HT.nthm(~V, el, s0), hnd)))

# THEOREM (model side): a live listed slot holding key is what find returns
def find_hit(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +hl: {ST.live(~V, el, s) == True{} : Bool}, +key: String, +hk: {S.str_eq(ST.skey(ll, kl, s), key) == True{} : Bool}, +sl: List<&2, Nat>, +hm: {NL.memn(s, sl) == True{} : Bool}, +hnd: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, sl))) == True{} : Bool}) -> {SP.find(~V, ST.es(~V, ll, kl, el, sl), key) == fnd(~V, ll, kl, s, HT.nthm(~V, el, s)) : Maybe<&2, SP.Ent<V>>}:
  match sl:
    case Nil{}:
      Empty.absurd({SP.find(~V, ST.es(~V, ll, kl, el, Nil{}), key) == fnd(~V, ll, kl, s, HT.nthm(~V, el, s)) : Maybe<&2, SP.Ent<V>>}, L.false_true(hm))
    case Con{+s0, +t}:
      fh_c(~V, ll, kl, el, s, hl, key, hk, s0, t, hnd, Nat.is_eq(s0, s), {==}, hm, h => hn => find_hit(~V, ll, kl, el, s, hl, key, hk, t, h, hn))

# no listed slot holds key: find returns nothing
def find_miss(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +key: String, +sl: List<&2, Nat>, +h: {ST.nokey(~V, ll, kl, sl, key) == True{} : Bool}) -> {SP.find(~V, ST.es(~V, ll, kl, el, sl), key) == None{} : Maybe<&2, SP.Ent<V>>}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s0, +t}:
      +h0 = L.and_left(Bool.not(S.str_eq(ST.skey(ll, kl, s0), key)), ST.nokey(~V, ll, kl, t, key), h)
      Equal.trans(Maybe<&2, SP.Ent<V>>, SP.find(~V, ST.es(~V, ll, kl, el, Con{s0, t}), key), SP.find(~V, ST.es(~V, ll, kl, el, t), key), None{}, find_skip(~V, ll, kl, s0, HT.nthm(~V, el, s0), ST.es(~V, ll, kl, el, t), key, or_r(Bool.not(HT.some_b(~V, HT.nthm(~V, el, s0))), Bool.not(S.str_eq(ST.skey(ll, kl, s0), key)), h0)), find_miss(~V, ll, kl, el, key, t, L.and_right(Bool.not(S.str_eq(ST.skey(ll, kl, s0), key)), ST.nokey(~V, ll, kl, t, key), h)))
