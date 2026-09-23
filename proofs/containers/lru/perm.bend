import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../hash_table/spec.bend as S
import ./spec.bend as SP
import ../hash_table/state.bend as HT
import ../hash_table/insf.bend as IF
import ./state.bend as ST
import ./lists.bend as LS
import ./trace.bend as TR
import ./unlink.bend as UL
import ./rebuild.bend as RB
import ./touch.bend as TO
import ../../lib/nat_list.bend as NL

# The recency list a ++ [s] ++ b against (a ++ b) ++ [s]: same slots, same
# length, both duplicate-free, both with unique keys.


def sub_xt(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {IF.subl(SC.append(Nat, a, Con{s, b}), SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})) == True{} : Bool}:
  +sa = RB.subl_ml(a, SC.append(Nat, a, b), Con{s, Nil{}}, RB.subl_ml(a, a, b, RB.subl_refl(a)))
  +ssb = L.and_intro(NL.memn(s, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), IF.subl(b, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), NL.mem_app_r(s, SC.append(Nat, a, b), Con{s, Nil{}}, UL.self_in(s, Nil{})), RB.subl_ml(b, SC.append(Nat, a, b), Con{s, Nil{}}, RB.subl_mr(b, a, b, RB.subl_refl(b))))
  RB.subl_app(a, Con{s, b}, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}), sa, ssb)

def sub_tx(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {IF.subl(SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}), SC.append(Nat, a, Con{s, b})) == True{} : Bool}:
  +sab = RB.subl_app(a, b, SC.append(Nat, a, Con{s, b}), RB.subl_ml(a, a, Con{s, b}, RB.subl_refl(a)), RB.subl_mr(b, a, Con{s, b}, IF.subl_cons(b, b, s, RB.subl_refl(b))))
  RB.subl_app(SC.append(Nat, a, b), Con{s, Nil{}}, SC.append(Nat, a, Con{s, b}), sab, L.and_intro(NL.memn(s, SC.append(Nat, a, Con{s, b})), True{}, NL.mem_app_r(s, a, Con{s, b}, UL.self_in(s, b)), {==}))

def trin_sub(+tr: TR.Tr, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {TR.trin(tr, xs) == True{} : Bool}, +sub: {IF.subl(xs, ys) == True{} : Bool}) -> {TR.trin(tr, ys) == True{} : Bool}:
  match tr:
    case TR.TNil{}:
      {==}
    case TR.TW{+y, +o, +v, +t}:
      L.and_intro(NL.memn(y, ys), TR.trin(t, ys), IF.memn_sub(y, xs, ys, sub, L.and_left(NL.memn(y, xs), TR.trin(t, xs), h)), trin_sub(t, xs, ys, L.and_right(NL.memn(y, xs), TR.trin(t, xs), h), sub))

# x ++ [s]: duplicate-free when x is and s is not in it
def nd_snoc(+x: List<&2, Nat>, +s: Nat) -> {NL.nodupn(SC.append(Nat, x, Con{s, Nil{}})) == Bool.and(NL.nodupn(x), Bool.not(NL.memn(s, x))) : Bool}:
  +e = NL.nd_mid(x, s, Nil{})
  +an = LL.append_nil(Nat, x)
  L.subst(List<&2, Nat>, z => {NL.nodupn(SC.append(Nat, x, Con{s, Nil{}})) == Bool.and(NL.nodupn(z), Bool.not(NL.memn(s, z))) : Bool}, SC.append(Nat, x, Nil{}), x, an, e)

def nd_xt(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {NL.nodupn(SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})) == True{} : Bool}:
  Equal.trans(Bool, NL.nodupn(SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), Bool.and(NL.nodupn(SC.append(Nat, a, b)), Bool.not(NL.memn(s, SC.append(Nat, a, b)))), True{}, nd_snoc(SC.append(Nat, a, b), s), Equal.trans(Bool, Bool.and(NL.nodupn(SC.append(Nat, a, b)), Bool.not(NL.memn(s, SC.append(Nat, a, b)))), NL.nodupn(SC.append(Nat, a, Con{s, b})), True{}, Equal.sym(Bool, NL.nodupn(SC.append(Nat, a, Con{s, b})), Bool.and(NL.nodupn(SC.append(Nat, a, b)), Bool.not(NL.memn(s, SC.append(Nat, a, b)))), NL.nd_mid(a, s, b)), h))

def len_xt(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})) == SC.length(Nat, SC.append(Nat, a, Con{s, b})) : Nat}:
  +e1 = Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), Nat.add(SC.length(Nat, SC.append(Nat, a, b)), 1n), Nat.add(Nat.add(SC.length(Nat, a), SC.length(Nat, b)), 1n), LL.length_append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}), Equal.cong(Nat, Nat, z => Nat.add(z, 1n), SC.length(Nat, SC.append(Nat, a, b)), Nat.add(SC.length(Nat, a), SC.length(Nat, b)), LL.length_append(Nat, a, b)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(SC.length(Nat, a), SC.length(Nat, b)), 1n), Nat.add(SC.length(Nat, a), Nat.add(SC.length(Nat, b), 1n)), Nat.add(SC.length(Nat, a), 1n+SC.length(Nat, b)), N.add_assoc(SC.length(Nat, a), SC.length(Nat, b), 1n), Equal.cong(Nat, Nat, z => Nat.add(SC.length(Nat, a), z), Nat.add(SC.length(Nat, b), 1n), 1n+SC.length(Nat, b), Equal.trans(Nat, Nat.add(SC.length(Nat, b), 1n), 1n+Nat.add(SC.length(Nat, b), 0n), 1n+SC.length(Nat, b), N.add_succ(SC.length(Nat, b), 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(SC.length(Nat, b), 0n), SC.length(Nat, b), N.add_zero(SC.length(Nat, b))))))
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), Nat.add(SC.length(Nat, a), 1n+SC.length(Nat, b)), SC.length(Nat, SC.append(Nat, a, Con{s, b})), Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), Nat.add(Nat.add(SC.length(Nat, a), SC.length(Nat, b)), 1n), Nat.add(SC.length(Nat, a), 1n+SC.length(Nat, b)), e1, e2), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, Con{s, b})), Nat.add(SC.length(Nat, a), 1n+SC.length(Nat, b)), LL.length_append(Nat, a, Con{s, b})))

# ---- keys ----

def keys_x(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}) -> {SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b}))) == SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))}) : List<&2, String>}:
  +e1 = Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{TO.ev(~V, ll, kl, s, v), ST.es(~V, ll, kl, el, b)}), LS.es_app(~V, ll, kl, el, a, Con{s, b}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), z), ST.es(~V, ll, kl, el, Con{s, b}), Con{TO.ev(~V, ll, kl, s, v), ST.es(~V, ll, kl, el, b)}, TO.es_cons(~V, ll, kl, el, s, v, hm, b)))
  Equal.trans(List<&2, String>, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b}))), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{TO.ev(~V, ll, kl, s, v), ST.es(~V, ll, kl, el, b)})), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, String>, z => SP.keys_of(~V, z), ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), Con{TO.ev(~V, ll, kl, s, v), ST.es(~V, ll, kl, el, b)}), e1), LS.keys_app(~V, ST.es(~V, ll, kl, el, a), Con{TO.ev(~V, ll, kl, s, v), ST.es(~V, ll, kl, el, b)}))

def keys_t(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}) -> {SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}))) == SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}) : List<&2, String>}:
  +e1 = Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}}), LS.es_app(~V, ll, kl, el, SC.append(Nat, a, b), Con{s, Nil{}}), Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), ST.es(~V, ll, kl, el, Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, ll, kl, el, Con{s, Nil{}})), ST.es(~V, ll, kl, el, SC.append(Nat, a, b)), SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), LS.es_app(~V, ll, kl, el, a, b)), Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), z), ST.es(~V, ll, kl, el, Con{s, Nil{}}), Con{TO.ev(~V, ll, kl, s, v), Nil{}}, TO.es_cons(~V, ll, kl, el, s, v, hm, Nil{}))))
  +e2 = Equal.trans(List<&2, String>, SP.keys_of(~V, SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}})), SC.append(String, SP.keys_of(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}), SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}), LS.keys_app(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}}), Equal.cong(List<&2, String>, List<&2, String>, z => SC.append(String, z, Con{ST.skey(ll, kl, s), Nil{}}), SP.keys_of(~V, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b))), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), LS.keys_app(~V, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b))))
  Equal.trans(List<&2, String>, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}))), SP.keys_of(~V, SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}})), SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}), Equal.cong(List<&2, SP.Ent<V>>, List<&2, String>, z => SP.keys_of(~V, z), ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})), SC.append(SP.Ent<V>, SC.append(SP.Ent<V>, ST.es(~V, ll, kl, el, a), ST.es(~V, ll, kl, el, b)), Con{TO.ev(~V, ll, kl, s, v), Nil{}}), e1), e2)

def nd_snoc_s(+x: List<&2, String>, +k: String) -> {S.nodup(SC.append(String, x, Con{k, Nil{}})) == Bool.and(S.nodup(x), Bool.not(S.mem(k, x))) : Bool}:
  L.subst(List<&2, String>, z => {S.nodup(SC.append(String, x, Con{k, Nil{}})) == Bool.and(S.nodup(z), Bool.not(S.mem(k, z))) : Bool}, SC.append(String, x, Nil{}), x, LL.append_nil(String, x), LS.nd_mid_s(x, k, Nil{}))

def keys_xt(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +v: V, +hm: {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}, +h: {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b})))) == True{} : Bool}) -> {S.nodup(SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})))) == True{} : Bool}:
  +h1 = L.subst(List<&2, String>, z => {S.nodup(z) == True{} : Bool}, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, a, Con{s, b}))), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))}), keys_x(~V, ll, kl, el, a, s, b, v, hm), h)
  +h2 = Equal.trans(Bool, S.nodup(SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}})), Bool.and(S.nodup(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))), Bool.not(S.mem(ST.skey(ll, kl, s), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))))), True{}, nd_snoc_s(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), ST.skey(ll, kl, s)), Equal.trans(Bool, Bool.and(S.nodup(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))), Bool.not(S.mem(ST.skey(ll, kl, s), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))))), S.nodup(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))})), True{}, Equal.sym(Bool, S.nodup(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))})), Bool.and(S.nodup(SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))), Bool.not(S.mem(ST.skey(ll, kl, s), SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))))), LS.nd_mid_s(SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, b)))), h1))
  L.subst(List<&2, String>, z => {S.nodup(z) == True{} : Bool}, SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}), SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}))), Equal.sym(List<&2, String>, SP.keys_of(~V, ST.es(~V, ll, kl, el, SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}))), SC.append(String, SC.append(String, SP.keys_of(~V, ST.es(~V, ll, kl, el, a)), SP.keys_of(~V, ST.es(~V, ll, kl, el, b))), Con{ST.skey(ll, kl, s), Nil{}}), keys_t(~V, ll, kl, el, a, s, b, v, hm)), h2)
