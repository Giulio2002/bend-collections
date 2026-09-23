import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./map_routing.bend as Routing
import ./recency_unique.bend as Unique
import ./cache_order.bend as Order
import ./abstraction_recency.bend as Recency
import ./cache_storage_preservation.bend as Storage
import ./cache_oldest_available.bend as Oldest
import ./representation_access.bend as Access

# Native String caches under the representation invariant have no stray
# bindings: every stored binding's original key occurs in the recency list.

def list_keys(-V: Data, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>) -> List<&2, String>:
  match xs:
    case Nil{}: Nil{}
    case Con{Tuple{code, item}, rest}: Con{code, list_keys(V, rest)}

def keys_go(-V: Data, m: Map<&2, Maybe<&2, T.Entry<String, V>>>, +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>) -> {Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, m, list_keys(V, acc)) == list_keys(V, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, m, acc)) : List<&2, String>}:
  match m:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{pos, +lo, +hi}:
      %Equal.sym(List<&2, String>, Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, hi, list_keys(V, acc)), list_keys(V, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, hi, acc)), keys_go(V, hi, acc)) : {Map.keys.go(&2, Maybe<&2, T.Entry<String, V>>, lo, _) == list_keys(V, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, hi, acc))) : List<&2, String>}
      keys_go(V, lo, Map.to_list.go(&2, Maybe<&2, T.Entry<String, V>>, hi, acc))

def keys_to_list(-V: Data, m: Map<&2, Maybe<&2, T.Entry<String, V>>>) -> {Map.keys(&2, Maybe<&2, T.Entry<String, V>>, m) == list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, m)) : List<&2, String>}:
  keys_go(V, m, Nil{})

def member_string(xs: List<&2, String>, +q: String) -> {E.member(~String, ~Lookup.string_same, xs, q) == Inv.member(xs, q) : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}: Equal.cong(Bool, Bool, rest => Bool.or(String.eq(h, q), rest), E.member(~String, ~Lookup.string_same, t, q), Inv.member(t, q), member_string(t, q))

def stray_head(-V: Data, +order: List<&2, String>, +code: String, +k: String, +v: V, +d: T.Int64, +rest: List<&2, T.Entry<String, V>>, +same: {String.eq(code, k) == True{} : Bool}, bound: {Inv.member(order, code) == True{} : Bool}, ih: {E.stray(~String, ~Lookup.string_same, V, order, rest) == Nil{} : List<&2, T.Entry<String, V>>}) -> {E.keep_stray(String, V, T.Item{k, v, d}, E.stray(~String, ~Lookup.string_same, V, order, rest), E.member(~String, ~Lookup.string_same, order, k)) == Nil{} : List<&2, T.Entry<String, V>>}:
  member_k = Equal.trans(Bool, E.member(~String, ~Lookup.string_same, order, k), Inv.member(order, k), True{}, member_string(order, k), Equal.trans(Bool, Inv.member(order, k), Inv.member(order, code), True{}, Equal.cong(String, Bool, x => Inv.member(order, x), k, code, Equal.sym(String, code, k, Unique.equal_boolean(code, k, same))), bound))
  %Equal.sym(Bool, E.member(~String, ~Lookup.string_same, order, k), True{}, member_k) : {E.keep_stray(String, V, T.Item{k, v, d}, E.stray(~String, ~Lookup.string_same, V, order, rest), _) == Nil{} : List<&2, T.Entry<String, V>>}
  ih

def stray_list(-V: Data, +order: List<&2, String>, xs: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, T.Entry<String, V>>>>, +ident: {Inv.identities(~String, ~Codec.string_encode, V, xs) == True{} : Bool}, +incl: {Inv.included(list_keys(V, xs), order) == True{} : Bool}) -> {E.stray(~String, ~Lookup.string_same, V, order, F.bindings(String, V, xs)) == Nil{} : List<&2, T.Entry<String, V>>}:
  match xs:
    case Nil{}: {==}
    case Con{Tuple{+code, None{}}, +rest}: Empty.absurd({E.stray(~String, ~Lookup.string_same, V, order, F.bindings(String, V, rest)) == Nil{} : List<&2, T.Entry<String, V>>}, Routing.false_true(ident))
    case Con{Tuple{+code, Some{T.Item{+k, +v, +d}}}, +rest}:
      stray_head(V, order, code, k, v, d, F.bindings(String, V, rest), Routing.and_left(String.eq(code, k), Inv.identities(~String, ~Codec.string_encode, V, rest), ident), Routing.and_left(Inv.member(order, code), Inv.included(list_keys(V, rest), order), incl), stray_list(V, order, rest, Routing.and_right(String.eq(code, k), Inv.identities(~String, ~Codec.string_encode, V, rest), ident), Routing.and_right(Inv.member(order, code), Inv.included(list_keys(V, rest), order), incl)))

# A represented native cache, in its normal (native-order) abstraction.
def stray_normal(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}) == True{} : Bool}) -> {E.stray(~String, ~Lookup.string_same, V, order, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table))) == Nil{} : List<&2, T.Entry<String, V>>}:
  incl = Equal.trans(Bool, Inv.included(list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), order), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), order), True{}, Equal.cong(List<&2, String>, Bool, ks => Inv.included(ks, order), list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), Equal.sym(List<&2, String>, Map.keys(&2, Maybe<&2, T.Entry<String, V>>, table), list_keys(V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), keys_to_list(V, table))), Routing.and_right(Oldest.order_in_keys(String, V, C.State{cap, table, order, life, counts, cb}), Order.keys_in_order(String, V, C.State{cap, table, order, life, counts, cb}), Storage.membership(String, V, C.State{cap, table, order, life, counts, cb}, Access.get_storage(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, valid))))
  stray_list(V, order, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table), Access.get_identities(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, valid), incl)

# Relation by fields: equal scalars/recency, pointwise lookups at the recency
# keys, and no stray bindings on either side.
def by_fields(-V: Data, +cap: Nat, +o1: List<&2, String>, +o2: List<&2, String>, +l: T.Int64, +m: T.Metrics, +f: Bool, +b1: List<&2, T.Entry<String, V>>, +b2: List<&2, T.Entry<String, V>>, eo: {o1 == o2 : List<&2, String>}, looks: {E.lookups(~String, ~Lookup.string_same, V, o2, b1) == E.lookups(~String, ~Lookup.string_same, V, o2, b2) : List<&2, Maybe<&2, T.Entry<String, V>>>}, s1: {E.stray(~String, ~Lookup.string_same, V, o1, b1) == Nil{} : List<&2, T.Entry<String, V>>}, s2: {E.stray(~String, ~Lookup.string_same, V, o2, b2) == Nil{} : List<&2, T.Entry<String, V>>}) -> E.states(~String, ~Lookup.string_same, V, S.Abstract{cap, b1, o1, l, m, f}, S.Abstract{cap, b2, o2, l, m, f}):
  %Equal.sym(List<&2, T.Entry<String, V>>, E.stray(~String, ~Lookup.string_same, V, o1, b1), Nil{}, s1) : {E.Canon{cap, o1, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o1, b1), _} == E.Canon{cap, o2, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o2, b2), E.stray(~String, ~Lookup.string_same, V, o2, b2)} : E.Canonical<String, V>}
  %Equal.sym(List<&2, T.Entry<String, V>>, E.stray(~String, ~Lookup.string_same, V, o2, b2), Nil{}, s2) : {E.Canon{cap, o1, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o1, b1), Nil{}} == E.Canon{cap, o2, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o2, b2), _} : E.Canonical<String, V>}
  %looks : {E.Canon{cap, o1, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o1, b1), Nil{}} == E.Canon{cap, o2, l, m, f, _, Nil{}} : E.Canonical<String, V>}
  Equal.cong(List<&2, String>, E.Canonical<String, V>, o => E.Canon{cap, o, l, m, f, E.lookups(~String, ~Lookup.string_same, V, o, b1), Nil{}}, o1, o2, eo)
