import Base
import ../src/codec.bend as Codec
import ./cache_populated.bend as CachePop
import ./cache_oldest_available.bend as Oldest
import ../src/cache.bend as C
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./abstraction_identity.bend as Identity
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./map_populated.bend as Pop
import ./map_key_lookup.bend as M
import ./map_insert.bend as I
import ./map_lookup.bend as L
import ./map_routing.bend as R

# Encode the original keys of an entry sequence, retaining its exact order.
def codes(~K: Data, ~encode: K -> String, -V: Data, entries: List<&2, T.Entry<K, V>>) -> List<&2, String>:
  match entries:
    case Nil{}: Nil{}
    case Con{entry, tail}: Con{Identity.entry_code(~K, ~encode, V, entry), codes(~K, ~encode, V, tail)}

def head_step(~K: Data, ~encode: K -> String, -V: Data, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +code: String, +tail: List<&2, String>, identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, induction: {codes(~K, ~encode, V, C.entries_go(K, V, tail, table)) == tail : List<&2, String>}, w: Sigma<&2, &1, T.Entry<K, V>, entry => {I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}>) -> {codes(~K, ~encode, V, C.entries_go(K, V, Con{code, tail}, table)) == Con{code, tail} : List<&2, String>}:
  (+entry, +found) = w
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), F.lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code))) : {codes(~K, ~encode, V, C.collect_entry(K, V, _, C.entries_go(K, V, tail, table))) == Con{code, tail} : List<&2, String>}
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), Some{entry}, found) : {codes(~K, ~encode, V, C.collect_entry(K, V, _, C.entries_go(K, V, tail, table))) == Con{code, tail} : List<&2, String>}
  %Identity.listed_identity(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table), code, entry, identities, L.returned_value_enumerated(T.Entry<K, V>, table, code, entry, found)) : {Con{_, codes(~K, ~encode, V, C.entries_go(K, V, tail, table))} == Con{code, tail} : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, xs => Con{code, xs}, codes(~K, ~encode, V, C.entries_go(K, V, tail, table)), tail, induction)

# Exact sequence equality, not just length or membership. Native key inclusion
# supplies every lookup; identity supplies each original-key encoding.
def entries_go_faithful(~K: Data, ~encode: K -> String, -V: Data, order: List<&2, String>, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>, +valid: {Inv.critbit(Maybe<&2, T.Entry<K, V>>, table) == True{} : Bool}, +populated: {Pop.populated(T.Entry<K, V>, table) == True{} : Bool}, +identities: {Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}, +included: {Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)) == True{} : Bool}) -> {codes(~K, ~encode, V, C.entries_go(K, V, order, table)) == order : List<&2, String>}:
  match order:
    case Nil{}: {==}
    case Con{+code, +tail}:
      head_step(~K, ~encode, V, table, code, tail, identities,
        entries_go_faithful(~K, ~encode, V, tail, table, valid, populated, identities, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code), Inv.included(tail, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), included)),
        M.key_lookup(T.Entry<K, V>, table, code, valid, populated, R.and_left(Inv.member(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), code), Inv.included(tail, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), included)))

def encode_keys(~K: Data, ~encode: K -> String, keys: List<&2, K>) -> List<&2, String>:
  match keys:
    case Nil{}: Nil{}
    case Con{key, rest}: Con{encode(key), encode_keys(~K, ~encode, rest)}

def keys_of_codes(~K: Data, ~encode: K -> String, -V: Data, entries: List<&2, T.Entry<K, V>>) -> {encode_keys(~K, ~encode, F.keys_of(K, V, entries)) == codes(~K, ~encode, V, entries) : List<&2, String>}:
  match entries:
    case Nil{}: {==}
    case Con{T.Item{+key, value, deadline}, +rest}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => Con{encode(key), xs}, encode_keys(~K, ~encode, F.keys_of(K, V, rest)), codes(~K, ~encode, V, rest), keys_of_codes(~K, ~encode, V, rest))

def model_order(-K: Data, -V: Data, s: S.Model<K, V>) -> List<&2, K>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  order

def native_order(-K: Data, -V: Data, c: C.Cache<K, V>) -> List<&2, String>:
  C.State{cap, table, order, life, counts, cb} = c
  order

def cache_identities(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Inv.identities(~K, ~encode, V, Map.to_list(&2, Maybe<&2, T.Entry<K, V>>, table))

def faithful(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, valid: {F.storage_critbit(K, V, c) == True{} : Bool}, populated: {CachePop.storage_populated(K, V, c) == True{} : Bool}, identities: {cache_identities(~K, ~encode, V, c) == True{} : Bool}, included: {Oldest.order_in_keys(K, V, c) == True{} : Bool}) -> {encode_keys(~K, ~encode, model_order(K, V, F.abstract(K, V, c))) == native_order(K, V, c) : List<&2, String>}:
  C.State{cap, +table, +order, life, counts, cb} = c
  Equal.trans(List<&2, String>, encode_keys(~K, ~encode, F.keys_of(K, V, C.entries_go(K, V, order, table))), codes(~K, ~encode, V, C.entries_go(K, V, order, table)), order, keys_of_codes(~K, ~encode, V, C.entries_go(K, V, order, table)), entries_go_faithful(~K, ~encode, V, order, table, valid, populated, identities, included))

law string_recency_faithful:
  for -V: Data
  for c: C.Cache<String, V>
  for valid: {F.storage_critbit(String, V, c) == True{} : Bool}
  for populated: {CachePop.storage_populated(String, V, c) == True{} : Bool}
  for identities: {cache_identities(~String, ~Codec.string_encode, V, c) == True{} : Bool}
  for included: {Oldest.order_in_keys(String, V, c) == True{} : Bool}
  {encode_keys(~String, ~Codec.string_encode, model_order(String, V, F.abstract(String, V, c))) == native_order(String, V, c) : List<&2, String>}
def string_recency_faithful(V, c, valid, populated, identities, included):
  faithful(~String, ~Codec.string_encode, V, c, valid, populated, identities, included)

law integer_recency_faithful:
  for -V: Data
  for c: C.Cache<T.Integer, V>
  for valid: {F.storage_critbit(T.Integer, V, c) == True{} : Bool}
  for populated: {CachePop.storage_populated(T.Integer, V, c) == True{} : Bool}
  for identities: {cache_identities(~T.Integer, ~Codec.integer_encode, V, c) == True{} : Bool}
  for included: {Oldest.order_in_keys(T.Integer, V, c) == True{} : Bool}
  {encode_keys(~T.Integer, ~Codec.integer_encode, model_order(T.Integer, V, F.abstract(T.Integer, V, c))) == native_order(T.Integer, V, c) : List<&2, String>}
def integer_recency_faithful(V, c, valid, populated, identities, included):
  faithful(~T.Integer, ~Codec.integer_encode, V, c, valid, populated, identities, included)
