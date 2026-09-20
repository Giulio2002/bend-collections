import Base
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./spec_lookup.bend as Lookup
import ./recency_unique.bend as Unique

def head(~K: Data, ~same: K -> K -> Bool, -V: Data, +entry: T.Entry<K, V>, +tail: List<&2, T.Entry<K, V>>, +key: K, matched: Bool, decision: {same(Lookup.key(K, V, entry))(key) == matched : Bool}, induction: {S.find(~K, ~same, V, tail, key) == None{} : Maybe<&2, T.Entry<K, V>>}) -> {S.find(~K, ~same, V, S.omit_entry(K, V, entry, tail, matched), key) == None{} : Maybe<&2, T.Entry<K, V>>}:
  T.Item{+original, value, deadline} = entry
  match matched:
    case True{}: induction
    case False{}:
      %Equal.sym(Bool, same(original)(key), False{}, decision) : {S.choose_entry(K, V, T.Item{original, value, deadline}, S.find(~K, ~same, V, tail, key), _) == None{} : Maybe<&2, T.Entry<K, V>>}
      induction

# Removing a key from the independent binding list eliminates its lookup even
# when that list contains duplicates; no representation conclusion is assumed.
def same_key(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, +key: K) -> {S.find(~K, ~same, V, S.erase(~K, ~same, V, bindings, key), key) == None{} : Maybe<&2, T.Entry<K, V>>}:
  match bindings:
    case Nil{}: {==}
    case Con{T.Item{+original, value, deadline}, +tail}:
      head(~K, ~same, V, T.Item{original, value, deadline}, S.erase(~K, ~same, V, tail, key), key, same(original)(key), {==}, same_key(~K, ~same, V, tail, key))

def string_same_key(-V: Data, bindings: List<&2, T.Entry<String, V>>, key: String) -> {S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, bindings, key), key) == None{} : Maybe<&2, T.Entry<String, V>>}:
  same_key(~String, ~Lookup.string_same, V, bindings, key)

def excludes(+head: String, +removed: String, +query: String, matched: {String.eq(head, removed) == True{} : Bool}, different: {String.eq(removed, query) == False{} : Bool}) -> {String.eq(head, query) == False{} : Bool}:
  Equal.trans(Bool, String.eq(head, query), String.eq(removed, query), False{}, Equal.cong(String, Bool, k => String.eq(k, query), head, removed, Unique.equal_boolean(head, removed, matched)), different)

def other_head(-V: Data, +original: String, value: V, deadline: T.Int64, +tail: List<&2, T.Entry<String, V>>, +removed: String, +query: String, matched: Bool, decision: {String.eq(original, removed) == matched : Bool}, different: {String.eq(removed, query) == False{} : Bool}, induction: {S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, tail, removed), query) == S.find(~String, ~Lookup.string_same, V, tail, query) : Maybe<&2, T.Entry<String, V>>}) -> {S.find(~String, ~Lookup.string_same, V, S.omit_entry(String, V, T.Item{original, value, deadline}, S.erase(~String, ~Lookup.string_same, V, tail, removed), matched), query) == S.find(~String, ~Lookup.string_same, V, Con{T.Item{original, value, deadline}, tail}, query) : Maybe<&2, T.Entry<String, V>>}:
  match matched:
    case False{}:
      Equal.cong(Maybe<&2, T.Entry<String, V>>, Maybe<&2, T.Entry<String, V>>, item => S.choose_entry(String, V, T.Item{original, value, deadline}, item, String.eq(original, query)), S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, tail, removed), query), S.find(~String, ~Lookup.string_same, V, tail, query), induction)
    case True{}:
      %Equal.sym(Bool, String.eq(original, query), False{}, excludes(original, removed, query, decision, different)) : {S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, tail, removed), query) == S.choose_entry(String, V, T.Item{original, value, deadline}, S.find(~String, ~Lookup.string_same, V, tail, query), _) : Maybe<&2, T.Entry<String, V>>}
      induction

def string_other_key(-V: Data, bindings: List<&2, T.Entry<String, V>>, +removed: String, +query: String, +different: {String.eq(removed, query) == False{} : Bool}) -> {S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, bindings, removed), query) == S.find(~String, ~Lookup.string_same, V, bindings, query) : Maybe<&2, T.Entry<String, V>>}:
  match bindings:
    case Nil{}: {==}
    case Con{T.Item{+original, value, deadline}, +tail}:
      other_head(V, original, value, deadline, tail, removed, query, String.eq(original, removed), {==}, different, string_other_key(V, tail, removed, query, different))
