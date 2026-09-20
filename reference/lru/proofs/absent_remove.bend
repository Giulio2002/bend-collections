import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./abstraction_bindings.bend as B
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup

def model_dispatch(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, missing: {S.find(~K, ~same, V, B.model_bindings(K, V, s), key) == None{} : Maybe<&2, T.Entry<K, V>>}) -> {S.remove(~K, ~same, V, s, key) == S.missing_remove(K, V, s) : S.Observation<K, V>}:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Equal.cong(Maybe<&2, T.Entry<K, V>>, S.Observation<K, V>, found => S.remove_decision(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, found), S.find(~K, ~same, V, bindings, key), None{}, missing)

# Removing an absent key preserves the whole state and every metric, including
# in nonempty represented caches. No success flag or eviction event is invented.
def string_remove(-V: Data, +c: C.Cache<String, V>, +key: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +missing: {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key) == None{} : Maybe<&2, T.Entry<String, V>>}) -> {F.observe(String, V, C.remove(String, V, Codec.string_encode, c, key)) == S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key) : S.Observation<String, V>}:
  native = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), None{}, L.string_lookup(V, c, key, valid), missing)
  Equal.trans(S.Observation<String, V>, F.observe(String, V, C.remove(String, V, Codec.string_encode, c, key)), S.missing_remove(String, V, F.abstract(String, V, c)), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), Equal.cong(Maybe<&2, T.Entry<String, V>>, S.Observation<String, V>, found => F.observe(String, V, C.remove_found(String, V, c, key, False{}, found)), C.lookup(String, V, c, key), None{}, native), Equal.sym(S.Observation<String, V>, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), S.missing_remove(String, V, F.abstract(String, V, c)), model_dispatch(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, missing)))
