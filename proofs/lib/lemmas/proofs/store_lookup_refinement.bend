import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup
import ./spec_write_lookup.bend as Write
import ./abstraction_bindings.bend as B
import ./removal_lookup.bend as Storage
import ./recency_unique.bend as Unique

def target(-V: Data, s: S.Model<String, V>, key: String, value: V, deadline: T.Int64, flag: Bool, events: List<&2, T.LruEvent<String, V>>, query: String) -> Maybe<&2, T.Entry<String, V>>:
  S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, O.observed_state(String, V, O.write(~String, ~Lookup.string_same, V, s, key, value, deadline, flag, events))), query)

def same(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<String, V>>) -> {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), key) == target(V, F.abstract(String, V, c), key, value, deadline, flag, events, key) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), key), Some{T.Item{key, value, deadline}}, target(V, F.abstract(String, V, c), key, value, deadline, flag, events, key), F.store_lookup(String, V, c, key, key, value, deadline, flag, events), Equal.sym(Maybe<&2, T.Entry<String, V>>, target(V, F.abstract(String, V, c), key, value, deadline, flag, events, key), Some{T.Item{key, value, deadline}}, Write.same(V, F.abstract(String, V, c), key, value, deadline, flag, events)))

def other(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<String, V>>, +query: String, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +different: {String.eq(key, query) == False{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), query) == target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), query), C.lookup(String, V, c, query), target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query), F.store_other_lookup(String, V, c, key, key, value, deadline, flag, events, query, Write.reverse_false(key, query, different), Storage.valid_storage(V, c, valid)), Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), query), target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query), L.string_lookup(V, c, query, valid), Equal.sym(Maybe<&2, T.Entry<String, V>>, target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), query), Write.other(V, F.abstract(String, V, c), key, value, deadline, flag, events, query, different))))

def decide(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<String, V>>, +query: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, equal: Bool, decision: {String.eq(key, query) == equal : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), query) == target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query) : Maybe<&2, T.Entry<String, V>>}:
  match equal:
    case False{}: other(V, c, key, value, deadline, flag, events, query, valid, decision)
    case True{}:
      %Unique.equal_boolean(key, query, decision) : {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), _) == target(V, F.abstract(String, V, c), key, value, deadline, flag, events, _) : Maybe<&2, T.Entry<String, V>>}
      same(V, c, key, value, deadline, flag, events)

def correspondence(-V: Data, c: C.Cache<String, V>, +key: String, value: V, deadline: T.Int64, flag: Bool, events: List<&2, T.LruEvent<String, V>>, +query: String, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.store(String, V, c, key, key, value, deadline, flag, events)), query) == target(V, F.abstract(String, V, c), key, value, deadline, flag, events, query) : Maybe<&2, T.Entry<String, V>>}:
  decide(V, c, key, value, deadline, flag, events, query, valid, String.eq(key, query), {==})
