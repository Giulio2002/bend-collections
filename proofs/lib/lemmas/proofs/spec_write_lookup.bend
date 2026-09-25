import Base
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../types/model.bend as T
import ./spec_lookup.bend as Lookup
import ./lookup_refinement.bend as L
import ./spec_erase_lookup.bend as Erase
import ./abstraction_bindings.bend as B
import ./map_delete_membership.bend as Delete
import ./recency_unique.bend as Unique

def reverse_false_case(+a: String, +b: String, unequal: {String.eq(a, b) == False{} : Bool}, result: Bool, checked: {String.eq(b, a) == result : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  match result:
    case False{}: checked
    case True{}: Empty.absurd({String.eq(b, a) == False{} : Bool}, Delete.distinct(a, b, unequal, Equal.sym(String, b, a, Unique.equal_boolean(b, a, checked))))

def reverse_false(+a: String, +b: String, unequal: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  reverse_false_case(a, b, unequal, String.eq(b, a), {==})

def same(-V: Data, s: S.Model<String, V>, +key: String, value: V, deadline: T.Int64, flag: Bool, events: List<&2, T.LruEvent<String, V>>) -> {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, O.observed_state(String, V, O.write(~String, ~Lookup.string_same, V, s, key, value, deadline, flag, events))), key) == Some{T.Item{key, value, deadline}} : Maybe<&2, T.Entry<String, V>>}:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  %Equal.sym(Bool, String.eq(key, key), True{}, L.string_reflexive(key)) : {S.choose_entry(String, V, T.Item{key, value, deadline}, S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, bindings, key), key), _) == Some{T.Item{key, value, deadline}} : Maybe<&2, T.Entry<String, V>>}
  {==}

def other(-V: Data, s: S.Model<String, V>, +key: String, value: V, deadline: T.Int64, flag: Bool, events: List<&2, T.LruEvent<String, V>>, +query: String, +different: {String.eq(key, query) == False{} : Bool}) -> {S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, O.observed_state(String, V, O.write(~String, ~Lookup.string_same, V, s, key, value, deadline, flag, events))), query) == S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, s), query) : Maybe<&2, T.Entry<String, V>>}:
  S.Abstract{cap, +bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  %Equal.sym(Bool, String.eq(key, query), False{}, different) : {S.choose_entry(String, V, T.Item{key, value, deadline}, S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, bindings, key), query), _) == S.find(~String, ~Lookup.string_same, V, bindings, query) : Maybe<&2, T.Entry<String, V>>}
  Erase.string_other_key(V, bindings, key, query, different)
