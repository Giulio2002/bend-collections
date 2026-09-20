import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./representation_access.bend as Access
import ./cache_populated.bend as Pop
import ./cache_delete_membership.bend as Membership
import ./map_routing.bend as R
import ./map_delete_membership.bend as Delete
import ./recency_unique.bend as Unique
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup
import ./spec_erase_lookup.bend as Erase
import ./abstraction_bindings.bend as B

def valid_storage(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {F.storage_critbit(String, V, c) == True{} : Bool}:
  R.and_left(F.storage_critbit(String, V, c), Pop.storage_populated(String, V, c) && Membership.membership(String, V, c), Access.get_storage(~String, ~Codec.string_encode, V, c, valid))

def same(-V: Data, +c: C.Cache<String, V>, +key: String, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry)), key) == None{} : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  F.removed_key_absent(String, V, cap, table, order, life, counts, cb, key, False{}, entry, valid_storage(V, C.State{cap, table, order, life, counts, cb}, valid))

def other(-V: Data, +c: C.Cache<String, V>, +removed: String, +query: String, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, different: {String.eq(removed, query) == False{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), query) == C.lookup(String, V, c, query) : Maybe<&2, T.Entry<String, V>>}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  F.removal_preserves_other_lookup(String, V, C.State{cap, table, order, life, counts, cb}, removed, query, False{}, entry, R.critbit_certificate(Maybe<&2, T.Entry<String, V>>, table, valid_storage(V, C.State{cap, table, order, life, counts, cb}, valid)), eq => Delete.distinct(removed, query, different, Equal.sym(String, query, removed, eq)))

def other_spec(-V: Data, +c: C.Cache<String, V>, +removed: String, +query: String, entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +different: {String.eq(removed, query) == False{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), query) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), query), C.lookup(String, V, c, query), S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query), other(V, c, removed, query, entry, valid, different), Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), query), S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query), L.string_lookup(V, c, query, valid), Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), query), Erase.string_other_key(V, B.model_bindings(String, V, F.abstract(String, V, c)), removed, query, different))))

def same_spec(-V: Data, +c: C.Cache<String, V>, +key: String, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry)), key) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), key) : Maybe<&2, T.Entry<String, V>>}:
  Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, False{}, entry)), key), None{}, S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), key), same(V, c, key, entry, valid), Equal.sym(Maybe<&2, T.Entry<String, V>>, S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), key), None{}, Erase.string_same_key(V, B.model_bindings(String, V, F.abstract(String, V, c)), key)))

def decide(-V: Data, +c: C.Cache<String, V>, +removed: String, +query: String, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, equal: Bool, decision: {String.eq(removed, query) == equal : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), query) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query) : Maybe<&2, T.Entry<String, V>>}:
  match equal:
    case False{}: other_spec(V, c, removed, query, entry, valid, decision)
    case True{}:
      %Unique.equal_boolean(removed, query, decision) : {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), _) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), _) : Maybe<&2, T.Entry<String, V>>}
      same_spec(V, c, removed, entry, valid)

# Pointwise agreement with independently specified deletion, for every query.
# This is a storage observation, not yet the complete public Remove theorem.
def correspondence(-V: Data, c: C.Cache<String, V>, +removed: String, +query: String, entry: T.Entry<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {C.lookup(String, V, C.step_cache(String, V, C.remove_present(String, V, c, removed, False{}, entry)), query) == S.find(~String, ~Lookup.string_same, V, S.erase(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), removed), query) : Maybe<&2, T.Entry<String, V>>}:
  decide(V, c, removed, query, entry, valid, String.eq(removed, query), {==})
