import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./representation_access.bend as Access
import ./cache_storage_preservation.bend as Storage
import ./cache_oldest_available.bend as Oldest
import ./cache_order.bend as Order
import ./map_routing.bend as R
import ./cache_key_identity.bend as Identity
import ./store_state.bend as Store
import ./spec_lookup.bend as Lookup

def included(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> {Order.keys_in_order(String, V, c) == True{} : Bool}:
  R.and_right(Oldest.order_in_keys(String, V, c), Order.keys_in_order(String, V, c), Storage.membership(String, V, c, Access.get_storage(~String, ~Codec.string_encode, V, c, valid)))

# Replacement derives the internal store bound from existing membership and
# capacity laws. No additional resource/capacity premise reaches this branch.
def known(-V: Data, +c: C.Cache<String, V>, +key: String, +old: V, +oldexpiry: T.Int64, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, present: {C.lookup(String, V, c, key) == Some{T.Item{key, old, oldexpiry}} : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, Some{T.Item{key, old, oldexpiry}})), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, Some{T.Item{key, old, oldexpiry}})):
  Store.observation(V, c, key, value, deadline, False{}, Nil{}, valid, Order.replacement_bounded(String, V, c, key, key, old, oldexpiry, key, value, deadline, Access.get_bounded(~String, ~Codec.string_encode, V, c, valid), included(V, c, valid), present))

def branch(-V: Data, +c: C.Cache<String, V>, +key: String, +original: String, +old: V, +oldexpiry: T.Int64, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +present: {C.lookup(String, V, c, key) == Some{T.Item{original, old, oldexpiry}} : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, Some{T.Item{original, old, oldexpiry}})), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, Some{T.Item{original, old, oldexpiry}})):
  +same = Identity.lookup_code_identity(~String, ~Codec.string_encode, V, c, key, T.Item{original, old, oldexpiry}, Access.get_identities(~String, ~Codec.string_encode, V, c, valid), present)
  original_lookup = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, original), C.lookup(String, V, c, key), Some{T.Item{original, old, oldexpiry}}, Equal.cong(String, Maybe<&2, T.Entry<String, V>>, k => C.lookup(String, V, c, k), original, key, Equal.sym(String, key, original, same)), present)
  %Equal.sym(String, key, original, same) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.store(String, V, c, _, original, value, deadline, False{}, Nil{})), O.write(~String, ~Lookup.string_same, V, F.abstract(String, V, c), original, value, deadline, False{}, Nil{}))
  known(V, c, original, old, oldexpiry, value, deadline, valid, original_lookup)
