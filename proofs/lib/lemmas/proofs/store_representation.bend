import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./representation_access.bend as Access
import ./refresh_complete_representation.bend as Joint
import ./cache_storage_preservation.bend as Storage
import ./cache_store_identities.bend as Identity
import ./recency_unique.bend as Unique
import ./capacity_preservation.bend as Capacity

# Internal composition lemma. Add discharges the output bound below; it is not
# exposed as an assumed public-operation correctness premise.
def store(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, +flag: Bool, +events: List<&2, T.LruEvent<K, V>>, +invariant: {Inv.representation(~K, ~encode, V, c) == True{} : Bool}, fresh: {code == encode(key) : String}, bounded: {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), C.capacity(K, V, c)) == True{} : Bool}) -> {Inv.representation(~K, ~encode, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}:
  +same_capacity = Capacity.store(K, V, c, code, key, value, deadline, flag, events)
  Joint.assemble(~K, ~encode, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)),
    %Equal.sym(Nat, C.capacity(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), C.capacity(K, V, c), same_capacity) : {Nat.is_gt(_, 0n) == True{} : Bool} Access.get_positive(~K, ~encode, V, c, invariant),
    %Equal.sym(Nat, C.capacity(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), C.capacity(K, V, c), same_capacity) : {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), _) == True{} : Bool} bounded,
    Unique.store_preserves_unique_recency(K, V, c, code, key, value, deadline, flag, events, Access.get_unique(~K, ~encode, V, c, invariant)),
    Storage.store(K, V, c, code, key, value, deadline, flag, events, Access.get_storage(~K, ~encode, V, c, invariant)),
    Identity.store(~K, ~encode, V, c, code, key, value, deadline, flag, events, fresh, Storage.valid(K, V, c, Access.get_storage(~K, ~encode, V, c, invariant)), Access.get_identities(~K, ~encode, V, c, invariant)))
