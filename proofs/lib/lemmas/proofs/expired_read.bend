import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./remove_refinement.bend as Remove
import ./extensional_states.bend as Ext

def miss_projection(-K: Data, -V: Data, step: C.Step<K, V>, tracked: Bool) -> {F.observe(K, V, C.miss_after_remove(K, V, step, tracked)) == O.expired_result(K, V, F.observe(K, V, step), tracked) : S.Observation<K, V>}:
  C.Out{C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, item, flag, events} = step
  match tracked:
    case False{}: {==}
    case True{}: {==}

# Expiration removes the entry and then counts a miss only for tracked reads.
# The old entry remains in the native observation with a false presence flag,
# which supports the facade's GetOldest original-key projection.
def branch(-V: Data, +c: C.Cache<String, V>, +key: String, entry: T.Entry<String, V>, +tracked: Bool, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_expiry(String, V, c, key, entry, tracked, True{})), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, True{})):
  %Equal.sym(S.Observation<String, V>, F.observe(String, V, C.miss_after_remove(String, V, C.remove_encoded(String, V, c, key, False{}), tracked)), O.expired_result(String, V, F.observe(String, V, C.remove_encoded(String, V, c, key, False{})), tracked), miss_projection(String, V, C.remove_encoded(String, V, c, key, False{}), tracked)) : E.observations(~String, ~Lookup.string_same, V, _, O.expired_result(String, V, S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), tracked))
  Ext.string_expired_result(V, F.observe(String, V, C.remove_encoded(String, V, c, key, False{})), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), tracked, Remove.operation(V, c, key, valid, disabled))
