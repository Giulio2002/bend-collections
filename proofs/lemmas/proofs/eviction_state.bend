import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./spec_lookup.bend as Lookup
import ./removal_state.bend as Removal
import ./removal_representation.bend as Rep
import ./string_order.bend as Order
import ./canonical_native.bend as Native
import ./canonical_string.bend as CS

def normalized(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry))), O.evicted_state(~String, ~Lookup.string_same, V, Order.normal(V, c), key)):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  Native.by_fields(V, cap, C.without(order, key), S.unlist(~String, ~Lookup.string_same, order, key), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, key))), S.erase(~String, ~Lookup.string_same, V, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), key), Order.filter(order, key), Removal.lookups_removed(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, entry, valid, S.unlist(~String, ~Lookup.string_same, order, key)), Native.stray_normal(V, cap, Map.del(&2, Maybe<&2, T.Entry<String, V>>, table, key), C.without(order, key), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb, Rep.remove_present(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, key, True{}, entry, valid)), CS.removed_stray(V, order, F.bindings(String, V, Map.to_list(&2, Maybe<&2, T.Entry<String, V>>, table)), key, Native.stray_normal(V, cap, table, order, life, T.Counts{i, e, r, h, m}, cb, valid)))

def correspondence(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry))), O.evicted_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key)):
  %Equal.sym(S.Model<String, V>, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry))), Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry))), Order.normalize(V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry)), Rep.remove_present(~String, ~Codec.string_encode, V, c, key, True{}, entry, valid))) : E.states(~String, ~Lookup.string_same, V, _, O.evicted_state(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key))
  %Equal.sym(S.Model<String, V>, F.abstract(String, V, c), Order.normal(V, c), Order.normalize(V, c, valid)) : E.states(~String, ~Lookup.string_same, V, Order.normal(V, C.step_cache(String, V, C.remove_present(String, V, c, key, True{}, entry))), O.evicted_state(~String, ~Lookup.string_same, V, _, key))
  normalized(V, c, key, entry, valid)

# Check the new named specification state against the unchanged after_eviction
# definition, including the exact entry key and its event metadata.
def flag(-V: Data, s: S.Model<String, V>) -> Bool:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  cb

def specification_equation(-V: Data, s: S.Model<String, V>, key: String, value: V, deadline: T.Int64, old: T.Entry<String, V>) -> {O.after_eviction(~String, ~Lookup.string_same, V, s, key, value, deadline, old) == O.write(~String, ~Lookup.string_same, V, O.evicted_state(~String, ~Lookup.string_same, V, s, Lookup.key(String, V, old)), key, value, deadline, True{}, S.callbacks(String, V, Con{old, Nil{}}, flag(V, s))) : S.Observation<String, V>}:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  T.Item{oldkey, oldvalue, expiry} = old
  {==}
