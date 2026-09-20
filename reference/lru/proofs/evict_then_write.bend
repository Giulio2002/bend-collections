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
import ./disabled.bend as Disabled
import ./removal_state.bend as Removal
import ./removal_representation.bend as Rep
import ./eviction_state.bend as Evict
import ./store_state.bend as Store
import ./write_congruence.bend as Write
import ./extensional_states.bend as Ext

# Internal sequencing lemma; the full-cache branch must establish room from its
# actual oldest lookup and pre-eviction capacity invariant.
def known(-V: Data, +c: C.Cache<String, V>, +oldkey: String, +oldvalue: V, +oldexpiry: T.Int64, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, room: Store.bounded(V, C.step_cache(String, V, C.remove_present(String, V, c, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry})), key, value, deadline, True{}, C.step_events(String, V, C.remove_present(String, V, c, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry})))) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.store_after_evict(String, V, key, key, value, deadline, C.remove_present(String, V, c, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}))), O.after_eviction(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, T.Item{oldkey, oldvalue, oldexpiry})):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  %Removal.no_events(V, T.Item{oldkey, oldvalue, oldexpiry}, cb, disabled) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.store_after_evict(String, V, key, key, value, deadline, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}))), O.write(~String, ~Lookup.string_same, V, O.evicted_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), oldkey), key, value, deadline, True{}, _))
  Ext.observation_transitive(~String, ~Lookup.string_same, V, F.observe(String, V, C.store_after_evict(String, V, key, key, value, deadline, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}))), O.write(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}))), key, value, deadline, True{}, C.events(String, V, cb, T.Item{oldkey, oldvalue, oldexpiry})), O.write(~String, ~Lookup.string_same, V, O.evicted_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), oldkey), key, value, deadline, True{}, C.events(String, V, cb, T.Item{oldkey, oldvalue, oldexpiry})), Store.observation(V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry})), key, value, deadline, True{}, C.events(String, V, cb, T.Item{oldkey, oldvalue, oldexpiry}), Rep.remove_present(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}, valid), room), Write.observation(V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, True{}, T.Item{oldkey, oldvalue, oldexpiry}))), O.evicted_state(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), oldkey), key, value, deadline, True{}, C.events(String, V, cb, T.Item{oldkey, oldvalue, oldexpiry}), Evict.correspondence(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, oldkey, T.Item{oldkey, oldvalue, oldexpiry}, valid)))
