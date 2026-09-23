import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../spec/cache.bend as S
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./lookup_refinement.bend as L
import ./spec_lookup.bend as Lookup
import ./abstraction_bindings.bend as B
import ./removal_state.bend as Removal
import ./disabled.bend as Disabled
import ./extensional_states.bend as Ext

def branch(-V: Data, c: C.Cache<String, V>, key: String, result: Maybe<&2, T.Entry<String, V>>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.remove_found(String, V, c, key, False{}, result)), S.remove_decision(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, result)):
  match result:
    case None{}: Ext.string_observation_reflexive(V, S.missing_remove(String, V, F.abstract(String, V, c)))
    case Some{entry}: Removal.observation(V, c, key, entry, valid, disabled)

# Whole native Remove operation, every represented callback-disabled String
# cache and every key. All entries/return flags/events and the abstract state
# correspond; only unobservable binding-list enumeration order may differ.
def operation(-V: Data, +c: C.Cache<String, V>, +key: String, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.remove(String, V, Codec.string_encode, c, key)), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key)):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.remove_found(String, V, C.State{cap, table, order, life, counts, cb}, key, False{}, _)), S.remove(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key))
  branch(V, C.State{cap, table, order, life, counts, cb}, key, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), valid, disabled)
