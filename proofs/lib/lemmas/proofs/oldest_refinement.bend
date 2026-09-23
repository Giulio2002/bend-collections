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
import ./read_refinement.bend as Read
import ./remove_refinement.bend as Remove
import ./extensional_states.bend as Ext
import ./string_order.bend as Order
import ./abstraction_recency.bend as Recency

def remove_branch(-V: Data, c: C.Cache<String, V>, order: List<&2, String>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.oldest_remove(String, V, c, order, False{})), O.oldest_remove(~String, ~Lookup.string_same, V, F.abstract(String, V, c), order)):
  match order:
    case Nil{}: Ext.string_observation_reflexive(V, S.missing_remove(String, V, F.abstract(String, V, c)))
    case Con{key, rest}: Remove.operation(V, c, key, valid, disabled)

def read_branch(-V: Data, c: C.Cache<String, V>, order: List<&2, String>, now: T.Int64, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.oldest_read(String, V, c, order, now)), O.oldest_read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), order, now)):
  match order:
    case Nil{}: Ext.string_observation_reflexive(V, S.missing_remove(String, V, F.abstract(String, V, c)))
    case Con{key, rest}: Read.operation(V, c, key, now, False{}, valid, disabled)

def remove_oldest(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.remove_oldest(String, V, c, False{})), O.remove_oldest(~String, ~Lookup.string_same, V, F.abstract(String, V, c))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(List<&2, String>, Recency.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, Order.faithful(V, C.State{cap, table, order, life, counts, cb}, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.oldest_remove(String, V, C.State{cap, table, order, life, counts, cb}, order, False{})), O.oldest_remove(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), _))
  remove_branch(V, C.State{cap, table, order, life, counts, cb}, order, valid, disabled)

# Internal native GetOldest observation. The public captured-key/zero-value
# projection and clock effects remain the separate facade composition obligation.
def get_oldest(-V: Data, c: C.Cache<String, V>, +now: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.get_oldest(String, V, c, now)), O.get_oldest(~String, ~Lookup.string_same, V, F.abstract(String, V, c), now)):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(List<&2, String>, Recency.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, Order.faithful(V, C.State{cap, table, order, life, counts, cb}, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.oldest_read(String, V, C.State{cap, table, order, life, counts, cb}, order, now)), O.oldest_read(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), _, now))
  read_branch(V, C.State{cap, table, order, life, counts, cb}, order, now, valid, disabled)
