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
import ./cache_add_capacity.bend as Capacity
import ./cache_prepare_capacity.bend as Prep
import ./recency_capacity.bend as Bound
import ./configuration_observations.bend as Length
import ./store_state.bend as Store
import ./spec_lookup.bend as Lookup

def capacity(-V: Data, s: S.Model<String, V>) -> Nat:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  cap

def model_dispatch(-V: Data, +s: S.Model<String, V>, +key: String, value: V, deadline: T.Int64, not_full: {Nat.is_ge(S.length(String, V, s), capacity(V, s)) == False{} : Bool}) -> {O.absent_add(~String, ~Lookup.string_same, V, s, key, value, deadline) == O.write(~String, ~Lookup.string_same, V, s, key, value, deadline, False{}, Nil{}) : S.Observation<String, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  Equal.cong(Bool, S.Observation<String, V>, full => O.new_room(~String, ~Lookup.string_same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, value, deadline, bindings, order, full), Nat.is_ge(List.length(&2, String, order), cap), False{}, not_full)

def model_not_full(-V: Data, +c: C.Cache<String, V>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, not_full: {Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)) == False{} : Bool}) -> {Nat.is_ge(S.length(String, V, F.abstract(String, V, c)), capacity(V, F.abstract(String, V, c))) == False{} : Bool}:
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Length.string_length(V, C.State{cap, table, order, life, counts, cb}, valid) : {Nat.is_ge(_, cap) == False{} : Bool}
  not_full

# Nonfull insertion derives the actual store capacity bound from the executed
# comparison. No capacity/resource premise is introduced beyond representation.
def branch(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +not_full: {Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, None{})), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, None{})):
  %Equal.sym(Bool, Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)), False{}, not_full) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_room(String, V, c, key, key, value, deadline, _)), O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline))
  %Equal.sym(S.Observation<String, V>, O.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline), O.write(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, False{}, Nil{}), model_dispatch(V, F.abstract(String, V, c), key, value, deadline, model_not_full(V, c, valid, not_full))) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.store(String, V, c, key, key, value, deadline, False{}, Nil{})), _)
  Store.observation(V, c, key, value, deadline, False{}, Nil{}, valid, Bound.store_preserves_bound(String, V, c, key, key, value, deadline, False{}, Nil{}, Access.get_bounded(~String, ~Codec.string_encode, V, c, valid), Capacity.room_ready(String, V, c, key, Prep.not_full_has_room(C.len(String, V, c), C.capacity(String, V, c), not_full))))
