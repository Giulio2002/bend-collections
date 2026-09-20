import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../spec/cache.bend as S
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./replacement_refinement.bend as Replacement
import ./nonfull_add.bend as Nonfull
import ./full_add.bend as Full
import ./duration_refinement.bend as Duration

def absent(-V: Data, c: C.Cache<String, V>, key: String, value: V, deadline: T.Int64, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, full: Bool, checked: {Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)) == full : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, None{})), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, None{})):
  match full:
    case False{}: Nonfull.branch(V, c, key, value, deadline, valid, checked)
    case True{}: Full.branch(V, c, key, value, deadline, valid, disabled, checked)

def found(-V: Data, +c: C.Cache<String, V>, +key: String, value: V, deadline: T.Int64, result: Maybe<&2, T.Entry<String, V>>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, decision: {C.lookup(String, V, c, key) == result : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, result)), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, result)):
  match result:
    case None{}: absent(V, c, key, value, deadline, valid, disabled, Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)), {==})
    case Some{T.Item{original, old, expiry}}: Replacement.branch(V, c, key, original, old, expiry, value, deadline, valid, decision)

def at_deadline(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, C.lookup(String, V, c, key))), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key))):
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), L.string_lookup(V, c, key, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, _)), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key)))
  found(V, c, key, value, deadline, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key), valid, disabled, L.string_lookup(V, c, key, valid))

# Whole actual native AddWithLifetime: no remaining store-bound, selected-oldest,
# codec-identity or numeric-arithmetic premise. Public host effects remain open.
def with_lifetime(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +ns: T.Int64, +now: T.Int64, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now)), O.add_with_lifetime(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, ns, now)):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Duration.deadline(now, ns) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_with_lifetime(String, V, Codec.string_encode, C.State{cap, table, order, life, counts, cb}, key, value, ns, now)), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, value, _, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key)))
  at_deadline(V, C.State{cap, table, order, life, counts, cb}, key, value, Time.deadline(now, ns), valid, disabled)

def add(-V: Data, c: C.Cache<String, V>, key: String, value: V, now: T.Int64, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add(String, V, Codec.string_encode, c, key, value, now)), O.add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, now)):
  C.State{cap, table, order, +life, counts, cb} = c
  with_lifetime(V, C.State{cap, table, order, life, counts, cb}, key, value, life, now, valid, disabled)
