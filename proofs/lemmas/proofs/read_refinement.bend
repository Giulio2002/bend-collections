import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../spec/cache.bend as S
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./absent_read.bend as Absent
import ./live_read_state.bend as Live
import ./expired_read.bend as Expired
import ./extensional_states.bend as Ext
import ./numeric.bend as Numeric

def expiry(-V: Data, +c: C.Cache<String, V>, +key: String, +entry: T.Entry<String, V>, +tracked: Bool, expired: Bool, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, present: {C.lookup(String, V, c, key) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_expiry(String, V, c, key, entry, tracked, expired)), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, expired)):
  match expired:
    case True{}: Expired.branch(V, c, key, entry, tracked, valid, disabled)
    case False{}: Ext.from_equal(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_live(String, V, c, key, entry, tracked)), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, entry, tracked, False{}), Live.observation(V, c, key, entry, tracked, valid, present))

def found(-V: Data, +c: C.Cache<String, V>, +key: String, +now: T.Int64, +tracked: Bool, result: Maybe<&2, T.Entry<String, V>>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}, decision: {C.lookup(String, V, c, key) == result : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, c, key, now, tracked, result)), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, result)):
  match result:
    case None{}: Ext.from_equal(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, c, key, now, tracked, None{})), O.read_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked, None{}), Absent.branch(~String, ~Lookup.string_same, V, c, key, key, now, tracked))
    case Some{T.Item{+original, +value, +deadline}}:
      %Equal.sym(Bool, Time.expired(deadline, now), N.expired(deadline, now), Numeric.expiration_refines(deadline, now)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_expiry(String, V, c, key, T.Item{original, value, deadline}, tracked, _)), O.read_decide(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, T.Item{original, value, deadline}, tracked, N.expired(deadline, now)))
      expiry(V, c, key, T.Item{original, value, deadline}, tracked, N.expired(deadline, now), valid, disabled, decision)

# Whole actual native tracked/untracked read, for all keys and int64 times:
# absent, live, expired and immortal cases; exact recency, metrics and events.
# The actual host's clock acquisition and zero-value conversion are not assumed
# to follow from this native theorem and remain separate obligations.
def operation(-V: Data, +c: C.Cache<String, V>, +key: String, +now: T.Int64, +tracked: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_encoded(String, V, c, key, now, tracked)), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, now, tracked)):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.read_found(String, V, C.State{cap, table, order, life, counts, cb}, key, now, tracked, _)), O.read(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, now, tracked))
  found(V, C.State{cap, table, order, life, counts, cb}, key, now, tracked, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), valid, disabled, L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid))
