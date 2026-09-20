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
import ./spec_lookup.bend as Lookup
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./representation_access.bend as Access
import ./cache_key_identity.bend as Identity
import ./duration_refinement.bend as Duration
import ./refresh_state.bend as State
import ./extensional_states.bend as Ext

def miss(-V: Data, c: C.Cache<String, V>, key: String, ns: T.Int64, now: T.Int64) -> {F.observe(String, V, C.refresh_found(String, V, c, key, Time.deadline(now, ns), None{})) == O.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), ns, now, None{}) : S.Observation<String, V>}:
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  {==}

# Successful refresh never tests the old expiration. Original value/key are
# retained, recency/Hits change, and the independently computed deadline replaces
# the old one even when the stored entry was expired.
def present(-V: Data, +c: C.Cache<String, V>, +key: String, +original: String, +value: V, +old: T.Int64, +ns: T.Int64, +now: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +found: {C.lookup(String, V, c, key) == Some{T.Item{original, value, old}} : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_found(String, V, c, key, Time.deadline(now, ns), Some{T.Item{original, value, old}})), O.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), ns, now, Some{T.Item{original, value, old}})):
  +same = Identity.lookup_code_identity(~String, ~Codec.string_encode, V, c, key, T.Item{original, value, old}, Access.get_identities(~String, ~Codec.string_encode, V, c, valid), found)
  original_lookup = Equal.trans(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, c, original), C.lookup(String, V, c, key), Some{T.Item{original, value, old}}, Equal.cong(String, Maybe<&2, T.Entry<String, V>>, k => C.lookup(String, V, c, k), original, key, Equal.sym(String, key, original, same)), found)
  %Duration.deadline(now, ns) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_present(String, V, c, key, T.Item{original, value, Time.deadline(now, ns)})), O.refreshed(~String, ~Lookup.string_same, V, F.abstract(String, V, c), T.Item{original, value, old}, _))
  %Equal.sym(String, key, original, same) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_present(String, V, c, _, T.Item{original, value, Time.deadline(now, ns)})), O.refreshed(~String, ~Lookup.string_same, V, F.abstract(String, V, c), T.Item{original, value, old}, Time.deadline(now, ns)))
  State.observation(V, c, original, value, old, ns, now, valid, original_lookup)

def found(-V: Data, +c: C.Cache<String, V>, +key: String, +ns: T.Int64, +now: T.Int64, result: Maybe<&2, T.Entry<String, V>>, valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, decision: {C.lookup(String, V, c, key) == result : Maybe<&2, T.Entry<String, V>>}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_found(String, V, c, key, Time.deadline(now, ns), result)), O.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), ns, now, result)):
  match result:
    case None{}: Ext.from_equal(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_found(String, V, c, key, Time.deadline(now, ns), None{})), O.refresh_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), ns, now, None{}), miss(V, c, key, ns, now))
    case Some{T.Item{original, value, old}}: present(V, c, key, original, value, old, ns, now, valid, decision)

# Whole native refresh; actual host preparation-before-clock failure semantics
# and marshalling are separate and are not asserted by this theorem.
def operation(-V: Data, +c: C.Cache<String, V>, +key: String, +ns: T.Int64, +now: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.get_and_refresh(String, V, Codec.string_encode, c, key, ns, now)), O.refresh(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, ns, now)):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %Equal.sym(Maybe<&2, T.Entry<String, V>>, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid)) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.refresh_found(String, V, C.State{cap, table, order, life, counts, cb}, key, Time.deadline(now, ns), _)), O.refresh(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, ns, now))
  found(V, C.State{cap, table, order, life, counts, cb}, key, ns, now, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), key), valid, L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid))
