import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/cache.bend as S
import ../spec/clock.bend as Clock
import ../spec/numeric.bend as N
import ../spec/operations.bend as O
import ../spec/effectful_operations.bend as Eff
import ../spec/public_commands.bend as PC
import ../spec/equivalence.bend as E
import ../types/model.bend as T
import ./refinement.bend as F
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./spec_lookup.bend as Lookup
import ./public_relation.bend as R
import ./public_finish.bend as Finish
import ./extensional_states.bend as Ext
import ./empty_events.bend as Events
import ./add_refinement.bend as AddRefinement
import ./eviction_state.bend as Eviction
import ./lookup_refinement.bend as L
import ./abstraction_bindings.bend as B
import ./abstraction_recency.bend as Recency
import ./string_order.bend as Order
import ./cache_key_identity.bend as Key
import ./representation_access.bend as Access
import ./configuration_observations.bend as Config
import ./duration_refinement.bend as Duration
import ./numeric.bend as Numeric
import ./map_routing.bend as Routing

# Public Add/AddWithLifetime through the actual start/resume/abandon machine.
# The eviction (and its counter) happens before the clock request; a failed
# request retains it. After a sample the prepared cache receives one store.

# Proof-side projections of the independent prepared-Add record.
def prepared_state(-K: Data, -V: Data, p: Eff.PreparedAdd<K, V>) -> S.Model<K, V>:
  Eff.Prepared{s, k, ev} = p
  s

def write_prepared(~K: Data, ~same: K -> K -> Bool, -V: Data, p: Eff.PreparedAdd<K, V>, value: V, deadline: T.Int64) -> S.Observation<K, V>:
  Eff.Prepared{s, k, ev} = p
  O.write(~K, ~same, V, s, k, value, deadline, ev, Nil{})

def model_flag(-K: Data, -V: Data, s: S.Model<K, V>) -> Bool:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  cb

def sampled_accepted(~K: Data, ~same: K -> K -> Bool, -V: Data, p: Eff.PreparedAdd<K, V>, value: V, ns: T.Int64, now: T.Int64, remaining: List<&2, Clock.ClockEvent>) -> {Eff.sampled_add(~K, ~same, V, p, value, ns, Clock.Accepted{now, remaining}) == Eff.Returned{write_prepared(~K, ~same, V, p, value, N.deadline(now, ns)), remaining, 1n} : Eff.Outcome<K, V>}:
  match p:
    case Eff.Prepared{s, k, ev}: {==}

def sampled_rejected(~K: Data, ~same: K -> K -> Bool, -V: Data, p: Eff.PreparedAdd<K, V>, value: V, ns: T.Int64, error: Clock.Error, remaining: List<&2, Clock.ClockEvent>) -> {Eff.sampled_add(~K, ~same, V, p, value, ns, Clock.Rejected{error, remaining}) == Eff.Failed{prepared_state(K, V, p), error, remaining, 1n} : Eff.Outcome<K, V>}:
  match p:
    case Eff.Prepared{s, k, ev}: {==}

def immortal_added(~K: Data, ~same: K -> K -> Bool, -V: Data, p: Eff.PreparedAdd<K, V>, value: V, events: List<&2, Clock.ClockEvent>) -> {Eff.immortal_add(~K, ~same, V, p, value, events) == Eff.Returned{write_prepared(~K, ~same, V, p, value, T.I64{Word.zero(64n)}), events, 0n} : Eff.Outcome<K, V>}:
  match p:
    case Eff.Prepared{s, k, ev}: {==}

# The independent split Add (prepare, then write) equals the independent
# combined add_found for disabled legacy metadata.
def split_evict(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, entry: T.Entry<K, V>, disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.evicted(~K, ~same, V, s, key, entry), value, deadline) == O.after_eviction(~K, ~same, V, s, key, value, deadline, entry) : S.Observation<K, V>}:
  match s entry:
    case S.Abstract{+cap, +bindings, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} T.Item{+ok, +ov, +od}:
      %Equal.sym(Bool, cb, False{}, disabled) : {write_prepared(~K, ~same, V, Eff.evicted(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, _}, key, T.Item{ok, ov, od}), value, deadline) == O.after_eviction(~K, ~same, V, S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, _}, key, value, deadline, T.Item{ok, ov, od}) : S.Observation<K, V>}
      {==}

def split_found_old(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>, +disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.evict_found(~K, ~same, V, s, key, found), value, deadline) == O.evict_found(~K, ~same, V, s, key, value, deadline, found) : S.Observation<K, V>}:
  match found:
    case None{}: {==}
    case Some{entry}: split_evict(~K, ~same, V, s, key, value, deadline, entry, disabled)

def split_first(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, +bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>, +disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.evict_first(~K, ~same, V, s, key, bindings, order), value, deadline) == O.evict_first(~K, ~same, V, s, key, value, deadline, bindings, order) : S.Observation<K, V>}:
  match order:
    case Nil{}: {==}
    case Con{old, tail}: split_found_old(~K, ~same, V, s, key, value, deadline, S.find(~K, ~same, V, bindings, old), disabled)

def split_room(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, +bindings: List<&2, T.Entry<K, V>>, +order: List<&2, K>, full: Bool, +disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.room(~K, ~same, V, s, key, bindings, order, full), value, deadline) == O.new_room(~K, ~same, V, s, key, value, deadline, bindings, order, full) : S.Observation<K, V>}:
  match full:
    case False{}: {==}
    case True{}: split_first(~K, ~same, V, s, key, value, deadline, bindings, order, disabled)

def split_found(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>, +disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.prepare_found(~K, ~same, V, s, key, found), value, deadline) == O.add_found(~K, ~same, V, s, key, value, deadline, found) : S.Observation<K, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  match found:
    case Some{T.Item{o, ov, od}}: {==}
    case None{}:
      split_room(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, value, deadline, bindings, order, Nat.is_ge(List.length(&2, K, order), cap), disabled)

def spec_split(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, +value: V, +deadline: T.Int64, +disabled: {model_flag(K, V, s) == False{} : Bool}) -> {write_prepared(~K, ~same, V, Eff.prepare_add(~K, ~same, V, s, key), value, deadline) == O.add_found(~K, ~same, V, s, key, value, deadline, S.find(~K, ~same, V, B.model_bindings(K, V, s), key)) : S.Observation<K, V>}:
  S.Abstract{+cap, +bindings, +order, +life, +counts, +cb} = s
  split_found(~K, ~same, V, S.Abstract{cap, bindings, order, life, counts, cb}, key, value, deadline, S.find(~K, ~same, V, bindings, key), disabled)

# The actual split Add (prepare, then one store) has the same observation as
# the actual combined add_found for disabled legacy metadata.
def prepared_store(-K: Data, -V: Data, step: C.Step<K, V>, code: String, key: K, value: V, deadline: T.Int64) -> C.Step<K, V>:
  C.Out{c, item, flag, events} = step
  C.store(K, V, c, code, key, value, deadline, flag, Nil{})

def actual_split_evicted(-K: Data, -V: Data, step: C.Step<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, no_events: Events.empty(K, V, step)) -> {F.observe(K, V, prepared_store(K, V, step, code, key, value, deadline)) == F.observe(K, V, C.store_after_evict(K, V, code, key, value, deadline, step)) : S.Observation<K, V>}:
  C.Out{+c, item, +flag, evs} = step
  %Equal.sym(List<&2, T.LruEvent<K, V>>, evs, Nil{}, no_events) : {F.observe(K, V, C.store(K, V, c, code, key, value, deadline, flag, Nil{})) == F.observe(K, V, C.store(K, V, c, code, key, value, deadline, flag, _)) : S.Observation<K, V>}
  {==}

def actual_split_room(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, full: Bool, disabled: {Disabled.flag(K, V, c) == False{} : Bool}) -> {F.observe(K, V, prepared_store(K, V, Pub.prepare_room(K, V, c, full), code, key, value, deadline)) == F.observe(K, V, C.add_room(K, V, c, code, key, value, deadline, full)) : S.Observation<K, V>}:
  match full:
    case False{}: {==}
    case True{}: actual_split_evicted(K, V, C.remove_oldest(K, V, c, True{}), code, key, value, deadline, Events.remove_oldest(K, V, c, True{}, disabled))

def actual_split(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String, +key: K, +value: V, +deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>, disabled: {Disabled.flag(K, V, c) == False{} : Bool}) -> {F.observe(K, V, prepared_store(K, V, Pub.prepare_found(K, V, c, found), code, Pub.retained_key(K, V, key, found), value, deadline)) == F.observe(K, V, C.add_found(K, V, c, code, key, value, deadline, found)) : S.Observation<K, V>}:
  match found:
    case Some{T.Item{o, ov, od}}: {==}
    case None{}: actual_split_room(K, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)), disabled)

def abstract_flag(-K: Data, -V: Data, +c: C.Cache<K, V>, disabled: {Disabled.flag(K, V, c) == False{} : Bool}) -> {model_flag(K, V, F.abstract(K, V, c)) == False{} : Bool}:
  C.State{cap, table, order, life, counts, cb} = c
  disabled

# Successful insertion at any deadline: actual split store versus independent
# split write, composed through the checked combined native Add law.
def inserted(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +deadline: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, deadline)), write_prepared(~String, ~Lookup.string_same, V, Eff.prepare_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), value, deadline)):
  Ext.observation_transitive(~String, ~Lookup.string_same, V, F.observe(String, V, prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, deadline)), F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, C.lookup(String, V, c, key))), write_prepared(~String, ~Lookup.string_same, V, Eff.prepare_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), value, deadline), Ext.from_equal(~String, ~Lookup.string_same, V, F.observe(String, V, prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, deadline)), F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, C.lookup(String, V, c, key))), actual_split(String, V, c, key, key, value, deadline, C.lookup(String, V, c, key), disabled)), %Equal.sym(S.Observation<String, V>, write_prepared(~String, ~Lookup.string_same, V, Eff.prepare_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), value, deadline), O.add_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, S.find(~String, ~Lookup.string_same, V, B.model_bindings(String, V, F.abstract(String, V, c)), key)), spec_split(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, value, deadline, abstract_flag(String, V, c, disabled))) : E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.add_found(String, V, c, key, key, value, deadline, C.lookup(String, V, c, key))), _) AddRefinement.at_deadline(V, c, key, value, deadline, valid, disabled))

# The state retained when the awaited request fails: the prepared cache,
# including a completed pre-clock eviction and its Evictions increment.
def fail_evict(-V: Data, +c: C.Cache<String, V>, +key: String, +old: String, result: Maybe<&2, T.Entry<String, V>>, +decision: {C.lookup(String, V, c, old) == result : Maybe<&2, T.Entry<String, V>>}, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_found(String, V, c, old, True{}, result))), prepared_state(String, V, Eff.evict_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, result))):
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  match result:
    case None{}: Ext.reflexive(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}))
    case Some{T.Item{+ok, +ov, +od}}:
      %Key.string_lookup_key(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, old, ok, ov, od, Access.get_identities(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, valid), decision) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_present(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, old, True{}, T.Item{ok, ov, od}))), prepared_state(String, V, Eff.evicted(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), key, T.Item{_, ov, od})))
      Eviction.correspondence(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, old, T.Item{ok, ov, od}, valid)

def fail_order(-V: Data, +c: C.Cache<String, V>, +key: String, xs: List<&2, String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.oldest_remove(String, V, c, xs, True{}))), prepared_state(String, V, Eff.evict_first(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, B.model_bindings(String, V, F.abstract(String, V, c)), xs))):
  match xs:
    case Nil{}: Ext.reflexive(~String, ~Lookup.string_same, V, F.abstract(String, V, c))
    case Con{+old, rest}:
      %L.string_lookup(V, c, old, valid) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.remove_found(String, V, c, old, True{}, C.lookup(String, V, c, old)))), prepared_state(String, V, Eff.evict_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, _)))
      fail_evict(V, c, key, old, C.lookup(String, V, c, old), {==}, valid)

def fail_room(-V: Data, +c: C.Cache<String, V>, +key: String, full: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, Pub.prepare_room(String, V, c, full))), prepared_state(String, V, Eff.room(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, B.model_bindings(String, V, F.abstract(String, V, c)), Recency.model_order(String, V, F.abstract(String, V, c)), full))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  match full:
    case False{}: Ext.reflexive(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))
    case True{}:
      %Equal.sym(List<&2, String>, Recency.model_order(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), order, Order.faithful(V, C.State{cap, table, order, life, counts, cb}, valid)) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, C.oldest_remove(String, V, C.State{cap, table, order, life, counts, cb}, order, True{}))), prepared_state(String, V, Eff.evict_first(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, B.model_bindings(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), _)))
      fail_order(V, C.State{cap, table, order, life, counts, cb}, key, order, valid)

def fail_found(-V: Data, +c: C.Cache<String, V>, +key: String, result: Maybe<&2, T.Entry<String, V>>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, Pub.prepare_found(String, V, c, result))), prepared_state(String, V, Eff.prepare_found(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key, result))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  match result:
    case Some{T.Item{o, ov, od}}: Ext.reflexive(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}))
    case None{}:
      %Equal.sym(Nat, C.len(String, V, C.State{cap, table, order, life, counts, cb}), S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), Config.length(~String, ~Codec.string_encode, V, C.State{cap, table, order, life, counts, cb}, valid)) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, Pub.prepare_room(String, V, C.State{cap, table, order, life, counts, cb}, Nat.is_ge(_, C.capacity(String, V, C.State{cap, table, order, life, counts, cb}))))), prepared_state(String, V, Eff.absent_add(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key)))
      fail_room(V, C.State{cap, table, order, life, counts, cb}, key, Nat.is_ge(S.length(String, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb})), cap), valid)

def fail_prepare(-V: Data, +c: C.Cache<String, V>, +key: String, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}) -> E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)))), prepared_state(String, V, Eff.prepare_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  %L.string_lookup(V, C.State{cap, table, order, life, counts, cb}, key, valid) : E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, Pub.prepare_found(String, V, C.State{cap, table, order, life, counts, cb}, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key)))), prepared_state(String, V, Eff.prepare_found(~String, ~Lookup.string_same, V, F.abstract(String, V, C.State{cap, table, order, life, counts, cb}), key, _)))
  fail_found(V, C.State{cap, table, order, life, counts, cb}, key, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, key), valid)

# The awaited clock request and the immortal no-request path.
def lifetime(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +code: String, +key: String, +value: V, +ns: T.Int64, +evicted: Bool, +p: Eff.PreparedAdd<String, V>, immortal: Bool, +events: List<&2, Clock.ClockEvent>, success: @+moment: T.Int64 -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, C.store(String, V, c, code, key, value, moment, evicted, Nil{})), write_prepared(~String, ~Lookup.string_same, V, p, value, moment)), failure: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, c), prepared_state(String, V, p))) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.add_lifetime(String, V, zero_value, c, code, key, value, ns, evicted, immortal)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, Eff.add_lifetime(~String, ~Lookup.string_same, V, p, value, ns, events, immortal))):
  match immortal:
    case True{}:
      %Equal.sym(Eff.Outcome<String, V>, Eff.immortal_add(~String, ~Lookup.string_same, V, p, value, events), Eff.Returned{write_prepared(~String, ~Lookup.string_same, V, p, value, T.I64{Word.zero(64n)}), events, 0n}, immortal_added(~String, ~Lookup.string_same, V, p, value, events)) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, C.store(String, V, c, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{})), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, _))
      %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, C.store(String, V, c, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{})), Finish.returned(V, zero_value, C.store(String, V, c, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{}, events, 0n), Finish.drive_step(V, zero_value, C.store(String, V, c, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{}, events)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, write_prepared(~String, ~Lookup.string_same, V, p, value, T.I64{Word.zero(64n)}), events, 0n))
      Finish.finished(V, zero_key, zero_value, C.store(String, V, c, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{}, write_prepared(~String, ~Lookup.string_same, V, p, value, T.I64{Word.zero(64n)}), events, 0n, {==}, success(Pub.zero_time()))
    case False{}:
      match events:
        case Nil{}:
          %Equal.sym(Eff.Outcome<String, V>, Eff.sampled_add(~String, ~Lookup.string_same, V, p, value, ns, Clock.Rejected{Clock.Exhausted{}, Nil{}}), Eff.Failed{prepared_state(String, V, p), Clock.Exhausted{}, Nil{}, 1n}, sampled_rejected(~String, ~Lookup.string_same, V, p, value, ns, Clock.Exhausted{}, Nil{})) : R.results(~String, ~Lookup.string_same, V, D.Failed{c, Clock.Exhausted{}, Nil{}, 1n}, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, _))
          (failure, {==}, {==}, {==})
        case Con{Clock.InvalidSample{+reason}, +tail}:
          %Equal.sym(Eff.Outcome<String, V>, Eff.sampled_add(~String, ~Lookup.string_same, V, p, value, ns, Clock.Rejected{Clock.Invalid{reason}, tail}), Eff.Failed{prepared_state(String, V, p), Clock.Invalid{reason}, tail, 1n}, sampled_rejected(~String, ~Lookup.string_same, V, p, value, ns, Clock.Invalid{reason}, tail)) : R.results(~String, ~Lookup.string_same, V, D.Failed{c, Clock.Invalid{reason}, tail, 1n}, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, _))
          (failure, {==}, {==}, {==})
        case Con{Clock.ProviderException{+reason}, +tail}:
          %Equal.sym(Eff.Outcome<String, V>, Eff.sampled_add(~String, ~Lookup.string_same, V, p, value, ns, Clock.Rejected{Clock.Thrown{reason}, tail}), Eff.Failed{prepared_state(String, V, p), Clock.Thrown{reason}, tail, 1n}, sampled_rejected(~String, ~Lookup.string_same, V, p, value, ns, Clock.Thrown{reason}, tail)) : R.results(~String, ~Lookup.string_same, V, D.Failed{c, Clock.Thrown{reason}, tail, 1n}, PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, _))
          (failure, {==}, {==}, {==})
        case Con{Clock.Sample{+now}, +tail}:
          %Equal.sym(Eff.Outcome<String, V>, Eff.sampled_add(~String, ~Lookup.string_same, V, p, value, ns, Clock.Accepted{now, tail}), Eff.Returned{write_prepared(~String, ~Lookup.string_same, V, p, value, N.deadline(now, ns)), tail, 1n}, sampled_accepted(~String, ~Lookup.string_same, V, p, value, ns, now, tail)) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.finish_step(String, V, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}))), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, _))
          %Duration.deadline(now, ns) : R.results(~String, ~Lookup.string_same, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.finish_step(String, V, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}))), PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, write_prepared(~String, ~Lookup.string_same, V, p, value, _), tail, 1n))
          %Equal.sym(D.Outcome<String, V>, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.finish_step(String, V, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}))), Finish.returned(V, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}, tail, 1n), Finish.bump_step(V, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}, tail)) : R.results(~String, ~Lookup.string_same, V, _, PC.observation(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, write_prepared(~String, ~Lookup.string_same, V, p, value, Time.deadline(now, ns)), tail, 1n))
          Finish.finished(V, zero_key, zero_value, C.store(String, V, c, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}, write_prepared(~String, ~Lookup.string_same, V, p, value, Time.deadline(now, ns)), tail, 1n, {==}, success(Time.deadline(now, ns)))

def prepared(-V: Data, zero_key: String, +zero_value: V, step: C.Step<String, V>, +code: String, +key: String, +value: V, +bits: Word(64n), +p: Eff.PreparedAdd<String, V>, +events: List<&2, Clock.ClockEvent>, success: @+moment: T.Int64 -> E.observations(~String, ~Lookup.string_same, V, F.observe(String, V, prepared_store(String, V, step, code, key, value, moment)), write_prepared(~String, ~Lookup.string_same, V, p, value, moment)), failure: E.states(~String, ~Lookup.string_same, V, F.abstract(String, V, C.step_cache(String, V, step)), prepared_state(String, V, p))) -> R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.add_prepared(String, V, zero_value, step, code, key, value, T.I64{bits})), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, Eff.add_lifetime(~String, ~Lookup.string_same, V, p, value, T.I64{bits}, events, N.zero(bits)))):
  C.Out{+c, item, +evicted, evs} = step
  %Numeric.zero_comparison_correspondence(64n, bits) : R.results(~String, ~Lookup.string_same, V, D.drive(String, V, zero_value, events, Pub.add_lifetime(String, V, zero_value, c, code, key, value, T.I64{bits}, evicted, _)), PC.effect(~String, ~Lookup.string_same, V, zero_key, zero_value, PC.Flag{}, Eff.add_lifetime(~String, ~Lookup.string_same, V, p, value, T.I64{bits}, events, N.zero(bits))))
  lifetime(V, zero_key, zero_value, c, code, key, value, T.I64{bits}, evicted, p, N.zero(bits), events, success, failure)

# Whole public AddWithLifetime/Add for every event list, including failures.
def with_lifetime(-V: Data, zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +key: String, +value: V, ns: T.Int64, events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.AddWithLifetime{key, value, ns}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.AddWithLifetime{key, value, ns})):
  T.I64{+bits} = ns
  prepared(V, zero_key, zero_value, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, bits, Eff.prepare_add(~String, ~Lookup.string_same, V, F.abstract(String, V, c), key), events, moment => inserted(V, c, key, value, moment, valid, disabled), fail_prepare(V, c, key, valid))

def add(-V: Data, zero_key: String, +zero_value: V, c: C.Cache<String, V>, +key: String, +value: V, events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> R.results(~String, ~Lookup.string_same, V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, Pub.Add{key, value}), PC.execute(~String, ~Lookup.string_same, V, F.abstract(String, V, c), zero_key, zero_value, events, S.Add{key, value})):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  with_lifetime(V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, key, value, life, events, valid, disabled)
