import Base
import ../src/cache.bend as C
import ../src/codec.bend as Codec
import ../src/time.bend as Time
import ../src/entry_ops.bend as Entry
import ../src/protocol.bend as P
import ../src/public.bend as Pub
import ../src/driver.bend as D
import ../spec/clock.bend as Clock
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./disabled.bend as Disabled
import ./public_drive.bend as Drive
import ./public_add.bend as PublicAdd
import ./public_aggregate.bend as Aggregate
import ./representation_access.bend as Access
import ./read_representation.bend as ReadRep
import ./removal_representation.bend as RemovalRep
import ./add_representation.bend as AddRep
import ./refresh_representation.bend as RefreshRep
import ./refresh_complete_representation.bend as RefreshComplete
import ./refresh_lookup.bend as RefreshLookup
import ./configuration_representation.bend as ConfigRep
import ./map_routing.bend as Routing

# Public reachability: the cache of every outcome of the actual machine (the
# final cache, or the state retained after a clock failure) keeps the full
# representation invariant and disabled legacy callback metadata.

def ok(-V: Data, c: C.Cache<String, V>) -> Type:
  {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool} & {Disabled.flag(String, V, c) == False{} : Bool}

def outcome_ok(-V: Data, outcome: D.Outcome<String, V>) -> Type:
  ok(V, D.cache(String, V, outcome))

def finished_ok(-V: Data, +zero_value: V, +events: List<&2, Clock.ClockEvent>, +c: C.Cache<String, V>, +answer: Pub.Answer<String, V>, safe: ok(V, c)) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.Finished{c, answer})):
  %Equal.sym(D.Outcome<String, V>, D.drive(String, V, zero_value, events, Pub.Finished{c, answer}), D.Returned{c, answer, events, 0n}, Drive.finished(String, V, zero_value, events, c, answer)) : outcome_ok(V, _)
  safe

def bump_cache(-V: Data, outcome: D.Outcome<String, V>) -> {D.cache(String, V, D.bump(String, V, outcome)) == D.cache(String, V, outcome) : C.Cache<String, V>}:
  match outcome:
    case D.Returned{c, answer, events, count}: {==}
    case D.Failed{c, error, events, count}: {==}

# One awaited request: failures keep the abandoned state; a sample resumes.
def waiting_ok(-V: Data, +zero_value: V, pending: Pub.Pending<String, V>, abandoned: ok(V, Pub.abandon(String, V, pending)), next: @now: T.Int64 -> @tail: List<&2, Clock.ClockEvent> -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, pending, now))), events: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.Waiting{pending})):
  match events:
    case Nil{}: abandoned
    case Con{Clock.InvalidSample{reason}, tail}: abandoned
    case Con{Clock.ProviderException{reason}, tail}: abandoned
    case Con{Clock.Sample{+now}, +tail}:
      %Equal.sym(C.Cache<String, V>, D.cache(String, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, pending, now)))), D.cache(String, V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, pending, now))), bump_cache(V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, pending, now)))) : ok(V, _)
      next(now, tail)

def flag_step(-V: Data, step: C.Step<String, V>) -> {Disabled.flag(String, V, C.step_cache(String, V, step)) == Disabled.step_flag(String, V, step) : Bool}:
  C.Out{c, item, flag, events} = step
  {==}


def step_finished_ok(-V: Data, +zero_value: V, +events: List<&2, Clock.ClockEvent>, step: C.Step<String, V>, +shape: Pub.Shape<String>, safe: ok(V, C.step_cache(String, V, step))) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.finish_step(String, V, zero_value, step, shape))):
  C.Out{+c, +item, +flag, evs} = step
  finished_ok(V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, item, flag, shape), safe)

# ---------------------------------------------------------------------------
# Cache-level facts for each actual transition used by the public machine.
def flag_removed_miss(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +tracked: Bool, found: Maybe<&2, T.Entry<String, V>>) -> {Disabled.flag(String, V, C.step_cache(String, V, C.miss_after_remove(String, V, C.remove_found(String, V, C.State{cap, table, order, life, counts, cb}, code, False{}, found), tracked))) == cb : Bool}:
  match found:
    case None{}: {==}
    case Some{entry}: {==}

def flag_read_expiry(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +k: String, +v: V, +d: T.Int64, +tracked: Bool, expired: Bool) -> {Disabled.flag(String, V, C.step_cache(String, V, C.read_expiry(String, V, C.State{cap, table, order, life, counts, cb}, code, T.Item{k, v, d}, tracked, expired))) == cb : Bool}:
  match expired:
    case False{}: {==}
    case True{}: flag_removed_miss(V, cap, table, order, life, counts, cb, code, tracked, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, code))

def flag_read_found(-V: Data, +cap: Nat, +table: Map<&2, Maybe<&2, T.Entry<String, V>>>, +order: List<&2, String>, +life: T.Int64, +counts: T.Metrics, +cb: Bool, +code: String, +now: T.Int64, +tracked: Bool, found: Maybe<&2, T.Entry<String, V>>) -> {Disabled.flag(String, V, C.step_cache(String, V, C.read_found(String, V, C.State{cap, table, order, life, counts, cb}, code, now, tracked, found))) == cb : Bool}:
  match found:
    case None{}: {==}
    case Some{T.Item{+k, +v, +d}}: flag_read_expiry(V, cap, table, order, life, counts, cb, code, k, v, d, tracked, Time.expired(d, now))

def read_ok(-V: Data, c: C.Cache<String, V>, +code: String, +now: T.Int64, +tracked: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.step_cache(String, V, C.read_encoded(String, V, c, code, now, tracked))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  (ReadRep.string_read_encoded(V, C.State{cap, table, order, life, counts, cb}, code, now, tracked, valid), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, C.read_encoded(String, V, C.State{cap, table, order, life, counts, cb}, code, now, tracked))), cb, False{}, flag_read_found(V, cap, table, order, life, counts, cb, code, now, tracked, C.lookup(String, V, C.State{cap, table, order, life, counts, cb}, code)), disabled))

def removed_ok(-V: Data, +c: C.Cache<String, V>, +code: String, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.step_cache(String, V, C.remove_encoded(String, V, c, code, False{}))):
  (RemovalRep.remove_encoded(~String, ~Codec.string_encode, V, c, code, False{}, valid), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, C.remove_encoded(String, V, c, code, False{}))), Disabled.step_flag(String, V, C.remove_encoded(String, V, c, code, False{})), False{}, flag_step(V, C.remove_encoded(String, V, c, code, False{})), Equal.trans(Bool, Disabled.step_flag(String, V, C.remove_encoded(String, V, c, code, False{})), Disabled.flag(String, V, c), False{}, Disabled.remove_encoded(String, V, c, code, False{}), disabled)))

def oldest_removed_ok(-V: Data, +c: C.Cache<String, V>, +evict: Bool, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.step_cache(String, V, C.remove_oldest(String, V, c, evict))):
  (RemovalRep.string_remove_oldest(V, c, evict, valid), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, C.remove_oldest(String, V, c, evict))), Disabled.step_flag(String, V, C.remove_oldest(String, V, c, evict)), False{}, flag_step(V, C.remove_oldest(String, V, c, evict)), Equal.trans(Bool, Disabled.step_flag(String, V, C.remove_oldest(String, V, c, evict)), Disabled.flag(String, V, c), False{}, Disabled.remove_oldest(String, V, c, evict), disabled)))

def prepared_room_ok(-V: Data, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, full: Bool) -> ok(V, C.step_cache(String, V, Pub.prepare_room(String, V, c, full))):
  match full:
    case False{}: (valid, disabled)
    case True{}: oldest_removed_ok(V, c, True{}, valid, disabled)

# The pre-clock Add preparation (possibly an eviction) is a safe state.
def prepared_ok(-V: Data, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, found: Maybe<&2, T.Entry<String, V>>) -> ok(V, C.step_cache(String, V, Pub.prepare_found(String, V, c, found))):
  match found:
    case Some{entry}: (valid, disabled)
    case None{}: prepared_room_ok(V, c, valid, disabled, Nat.is_ge(C.len(String, V, c), C.capacity(String, V, c)))

# The split Add leaves exactly the cache of the combined native add_found.
def split_evicted_cache(-V: Data, step: C.Step<String, V>, +code: String, +key: String, +value: V, +deadline: T.Int64) -> {C.step_cache(String, V, PublicAdd.prepared_store(String, V, step, code, key, value, deadline)) == C.step_cache(String, V, C.store_after_evict(String, V, code, key, value, deadline, step)) : C.Cache<String, V>}:
  C.Out{C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, item, flag, events} = step
  {==}

def split_room_cache(-V: Data, +c: C.Cache<String, V>, +code: String, +key: String, +value: V, +deadline: T.Int64, full: Bool) -> {C.step_cache(String, V, PublicAdd.prepared_store(String, V, Pub.prepare_room(String, V, c, full), code, key, value, deadline)) == C.step_cache(String, V, C.add_room(String, V, c, code, key, value, deadline, full)) : C.Cache<String, V>}:
  match full:
    case False{}: {==}
    case True{}: split_evicted_cache(V, C.remove_oldest(String, V, c, True{}), code, key, value, deadline)

def split_cache(-V: Data, c: C.Cache<String, V>, +code: String, +key: String, +value: V, +deadline: T.Int64, found: Maybe<&2, T.Entry<String, V>>) -> {C.step_cache(String, V, PublicAdd.prepared_store(String, V, Pub.prepare_found(String, V, c, found), code, Pub.retained_key(String, V, key, found), value, deadline)) == C.step_cache(String, V, C.add_found(String, V, c, code, key, value, deadline, found)) : C.Cache<String, V>}:
  C.State{+cap, +table, +order, +life, T.Counts{+i, +e, +r, +h, +m}, +cb} = c
  match found:
    case Some{T.Item{o, ov, od}}: {==}
    case None{}: split_room_cache(V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}, code, key, value, deadline, Nat.is_ge(C.len(String, V, C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb}), cap))

# The single post-clock store of a public Add is a safe state.
def stored_ok(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +ns: T.Int64, +now: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.step_cache(String, V, PublicAdd.prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, Time.deadline(now, ns)))):
  %Equal.sym(C.Cache<String, V>, C.step_cache(String, V, PublicAdd.prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, Time.deadline(now, ns))), C.step_cache(String, V, C.add_found(String, V, c, key, key, value, Time.deadline(now, ns), C.lookup(String, V, c, key))), split_cache(V, c, key, key, value, Time.deadline(now, ns), C.lookup(String, V, c, key))) : ok(V, _)
  (AddRep.string_add_with_lifetime(V, c, key, value, ns, now, valid), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now))), Disabled.step_flag(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now)), False{}, flag_step(V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now)), Equal.trans(Bool, Disabled.step_flag(String, V, C.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now)), Disabled.flag(String, V, c), False{}, Disabled.add_with_lifetime(String, V, Codec.string_encode, c, key, value, ns, now), disabled)))

# Refresh preparation (hit and recency move, or miss count) is safe; so is the
# refreshed deadline written after an accepted sample.
def refresh_prepared_ok(-V: Data, +c: C.Cache<String, V>, +code: String, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code))):
  (RefreshRep.string_prepare(V, c, code, valid), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code))), Disabled.step_flag(String, V, Entry.refresh_prepare(String, V, c, code)), False{}, flag_step(V, Entry.refresh_prepare(String, V, c, code)), Equal.trans(Bool, Disabled.step_flag(String, V, Entry.refresh_prepare(String, V, c, code)), Disabled.flag(String, V, c), False{}, Disabled.refresh_prepare(String, V, c, code), disabled)))

def refreshed_ok(-V: Data, +c: C.Cache<String, V>, +code: String, +entry: T.Entry<String, V>, +life: T.Int64, +now: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +returned: {RefreshLookup.item(String, V, Entry.refresh_prepare(String, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> ok(V, Entry.refresh_at(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code)), code, entry, life, now)):
  (RefreshComplete.string_complete(V, c, code, entry, life, now, valid, returned), Equal.trans(Bool, Disabled.flag(String, V, Entry.refresh_at(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code)), code, entry, life, now)), Disabled.flag(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code))), False{}, Disabled.refresh_at(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code)), code, entry, life, now), Equal.trans(Bool, Disabled.flag(String, V, C.step_cache(String, V, Entry.refresh_prepare(String, V, c, code))), Disabled.step_flag(String, V, Entry.refresh_prepare(String, V, c, code)), False{}, flag_step(V, Entry.refresh_prepare(String, V, c, code)), Equal.trans(Bool, Disabled.step_flag(String, V, Entry.refresh_prepare(String, V, c, code)), Disabled.flag(String, V, c), False{}, Disabled.refresh_prepare(String, V, c, code), disabled))))

# Full Purge keeps a positive capacity with an empty native Map.
def purge_ok(-V: Data, c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, Pub.purge(String, V, c)):
  match c:
    case C.State{0n, +table, +order, +life, +counts, +cb}: Empty.absurd(ok(V, Pub.purge(String, V, C.State{0n, table, order, life, counts, cb})), Routing.false_true(Access.get_positive(~String, ~Codec.string_encode, V, C.State{0n, table, order, life, counts, cb}, valid)))
    case C.State{1n+n, +table, +order, +life, +counts, +cb}: ({==}, disabled)

def set_lifetime_ok(-V: Data, +c: C.Cache<String, V>, +ns: T.Int64, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.set_lifetime(String, V, c, ns)):
  (ConfigRep.string_set_lifetime(V, c, ns, valid), Equal.trans(Bool, Disabled.flag(String, V, C.set_lifetime(String, V, c, ns)), Disabled.flag(String, V, c), False{}, Disabled.set_lifetime(String, V, c, ns), disabled))

def cleared_ok(-V: Data, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> ok(V, C.clear_metrics(String, V, c)):
  (ConfigRep.clear_metrics(~String, ~Codec.string_encode, V, c, valid), Equal.trans(Bool, Disabled.flag(String, V, C.clear_metrics(String, V, c)), Disabled.flag(String, V, c), False{}, Disabled.clear_metrics(String, V, c), disabled))

# ---------------------------------------------------------------------------
# The oldest-prefix expiry walk.
def expire_decide_ok(-V: Data, +zero_value: V, +p: Nat, +shape: Pub.Shape<String>, +tail: List<&2, Clock.ClockEvent>, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, next: @c2: C.Cache<String, V> -> @safe2: ok(V, c2) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, c2, p, shape))), expired: Bool) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_decide(String, V, zero_value, c, p, shape, expired))):
  match expired:
    case False{}: finished_ok(V, zero_value, tail, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), (valid, disabled))
    case True{}:
      next(C.step_cache(String, V, C.remove_oldest(String, V, c, False{})), oldest_removed_ok(V, c, False{}, valid, disabled))

def expire_sampled_ok(-V: Data, +zero_value: V, +p: Nat, +shape: Pub.Shape<String>, +tail: List<&2, Clock.ClockEvent>, +now: T.Int64, +c: C.Cache<String, V>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, next: @c2: C.Cache<String, V> -> @safe2: ok(V, c2) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, c2, p, shape))), entry: Maybe<&2, T.Entry<String, V>>) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_sampled(String, V, zero_value, c, p, shape, now, entry))):
  match entry:
    case None{}: finished_ok(V, zero_value, tail, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), (valid, disabled))
    case Some{T.Item{k, v, +d}}: expire_decide_ok(V, zero_value, p, shape, tail, c, valid, disabled, next, Time.expired(d, now))

def expire_life_ok(-V: Data, +zero_value: V, +p: Nat, +c: C.Cache<String, V>, +shape: Pub.Shape<String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, next: @tail: List<&2, Clock.ClockEvent> -> @c2: C.Cache<String, V> -> @safe2: ok(V, c2) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, c2, p, shape))), immortal: Bool, events: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.expire_lifetime(String, V, zero_value, c, p, shape, immortal))):
  match immortal:
    case True{}: finished_ok(V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), (valid, disabled))
    case False{}:
      match events:
        case Nil{}: (valid, disabled)
        case Con{Clock.InvalidSample{reason}, tail}: (valid, disabled)
        case Con{Clock.ProviderException{reason}, tail}: (valid, disabled)
        case Con{Clock.Sample{+now}, +tail}:
          %Equal.sym(C.Cache<String, V>, D.cache(String, V, D.bump(String, V, D.drive(String, V, zero_value, tail, Pub.expire_sampled(String, V, zero_value, c, p, shape, now, C.oldest_entry(String, V, c))))), D.cache(String, V, D.drive(String, V, zero_value, tail, Pub.expire_sampled(String, V, zero_value, c, p, shape, now, C.oldest_entry(String, V, c)))), bump_cache(V, D.drive(String, V, zero_value, tail, Pub.expire_sampled(String, V, zero_value, c, p, shape, now, C.oldest_entry(String, V, c))))) : ok(V, _)
          expire_sampled_ok(V, zero_value, p, shape, tail, now, c, valid, disabled, next(tail), C.oldest_entry(String, V, c))

def expire_entry_ok(-V: Data, +zero_value: V, +p: Nat, +events: List<&2, Clock.ClockEvent>, +c: C.Cache<String, V>, +shape: Pub.Shape<String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, next: @tail: List<&2, Clock.ClockEvent> -> @c2: C.Cache<String, V> -> @safe2: ok(V, c2) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.expire_next(String, V, zero_value, c2, p, shape))), entry: Maybe<&2, T.Entry<String, V>>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.expire_entry(String, V, zero_value, c, p, shape, entry))):
  match entry:
    case None{}: finished_ok(V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), (valid, disabled))
    case Some{T.Item{k, v, +d}}: expire_life_ok(V, zero_value, p, c, shape, valid, disabled, next, Time.is_zero(d), events)

def expire_ok(-V: Data, +zero_value: V, rem: Nat, +events: List<&2, Clock.ClockEvent>, +c: C.Cache<String, V>, +shape: Pub.Shape<String>, safe: ok(V, c)) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.expire_next(String, V, zero_value, c, rem, shape))):
  match rem:
    case 0n: finished_ok(V, zero_value, events, c, Pub.shaped(String, V, zero_value, c, None{}, False{}, shape), safe)
    case 1n++p:
      (+valid, +disabled) = safe
      expire_entry_ok(V, zero_value, p, events, c, shape, valid, disabled, tail => c2 => safe2 => expire_ok(V, zero_value, p, tail, c2, shape, safe2), C.oldest_entry(String, V, c))

# ---------------------------------------------------------------------------
# Reads (Get/Peek/Contains and the captured GetOldest read).
def read_resumed_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +now: T.Int64, +tail: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, Pub.ReadWait{c, code, tracked, shape}, now))):
  step_finished_ok(V, zero_value, tail, C.read_encoded(String, V, c, code, now, tracked), shape, read_ok(V, c, code, now, tracked, valid, disabled))

def read_life_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<String>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, immortal: Bool, events: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.read_lifetime(String, V, zero_value, c, code, tracked, shape, immortal))):
  match immortal:
    case True{}: step_finished_ok(V, zero_value, events, C.read_encoded(String, V, c, code, Pub.zero_time(), tracked), shape, read_ok(V, c, code, Pub.zero_time(), tracked, valid, disabled))
    case False{}: waiting_ok(V, zero_value, Pub.ReadWait{c, code, tracked, shape}, (valid, disabled), now => tail => read_resumed_ok(V, zero_value, c, code, tracked, shape, valid, disabled, now, tail), events)

def read_found_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, found: Maybe<&2, T.Entry<String, V>>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.read_found(String, V, zero_value, c, code, tracked, shape, found))):
  match found:
    case None{}: step_finished_ok(V, zero_value, events, C.read_encoded(String, V, c, code, Pub.zero_time(), tracked), shape, read_ok(V, c, code, Pub.zero_time(), tracked, valid, disabled))
    case Some{T.Item{k, v, +d}}: read_life_ok(V, zero_value, c, code, tracked, shape, valid, disabled, Time.is_zero(d), events)

def read_path_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +tracked: Bool, +shape: Pub.Shape<String>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.read(String, V, zero_value, c, code, tracked, shape))):
  read_found_ok(V, zero_value, c, code, tracked, shape, events, valid, disabled, C.lookup(String, V, c, code))

# Add: the pre-clock preparation is retained on failure; the store otherwise.
def add_resumed_ok(-V: Data, +zero_value: V, +c1: C.Cache<String, V>, +code: String, +key: String, +value: V, +ns: T.Int64, +evicted: Bool, stored: @now: T.Int64 -> @life: T.Int64 -> ok(V, C.step_cache(String, V, C.store(String, V, c1, code, key, value, Time.deadline(now, life), evicted, Nil{}))), +now: T.Int64, +tail: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, Pub.AddWait{c1, code, key, value, ns, evicted}, now))):
  step_finished_ok(V, zero_value, tail, C.store(String, V, c1, code, key, value, Time.deadline(now, ns), evicted, Nil{}), Pub.Flag{}, stored(now, ns))

def add_life_ok(-V: Data, +zero_value: V, +c1: C.Cache<String, V>, +code: String, +key: String, +value: V, +ns: T.Int64, +evicted: Bool, prepared: ok(V, c1), stored: @now: T.Int64 -> @life: T.Int64 -> ok(V, C.step_cache(String, V, C.store(String, V, c1, code, key, value, Time.deadline(now, life), evicted, Nil{}))), immortal: Bool, events: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.add_lifetime(String, V, zero_value, c1, code, key, value, ns, evicted, immortal))):
  match immortal:
    case True{}: step_finished_ok(V, zero_value, events, C.store(String, V, c1, code, key, value, Pub.zero_time(), evicted, Nil{}), Pub.Flag{}, stored(Pub.zero_time(), Pub.zero_time()))
    case False{}: waiting_ok(V, zero_value, Pub.AddWait{c1, code, key, value, ns, evicted}, prepared, now => tail => add_resumed_ok(V, zero_value, c1, code, key, value, ns, evicted, stored, now, tail), events)

def add_prepared_ok(-V: Data, +zero_value: V, step: C.Step<String, V>, +code: String, +key: String, +value: V, +ns: T.Int64, +events: List<&2, Clock.ClockEvent>, prepared: ok(V, C.step_cache(String, V, step)), stored: @now: T.Int64 -> @life: T.Int64 -> ok(V, C.step_cache(String, V, PublicAdd.prepared_store(String, V, step, code, key, value, Time.deadline(now, life))))) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.add_prepared(String, V, zero_value, step, code, key, value, ns))):
  C.Out{+c1, item, +evicted, evs} = step
  add_life_ok(V, zero_value, c1, code, key, value, ns, evicted, prepared, stored, Time.is_zero(ns), events)

def stored_at(-V: Data, +c: C.Cache<String, V>, +key: String, +value: V, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +now: T.Int64, +life: T.Int64) -> ok(V, C.step_cache(String, V, PublicAdd.prepared_store(String, V, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, Time.deadline(now, life)))):
  stored_ok(V, c, key, value, life, now, valid, disabled)

def add_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +key: String, +value: V, +ns: T.Int64, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.add_with_lifetime(String, V, zero_value, c, key, key, value, ns))):
  add_prepared_ok(V, zero_value, Pub.prepare_found(String, V, c, C.lookup(String, V, c, key)), key, Pub.retained_key(String, V, key, C.lookup(String, V, c, key)), value, ns, events, prepared_ok(V, c, valid, disabled, C.lookup(String, V, c, key)), now => life => stored_at(V, c, key, value, valid, disabled, now, life))

# GetAndRefresh: the pre-clock hit/recency state is retained on failure.
def refresh_resumed_ok(-V: Data, +zero_value: V, +c1: C.Cache<String, V>, +code: String, +k: String, +v: V, +d: T.Int64, +ns: T.Int64, refreshed: @now: T.Int64 -> @life: T.Int64 -> ok(V, Entry.refresh_at(String, V, c1, code, T.Item{k, v, d}, life, now)), +now: T.Int64, +tail: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, tail, Pub.resume(String, V, zero_value, Pub.RefreshWait{c1, code, T.Item{k, v, d}, ns}, now))):
  finished_ok(V, zero_value, tail, Entry.refresh_at(String, V, c1, code, T.Item{k, v, d}, ns, now), Pub.Value{v, True{}}, refreshed(now, ns))

def refresh_life_ok(-V: Data, +zero_value: V, +c1: C.Cache<String, V>, +code: String, +k: String, +v: V, +d: T.Int64, +ns: T.Int64, prepared: ok(V, c1), refreshed: @now: T.Int64 -> @life: T.Int64 -> ok(V, Entry.refresh_at(String, V, c1, code, T.Item{k, v, d}, life, now)), immortal: Bool, events: List<&2, Clock.ClockEvent>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.refresh_lifetime(String, V, c1, code, T.Item{k, v, d}, ns, immortal))):
  match immortal:
    case True{}: finished_ok(V, zero_value, events, Entry.refresh_at(String, V, c1, code, T.Item{k, v, d}, Pub.zero_time(), Pub.zero_time()), Pub.Value{v, True{}}, refreshed(Pub.zero_time(), Pub.zero_time()))
    case False{}: waiting_ok(V, zero_value, Pub.RefreshWait{c1, code, T.Item{k, v, d}, ns}, prepared, now => tail => refresh_resumed_ok(V, zero_value, c1, code, k, v, d, ns, refreshed, now, tail), events)

def refreshed_at(-V: Data, +c: C.Cache<String, V>, +code: String, +c1: C.Cache<String, V>, +k: String, +v: V, +d: T.Int64, +evs: List<&2, T.LruEvent<String, V>>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, +eq: {Entry.refresh_prepare(String, V, c, code) == C.Out{c1, Some{T.Item{k, v, d}}, True{}, evs} : C.Step<String, V>}, +now: T.Int64, +life: T.Int64) -> ok(V, Entry.refresh_at(String, V, c1, code, T.Item{k, v, d}, life, now)):
  %eq : ok(V, Entry.refresh_at(String, V, C.step_cache(String, V, _), code, T.Item{k, v, d}, life, now))
  refreshed_ok(V, c, code, T.Item{k, v, d}, life, now, valid, disabled, Equal.cong(C.Step<String, V>, Maybe<&2, T.Entry<String, V>>, st => RefreshLookup.item(String, V, st), Entry.refresh_prepare(String, V, c, code), C.Out{c1, Some{T.Item{k, v, d}}, True{}, evs}, eq))

def refresh_step_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +ns: T.Int64, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, step: C.Step<String, V>, +eq: {Entry.refresh_prepare(String, V, c, code) == step : C.Step<String, V>}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.refresh_prepared(String, V, zero_value, code, ns, step))):
  match step:
    case C.Out{+c1, None{}, +flag, +evs}:
      finished_ok(V, zero_value, events, c1, Pub.Value{zero_value, False{}}, %eq : ok(V, C.step_cache(String, V, _)) refresh_prepared_ok(V, c, code, valid, disabled))
    case C.Out{+c1, Some{T.Item{+k, +v, +d}}, False{}, +evs}:
      finished_ok(V, zero_value, events, c1, Pub.Value{zero_value, False{}}, %eq : ok(V, C.step_cache(String, V, _)) refresh_prepared_ok(V, c, code, valid, disabled))
    case C.Out{+c1, Some{T.Item{+k, +v, +d}}, True{}, +evs}:
      refresh_life_ok(V, zero_value, c1, code, k, v, d, ns, %eq : ok(V, C.step_cache(String, V, _)) refresh_prepared_ok(V, c, code, valid, disabled), now => life => refreshed_at(V, c, code, c1, k, v, d, evs, valid, disabled, eq, now, life), Time.is_zero(ns), events)

def refresh_path_ok(-V: Data, +zero_value: V, +c: C.Cache<String, V>, +code: String, +ns: T.Int64, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.refresh(String, V, zero_value, c, code, ns))):
  refresh_step_ok(V, zero_value, c, code, ns, events, valid, disabled, Entry.refresh_prepare(String, V, c, code), {==})

# ---------------------------------------------------------------------------
def removed_step_ok(-V: Data, +zero_key: String, +zero_value: V, +events: List<&2, Clock.ClockEvent>, step: C.Step<String, V>, safe: ok(V, C.step_cache(String, V, step))) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.removed_oldest(String, V, zero_key, zero_value, step))):
  C.Out{+c, +item, +flag, evs} = step
  finished_ok(V, zero_value, events, c, Pub.Oldest{Pub.item_key(String, V, zero_key, item, flag), Pub.item_value(String, V, zero_value, item, flag), flag}, safe)

def oldest_found_ok(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +code: String, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, found: Maybe<&2, T.Entry<String, V>>) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.oldest_found(String, V, zero_key, zero_value, c, code, found))):
  match found:
    case None{}: finished_ok(V, zero_value, events, c, Pub.Oldest{zero_key, zero_value, False{}}, (valid, disabled))
    case Some{T.Item{+k, v, d}}: read_path_ok(V, zero_value, c, code, False{}, Pub.Captured{k}, events, valid, disabled)

def get_oldest_ok(-V: Data, +zero_key: String, +zero_value: V, c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.get_oldest(String, V, zero_key, zero_value, c))):
  match c:
    case C.State{+cap, +table, Nil{}, +life, +counts, +cb}: finished_ok(V, zero_value, events, C.State{cap, table, Nil{}, life, counts, cb}, Pub.Oldest{zero_key, zero_value, False{}}, (valid, disabled))
    case C.State{+cap, +table, Con{+code, +rest}, +life, +counts, +cb}: oldest_found_ok(V, zero_key, zero_value, C.State{cap, table, Con{code, rest}, life, counts, cb}, code, events, valid, disabled, C.lookup(String, V, C.State{cap, table, Con{code, rest}, life, counts, cb}, code))

def add_plain_ok(-V: Data, +zero_value: V, c: C.Cache<String, V>, +key: String, +value: V, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}) -> outcome_ok(V, D.drive(String, V, zero_value, events, Pub.add(String, V, zero_value, c, key, key, value))):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  add_ok(V, zero_value, C.State{cap, table, order, life, counts, cb}, key, value, life, events, valid, disabled)

# Every public request from a safe cache ends in a safe cache, including the
# retained state after provider exceptions, invalid samples and exhaustion.
def request_ok(-V: Data, +zero_key: String, +zero_value: V, +c: C.Cache<String, V>, +events: List<&2, Clock.ClockEvent>, +valid: {Inv.representation(~String, ~Codec.string_encode, V, c) == True{} : Bool}, +disabled: {Disabled.flag(String, V, c) == False{} : Bool}, request: Pub.Request<String, V>) -> outcome_ok(V, D.execute(~String, ~Codec.string_encode, V, zero_key, zero_value, c, events, request)):
  match request:
    case Pub.Add{+k, +v}: add_plain_ok(V, zero_value, c, k, v, events, valid, disabled)
    case Pub.AddWithLifetime{+k, +v, +ns}: add_ok(V, zero_value, c, k, v, ns, events, valid, disabled)
    case Pub.Get{+k}: read_path_ok(V, zero_value, c, k, True{}, Pub.ValueOnly{}, events, valid, disabled)
    case Pub.GetAndRefresh{+k, +ns}: refresh_path_ok(V, zero_value, c, k, ns, events, valid, disabled)
    case Pub.Peek{+k}: read_path_ok(V, zero_value, c, k, False{}, Pub.ValueOnly{}, events, valid, disabled)
    case Pub.Contains{+k}: read_path_ok(V, zero_value, c, k, False{}, Pub.Flag{}, events, valid, disabled)
    case Pub.Remove{+k}: step_finished_ok(V, zero_value, events, C.remove(String, V, Codec.string_encode, c, k), Pub.Flag{}, removed_ok(V, c, k, valid, disabled))
    case Pub.RemoveOldest{}: removed_step_ok(V, zero_key, zero_value, events, C.remove_oldest(String, V, c, False{}), oldest_removed_ok(V, c, False{}, valid, disabled))
    case Pub.GetOldest{}: get_oldest_ok(V, zero_key, zero_value, c, events, valid, disabled)
    case Pub.Keys{}: expire_ok(V, zero_value, C.len(String, V, c), events, c, Pub.AllKeys{}, (valid, disabled))
    case Pub.Values{}: expire_ok(V, zero_value, C.len(String, V, c), events, c, Pub.AllValues{}, (valid, disabled))
    case Pub.Purge{}: finished_ok(V, zero_value, events, Pub.purge(String, V, c), Pub.Empty{}, purge_ok(V, c, valid, disabled))
    case Pub.PurgeExpired{}: expire_ok(V, zero_value, C.len(String, V, c), events, c, Pub.Nothing{}, (valid, disabled))
    case Pub.Len{}: finished_ok(V, zero_value, events, c, Pub.Length{C.len(String, V, c)}, (valid, disabled))
    case Pub.SetLifetime{+ns}: finished_ok(V, zero_value, events, C.set_lifetime(String, V, c, ns), Pub.Empty{}, set_lifetime_ok(V, c, ns, valid, disabled))
    case Pub.Metrics{}: finished_ok(V, zero_value, events, c, Pub.Counters{C.metrics(String, V, c)}, (valid, disabled))
    case Pub.ResetMetrics{}: finished_ok(V, zero_value, events, C.clear_metrics(String, V, c), Pub.Counters{C.metrics(String, V, c)}, cleared_ok(V, c, valid, disabled))
    case Pub.Diagnostics{}: finished_ok(V, zero_value, events, c, Pub.Storage{C.map_size(String, V, c), C.len(String, V, c), C.capacity(String, V, c), C.metrics(String, V, c)}, (valid, disabled))
