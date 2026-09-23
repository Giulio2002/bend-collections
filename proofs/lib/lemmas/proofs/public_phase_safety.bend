import Base
import ./representation_parts.bend as Parts
import ./removal_representation.bend as Removal
import ./read_representation.bend as Read
import ./aggregate_representation.bend as Aggregate
import ./refresh_representation.bend as Refresh
import ./refresh_complete_representation.bend as Complete
import ./refresh_lookup.bend as Lookup
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/codec.bend as Codec
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./disabled.bend as D
import ./empty_events.bend as Events
import ./configuration_representation.bend as Config
import ./add_representation.bend as Add
import ./cache_key_identity.bend as Key

# Joint obligations needed at actual adapter commit boundaries. These laws reach
# existing cache/protocol functions; they do not assume the TypeScript bridge.
def safe_cache(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>) -> Type:
  {Inv.representation(~K, ~encode, V, c) == True{} : Bool} & {D.flag(K, V, c) == False{} : Bool}

def safe_step(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>) -> Type:
  safe_cache(~K, ~encode, V, C.step_cache(K, V, result)) & Events.empty(K, V, result)

def representation(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, facts: safe_cache(~K, ~encode, V, c)) -> {Inv.representation(~K, ~encode, V, c) == True{} : Bool}:
  (invariant, disabled) = facts
  invariant

def disabled(~K: Data, ~encode: K -> String, -V: Data, c: C.Cache<K, V>, facts: safe_cache(~K, ~encode, V, c)) -> {D.flag(K, V, c) == False{} : Bool}:
  (invariant, flag) = facts
  flag

def committed(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, facts: safe_step(~K, ~encode, V, result)) -> safe_cache(~K, ~encode, V, C.step_cache(K, V, result)):
  (state, events) = facts
  state

def pack(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, invariant: {Inv.representation(~K, ~encode, V, C.step_cache(K, V, result)) == True{} : Bool}, flag: {D.step_flag(K, V, result) == False{} : Bool}, events: Events.empty(K, V, result)) -> safe_step(~K, ~encode, V, result):
  C.Out{c, item, present, evs} = result
  ((invariant, flag), events)

def finish_removal(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +evict: Bool, facts: safe_cache(~K, ~encode, V, c)) -> safe_cache(~K, ~encode, V, P.finish_removal(K, V, c, evict)):
  (invariant, flag) = facts
  (Config.finish_removal(~K, ~encode, V, c, evict, invariant), Equal.trans(Bool, D.flag(K, V, P.finish_removal(K, V, c, evict)), D.flag(K, V, c), False{}, D.finish_removal(K, V, c, evict), flag))

def finish_detached(~K: Data, ~encode: K -> String, -V: Data, result: C.Step<K, V>, evict: Bool, facts: safe_step(~K, ~encode, V, result)) -> safe_step(~K, ~encode, V, P.finish_detached(K, V, result, evict)):
  C.Out{c, item, flag, events} = result
  match flag:
    case False{}: facts
    case True{}:
      (state, empty) = facts
      (finish_removal(~K, ~encode, V, c, evict, state), empty)

def prepare_add(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, P.prepare_add(K, V, c, code)):
  (invariant, +flag) = facts
  pack(~K, ~encode, V, P.prepare_add(K, V, c, code), Config.prepare_add(~K, ~encode, V, c, code, invariant), Equal.trans(Bool, D.step_flag(K, V, P.prepare_add(K, V, c, code)), D.flag(K, V, c), False{}, D.prepare_add(K, V, c, code), flag), Events.prepare_add(K, V, c, code, flag))

# Exact composition of the preparation and conditional eviction-count phase.
# The intermediate preparation itself is certified separately above, so later
# clock/provider failure cannot erase the proof of the already committed state.
def counted_preparation(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, P.finish_detached(K, V, P.prepare_add(K, V, c, code), True{})):
  finish_detached(~K, ~encode, V, P.prepare_add(K, V, c, code), True{}, prepare_add(~K, ~encode, V, c, code, facts))

def insertion(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +key: K, +value: V, +ns: T.Int64, +now: T.Int64, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now)):
  (invariant, +flag) = facts
  pack(~K, ~encode, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now), Add.add_with_lifetime(~K, ~encode, V, c, key, value, ns, now, invariant), Equal.trans(Bool, D.step_flag(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now)), D.flag(K, V, c), False{}, D.add_with_lifetime(K, V, encode, c, key, value, ns, now), flag), Events.add_with_lifetime(K, V, encode, c, key, value, ns, now, flag))

def add_after_preparation(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +key: K, value: V, ns: T.Int64, now: T.Int64, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, C.add_with_lifetime(K, V, encode, C.step_cache(K, V, P.finish_detached(K, V, P.prepare_add(K, V, c, encode(key)), True{})), key, value, ns, now)):
  insertion(~K, ~encode, V, C.step_cache(K, V, P.finish_detached(K, V, P.prepare_add(K, V, c, encode(key)), True{})), key, value, ns, now, committed(~K, ~encode, V, P.finish_detached(K, V, P.prepare_add(K, V, c, encode(key)), True{}), counted_preparation(~K, ~encode, V, c, encode(key), facts)))

def string_add(-V: Data, c: C.Cache<String, V>, key: String, value: V, ns: T.Int64, now: T.Int64, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_step(~String, ~Codec.string_encode, V, C.add_with_lifetime(String, V, Codec.string_encode, C.step_cache(String, V, P.finish_detached(String, V, P.prepare_add(String, V, c, Codec.string_encode(key)), True{})), key, value, ns, now)):
  add_after_preparation(~String, ~Codec.string_encode, V, c, key, value, ns, now, facts)

def integer_add(-V: Data, c: C.Cache<T.Integer, V>, key: T.Integer, value: V, ns: T.Int64, now: T.Int64, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_step(~T.Integer, ~Codec.integer_encode, V, C.add_with_lifetime(T.Integer, V, Codec.integer_encode, C.step_cache(T.Integer, V, P.finish_detached(T.Integer, V, P.prepare_add(T.Integer, V, c, Codec.integer_encode(key)), True{})), key, value, ns, now)):
  add_after_preparation(~T.Integer, ~Codec.integer_encode, V, c, key, value, ns, now, facts)

def word64_add(-V: Data, c: C.Cache<Word(64n), V>, key: Word(64n), value: V, ns: T.Int64, now: T.Int64, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_step(~Word(64n), ~Key.word64_encode, V, C.add_with_lifetime(Word(64n), V, Key.word64_encode, C.step_cache(Word(64n), V, P.finish_detached(Word(64n), V, P.prepare_add(Word(64n), V, c, Key.word64_encode(key)), True{})), key, value, ns, now)):
  add_after_preparation(~Word(64n), ~Key.word64_encode, V, c, key, value, ns, now, facts)

def prepare_refresh(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, P.refresh_prepare(K, V, c, code)):
  (invariant, flag) = facts
  pack(~K, ~encode, V, P.refresh_prepare(K, V, c, code), Refresh.prepare(~K, ~encode, V, c, code, invariant), Equal.trans(Bool, D.step_flag(K, V, P.refresh_prepare(K, V, c, code)), D.flag(K, V, c), False{}, D.refresh_prepare(K, V, c, code), flag), Events.refresh_prepare(K, V, c, code))

def refresh_at(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, +ns: T.Int64, +now: T.Int64, facts: safe_cache(~K, ~encode, V, c), found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> safe_cache(~K, ~encode, V, P.refresh_at(K, V, c, code, entry, ns, now)):
  (invariant, flag) = facts
  (Complete.at(~K, ~encode, V, c, code, entry, ns, now, found, invariant), Equal.trans(Bool, D.flag(K, V, P.refresh_at(K, V, c, code, entry, ns, now)), D.flag(K, V, c), False{}, D.refresh_at(K, V, c, code, entry, ns, now), flag))

# Success requires the actual prepared item, not an arbitrary assumed binding.
def refresh_after_preparation(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>, ns: T.Int64, now: T.Int64, facts: safe_cache(~K, ~encode, V, c), returned: {Lookup.item(K, V, P.refresh_prepare(K, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<K, V>>}) -> safe_cache(~K, ~encode, V, P.refresh_at(K, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, ns, now)):
  refresh_at(~K, ~encode, V, C.step_cache(K, V, P.refresh_prepare(K, V, c, code)), code, entry, ns, now, committed(~K, ~encode, V, P.refresh_prepare(K, V, c, code), prepare_refresh(~K, ~encode, V, c, code, facts)), Lookup.successful_prepare(K, V, c, code, entry, returned))

def string_refresh(-V: Data, c: C.Cache<String, V>, code: String, entry: T.Entry<String, V>, ns: T.Int64, now: T.Int64, facts: safe_cache(~String, ~Codec.string_encode, V, c), returned: {Lookup.item(String, V, P.refresh_prepare(String, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<String, V>>}) -> safe_cache(~String, ~Codec.string_encode, V, P.refresh_at(String, V, C.step_cache(String, V, P.refresh_prepare(String, V, c, code)), code, entry, ns, now)):
  refresh_after_preparation(~String, ~Codec.string_encode, V, c, code, entry, ns, now, facts, returned)

def integer_refresh(-V: Data, c: C.Cache<T.Integer, V>, code: String, entry: T.Entry<T.Integer, V>, ns: T.Int64, now: T.Int64, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c), returned: {Lookup.item(T.Integer, V, P.refresh_prepare(T.Integer, V, c, code)) == Some{entry} : Maybe<&2, T.Entry<T.Integer, V>>}) -> safe_cache(~T.Integer, ~Codec.integer_encode, V, P.refresh_at(T.Integer, V, C.step_cache(T.Integer, V, P.refresh_prepare(T.Integer, V, c, code)), code, entry, ns, now)):
  refresh_after_preparation(~T.Integer, ~Codec.integer_encode, V, c, code, entry, ns, now, facts, returned)

def word64_refresh(-V: Data, c: C.Cache<Word(64n), V>, code: String, entry: T.Entry<Word(64n), V>, ns: T.Int64, now: T.Int64, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c), returned: {Lookup.item(Word(64n), V, P.refresh_prepare(Word(64n), V, c, code)) == Some{entry} : Maybe<&2, T.Entry<Word(64n), V>>}) -> safe_cache(~Word(64n), ~Key.word64_encode, V, P.refresh_at(Word(64n), V, C.step_cache(Word(64n), V, P.refresh_prepare(Word(64n), V, c, code)), code, entry, ns, now)):
  refresh_after_preparation(~Word(64n), ~Key.word64_encode, V, c, code, entry, ns, now, facts, returned)

def read_step(-K: Data, -V: Data, pending: P.Read<K, V>) -> C.Step<K, V>:
  P.Reading{result, removed} = pending
  result

def read_pack(~K: Data, ~encode: K -> String, -V: Data, pending: P.Read<K, V>, invariant: {Inv.representation(~K, ~encode, V, Read.read_cache(K, V, pending)) == True{} : Bool}, flag: {D.read_flag(K, V, pending) == False{} : Bool}, events: Events.read_empty(K, V, pending)) -> safe_step(~K, ~encode, V, read_step(K, V, pending)):
  P.Reading{result, removed} = pending
  pack(~K, ~encode, V, result, invariant, flag, events)

def read(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, +now: T.Int64, +tracked: Bool, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, read_step(K, V, P.read(K, V, c, code, now, tracked))):
  (invariant, +flag) = facts
  read_pack(~K, ~encode, V, P.read(K, V, c, code, now, tracked), Read.protocol_read(~K, ~encode, V, c, code, now, tracked, invariant), Equal.trans(Bool, D.read_flag(K, V, P.read(K, V, c, code, now, tracked)), D.flag(K, V, c), False{}, D.read(K, V, c, code, now, tracked), flag), Events.read(K, V, c, code, now, tracked, flag))

def finish_miss(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +tracked: Bool, facts: safe_cache(~K, ~encode, V, c)) -> safe_cache(~K, ~encode, V, P.finish_miss(K, V, c, tracked)):
  (invariant, flag) = facts
  (Config.finish_miss(~K, ~encode, V, c, tracked, invariant), Equal.trans(Bool, D.flag(K, V, P.finish_miss(K, V, c, tracked)), D.flag(K, V, c), False{}, D.finish_miss(K, V, c, tracked), flag))

def expired_read_counters(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, tracked: Bool, facts: safe_cache(~K, ~encode, V, c)) -> safe_cache(~K, ~encode, V, P.finish_miss(K, V, P.finish_removal(K, V, c, False{}), tracked)):
  finish_miss(~K, ~encode, V, P.finish_removal(K, V, c, False{}), tracked, finish_removal(~K, ~encode, V, c, False{}, facts))

def safe_aggregate(~K: Data, ~encode: K -> String, -V: Data, result: P.Aggregate<K, V>) -> Type:
  safe_cache(~K, ~encode, V, Aggregate.cache(K, V, result)) & Events.aggregate_empty(K, V, result)

def aggregate_pack(~K: Data, ~encode: K -> String, -V: Data, result: P.Aggregate<K, V>, invariant: {Inv.representation(~K, ~encode, V, Aggregate.cache(K, V, result)) == True{} : Bool}, flag: {D.aggregate_flag(K, V, result) == False{} : Bool}, events: Events.aggregate_empty(K, V, result)) -> safe_aggregate(~K, ~encode, V, result):
  match result:
    case P.Complete{c, keys, values}: ((invariant, flag), events)
    case P.NeedClock{c, remaining, kind}: ((invariant, flag), events)
    case P.RemovalReady{C.Out{c, item, found, evs}, remaining, kind}: ((invariant, flag), events)

def aggregate_next(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +remaining: Nat, +kind: P.Mode, facts: safe_cache(~K, ~encode, V, c)) -> safe_aggregate(~K, ~encode, V, P.aggregate_next(K, V, remaining, c, kind)):
  (invariant, +flag) = facts
  aggregate_pack(~K, ~encode, V, P.aggregate_next(K, V, remaining, c, kind), Aggregate.next(~K, ~encode, V, remaining, c, kind, invariant), Equal.trans(Bool, D.aggregate_flag(K, V, P.aggregate_next(K, V, remaining, c, kind)), D.flag(K, V, c), False{}, D.aggregate_next(K, V, remaining, c, kind), flag), Events.aggregate_next(K, V, remaining, c, kind, flag))

def after_removal(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +remaining: Nat, +kind: P.Mode, facts: safe_cache(~K, ~encode, V, c)) -> safe_aggregate(~K, ~encode, V, P.after_removal(K, V, remaining, c, kind)):
  (invariant, +flag) = facts
  aggregate_pack(~K, ~encode, V, P.after_removal(K, V, remaining, c, kind), Aggregate.after_removal(~K, ~encode, V, remaining, c, kind, invariant), Equal.trans(Bool, D.aggregate_flag(K, V, P.after_removal(K, V, remaining, c, kind)), D.flag(K, V, c), False{}, D.after_removal(K, V, remaining, c, kind), flag), Events.after_removal(K, V, remaining, c, kind, flag))

def after_clock(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +remaining: Nat, +kind: P.Mode, +now: T.Int64, facts: safe_cache(~K, ~encode, V, c)) -> safe_aggregate(~K, ~encode, V, P.after_clock(K, V, c, remaining, kind, now)):
  (invariant, +flag) = facts
  aggregate_pack(~K, ~encode, V, P.after_clock(K, V, c, remaining, kind, now), Aggregate.after_clock(~K, ~encode, V, c, remaining, kind, now, invariant), Equal.trans(Bool, D.aggregate_flag(K, V, P.after_clock(K, V, c, remaining, kind, now)), D.flag(K, V, c), False{}, D.after_clock(K, V, c, remaining, kind, now), flag), Events.after_clock(K, V, c, remaining, kind, now, flag))

def string_aggregate_next(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_aggregate(~String, ~Codec.string_encode, V, P.aggregate_next(String, V, remaining, c, kind)):
  aggregate_next(~String, ~Codec.string_encode, V, c, remaining, kind, facts)

def string_after_removal(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_aggregate(~String, ~Codec.string_encode, V, P.after_removal(String, V, remaining, c, kind)):
  after_removal(~String, ~Codec.string_encode, V, c, remaining, kind, facts)

def string_after_clock(-V: Data, c: C.Cache<String, V>, remaining: Nat, kind: P.Mode, now: T.Int64, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_aggregate(~String, ~Codec.string_encode, V, P.after_clock(String, V, c, remaining, kind, now)):
  after_clock(~String, ~Codec.string_encode, V, c, remaining, kind, now, facts)

def string_read(-V: Data, c: C.Cache<String, V>, code: String, now: T.Int64, tracked: Bool, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_step(~String, ~Codec.string_encode, V, read_step(String, V, P.read(String, V, c, code, now, tracked))):
  read(~String, ~Codec.string_encode, V, c, code, now, tracked, facts)

def string_expired_counters(-V: Data, c: C.Cache<String, V>, tracked: Bool, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_cache(~String, ~Codec.string_encode, V, P.finish_miss(String, V, P.finish_removal(String, V, c, False{}), tracked)):
  expired_read_counters(~String, ~Codec.string_encode, V, c, tracked, facts)

def integer_aggregate_next(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_aggregate(~T.Integer, ~Codec.integer_encode, V, P.aggregate_next(T.Integer, V, remaining, c, kind)):
  aggregate_next(~T.Integer, ~Codec.integer_encode, V, c, remaining, kind, facts)

def integer_after_removal(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_aggregate(~T.Integer, ~Codec.integer_encode, V, P.after_removal(T.Integer, V, remaining, c, kind)):
  after_removal(~T.Integer, ~Codec.integer_encode, V, c, remaining, kind, facts)

def integer_after_clock(-V: Data, c: C.Cache<T.Integer, V>, remaining: Nat, kind: P.Mode, now: T.Int64, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_aggregate(~T.Integer, ~Codec.integer_encode, V, P.after_clock(T.Integer, V, c, remaining, kind, now)):
  after_clock(~T.Integer, ~Codec.integer_encode, V, c, remaining, kind, now, facts)

def integer_read(-V: Data, c: C.Cache<T.Integer, V>, code: String, now: T.Int64, tracked: Bool, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_step(~T.Integer, ~Codec.integer_encode, V, read_step(T.Integer, V, P.read(T.Integer, V, c, code, now, tracked))):
  read(~T.Integer, ~Codec.integer_encode, V, c, code, now, tracked, facts)

def integer_expired_counters(-V: Data, c: C.Cache<T.Integer, V>, tracked: Bool, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_cache(~T.Integer, ~Codec.integer_encode, V, P.finish_miss(T.Integer, V, P.finish_removal(T.Integer, V, c, False{}), tracked)):
  expired_read_counters(~T.Integer, ~Codec.integer_encode, V, c, tracked, facts)

def word64_aggregate_next(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_aggregate(~Word(64n), ~Key.word64_encode, V, P.aggregate_next(Word(64n), V, remaining, c, kind)):
  aggregate_next(~Word(64n), ~Key.word64_encode, V, c, remaining, kind, facts)

def word64_after_removal(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_aggregate(~Word(64n), ~Key.word64_encode, V, P.after_removal(Word(64n), V, remaining, c, kind)):
  after_removal(~Word(64n), ~Key.word64_encode, V, c, remaining, kind, facts)

def word64_after_clock(-V: Data, c: C.Cache<Word(64n), V>, remaining: Nat, kind: P.Mode, now: T.Int64, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_aggregate(~Word(64n), ~Key.word64_encode, V, P.after_clock(Word(64n), V, c, remaining, kind, now)):
  after_clock(~Word(64n), ~Key.word64_encode, V, c, remaining, kind, now, facts)

def word64_read(-V: Data, c: C.Cache<Word(64n), V>, code: String, now: T.Int64, tracked: Bool, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_step(~Word(64n), ~Key.word64_encode, V, read_step(Word(64n), V, P.read(Word(64n), V, c, code, now, tracked))):
  read(~Word(64n), ~Key.word64_encode, V, c, code, now, tracked, facts)

def word64_expired_counters(-V: Data, c: C.Cache<Word(64n), V>, tracked: Bool, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_cache(~Word(64n), ~Key.word64_encode, V, P.finish_miss(Word(64n), V, P.finish_removal(Word(64n), V, c, False{}), tracked)):
  expired_read_counters(~Word(64n), ~Key.word64_encode, V, c, tracked, facts)

def initialized(~K: Data, ~encode: K -> String, -V: Data, +n: Nat) -> safe_cache(~K, ~encode, V, C.init(K, V, 1n+n)):
  (Parts.initialized(~K, ~encode, V, n), D.initial(K, V, 1n+n))

def set_lifetime(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +ns: T.Int64, facts: safe_cache(~K, ~encode, V, c)) -> safe_cache(~K, ~encode, V, C.set_lifetime(K, V, c, ns)):
  (invariant, flag) = facts
  (Config.set_lifetime(~K, ~encode, V, c, ns, invariant), Equal.trans(Bool, D.flag(K, V, C.set_lifetime(K, V, c, ns)), D.flag(K, V, c), False{}, D.set_lifetime(K, V, c, ns), flag))

def clear_metrics(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, facts: safe_cache(~K, ~encode, V, c)) -> safe_cache(~K, ~encode, V, C.clear_metrics(K, V, c)):
  (invariant, flag) = facts
  (Config.clear_metrics(~K, ~encode, V, c, invariant), Equal.trans(Bool, D.flag(K, V, C.clear_metrics(K, V, c)), D.flag(K, V, c), False{}, D.clear_metrics(K, V, c), flag))

def string_initialized(-V: Data, n: Nat) -> safe_cache(~String, ~Codec.string_encode, V, C.init(String, V, 1n+n)):
  initialized(~String, ~Codec.string_encode, V, n)

def string_configuration(-V: Data, +c: C.Cache<String, V>, +ns: T.Int64, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_cache(~String, ~Codec.string_encode, V, C.clear_metrics(String, V, C.set_lifetime(String, V, c, ns))):
  clear_metrics(~String, ~Codec.string_encode, V, C.set_lifetime(String, V, c, ns), set_lifetime(~String, ~Codec.string_encode, V, c, ns, facts))

def integer_initialized(-V: Data, n: Nat) -> safe_cache(~T.Integer, ~Codec.integer_encode, V, C.init(T.Integer, V, 1n+n)):
  initialized(~T.Integer, ~Codec.integer_encode, V, n)

def integer_configuration(-V: Data, +c: C.Cache<T.Integer, V>, +ns: T.Int64, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_cache(~T.Integer, ~Codec.integer_encode, V, C.clear_metrics(T.Integer, V, C.set_lifetime(T.Integer, V, c, ns))):
  clear_metrics(~T.Integer, ~Codec.integer_encode, V, C.set_lifetime(T.Integer, V, c, ns), set_lifetime(~T.Integer, ~Codec.integer_encode, V, c, ns, facts))

def word64_initialized(-V: Data, n: Nat) -> safe_cache(~Word(64n), ~Key.word64_encode, V, C.init(Word(64n), V, 1n+n)):
  initialized(~Word(64n), ~Key.word64_encode, V, n)

def word64_configuration(-V: Data, +c: C.Cache<Word(64n), V>, +ns: T.Int64, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_cache(~Word(64n), ~Key.word64_encode, V, C.clear_metrics(Word(64n), V, C.set_lifetime(Word(64n), V, c, ns))):
  clear_metrics(~Word(64n), ~Key.word64_encode, V, C.set_lifetime(Word(64n), V, c, ns), set_lifetime(~Word(64n), ~Key.word64_encode, V, c, ns, facts))

def detach(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, +code: String, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, P.detach(K, V, c, code)):
  (invariant, +flag) = facts
  pack(~K, ~encode, V, P.detach(K, V, c, code), Removal.detach(~K, ~encode, V, c, code, invariant), Equal.trans(Bool, D.step_flag(K, V, P.detach(K, V, c, code)), D.flag(K, V, c), False{}, D.detach(K, V, c, code), flag), Events.detach(K, V, c, code, flag))

def string_detach(-V: Data, c: C.Cache<String, V>, code: String, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_step(~String, ~Codec.string_encode, V, P.detach(String, V, c, code)):
  detach(~String, ~Codec.string_encode, V, c, code, facts)

def integer_detach(-V: Data, c: C.Cache<T.Integer, V>, code: String, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_step(~T.Integer, ~Codec.integer_encode, V, P.detach(T.Integer, V, c, code)):
  detach(~T.Integer, ~Codec.integer_encode, V, c, code, facts)

def word64_detach(-V: Data, c: C.Cache<Word(64n), V>, code: String, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_step(~Word(64n), ~Key.word64_encode, V, P.detach(Word(64n), V, c, code)):
  detach(~Word(64n), ~Key.word64_encode, V, c, code, facts)

def detach_oldest(~K: Data, ~encode: K -> String, -V: Data, +c: C.Cache<K, V>, facts: safe_cache(~K, ~encode, V, c)) -> safe_step(~K, ~encode, V, P.detach_oldest(K, V, c)):
  (invariant, +flag) = facts
  pack(~K, ~encode, V, P.detach_oldest(K, V, c), Removal.detach_oldest(~K, ~encode, V, c, invariant), Equal.trans(Bool, D.step_flag(K, V, P.detach_oldest(K, V, c)), D.flag(K, V, c), False{}, D.detach_oldest(K, V, c), flag), Events.detach_oldest(K, V, c, flag))

def string_detach_oldest(-V: Data, c: C.Cache<String, V>, facts: safe_cache(~String, ~Codec.string_encode, V, c)) -> safe_step(~String, ~Codec.string_encode, V, P.detach_oldest(String, V, c)):
  detach_oldest(~String, ~Codec.string_encode, V, c, facts)

def integer_detach_oldest(-V: Data, c: C.Cache<T.Integer, V>, facts: safe_cache(~T.Integer, ~Codec.integer_encode, V, c)) -> safe_step(~T.Integer, ~Codec.integer_encode, V, P.detach_oldest(T.Integer, V, c)):
  detach_oldest(~T.Integer, ~Codec.integer_encode, V, c, facts)

def word64_detach_oldest(-V: Data, c: C.Cache<Word(64n), V>, facts: safe_cache(~Word(64n), ~Key.word64_encode, V, c)) -> safe_step(~Word(64n), ~Key.word64_encode, V, P.detach_oldest(Word(64n), V, c)):
  detach_oldest(~Word(64n), ~Key.word64_encode, V, c, facts)
