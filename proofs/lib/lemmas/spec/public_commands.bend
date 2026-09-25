import Base
import ../types/model.bend as T
import ./cache.bend as S
import ./operations.bend as O
import ./clock.bend as Clock
import ./effectful_operations.bend as E
import ./effectful_aggregate.bend as A

# Public callback-free observations. Metrics' storage-dependent Collisions field
# is always the documented zero/not-applicable adaptation. Diagnostics describe
# the abstract bound-entry count; refinement establishes the native leaf count.
type Reply<-K: Data, -V: Data> is Data:
  NoReply{}
  Boolean{value: Bool}
  Value{value: V, found: Bool}
  Oldest{key: K, value: V, found: Bool}
  KeyList{keys: List<&2, K>}
  ValueList{values: List<&2, V>}
  Length{length: Nat}
  Counters{metrics: T.Metrics}
  Storage{leaves: Nat, recency: Nat, capacity: Nat, metrics: T.Metrics}

type CmdResult<-K: Data, -V: Data> is Data:
  Returned{state: S.Model<K, V>, reply: Reply<K, V>, remaining: List<&2, Clock.ClockEvent>, requests: Nat}
  Failed{state: S.Model<K, V>, error: Clock.Error, remaining: List<&2, Clock.ClockEvent>, requests: Nat}

type Projection<-K: Data> is Data:
  Flag{}
  ValueOnly{}
  RemovedOldest{}
  CapturedOldest{key: K}
  Nothing{}
  Keys{}
  Values{}

def value(-K: Data, -V: Data, zero: V, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> V:
  match item present:
    case Some{T.Item{k, v, d}} True{}: v
    case x y: zero

def key(-K: Data, -V: Data, zero: K, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> K:
  match item present:
    case Some{T.Item{k, v, d}} True{}: k
    case x y: zero

def project(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, zero_key: K, zero_value: V, +item: Maybe<&2, T.Entry<K, V>>, +present: Bool, kind: Projection<K>) -> Reply<K, V>:
  match kind:
    case Flag{}: Boolean{present}
    case ValueOnly{}: Value{value(K, V, zero_value, item, present), present}
    case RemovedOldest{}: Oldest{key(K, V, zero_key, item, present), value(K, V, zero_value, item, present), present}
    case CapturedOldest{captured}: Oldest{captured, value(K, V, zero_value, item, present), present}
    case Nothing{}: NoReply{}
    case Keys{}: KeyList{O.entry_keys(K, V, O.all_entries(~K, ~same, V, s))}
    case Values{}: ValueList{O.entry_values(K, V, O.all_entries(~K, ~same, V, s))}

def observation(~K: Data, ~same: K -> K -> Bool, -V: Data, zero_key: K, zero_value: V, kind: Projection<K>, observed: S.Observation<K, V>, events: List<&2, Clock.ClockEvent>, requests: Nat) -> CmdResult<K, V>:
  S.Observed{+s, item, present, ignored} = observed
  Returned{s, project(~K, ~same, V, s, zero_key, zero_value, item, present, kind), events, requests}

def effect(~K: Data, ~same: K -> K -> Bool, -V: Data, zero_key: K, zero_value: V, kind: Projection<K>, outcome: E.Outcome<K, V>) -> CmdResult<K, V>:
  match outcome:
    case E.Failed{s, error, events, requests}: Failed{s, error, events, requests}
    case E.Returned{observed, events, requests}: observation(~K, ~same, V, zero_key, zero_value, kind, observed, events, requests)

def oldest_binding(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, zero_key: K, zero_value: V, events: List<&2, Clock.ClockEvent>, found: Maybe<&2, T.Entry<K, V>>) -> CmdResult<K, V>:
  match found:
    case None{}: Returned{s, Oldest{zero_key, zero_value, False{}}, events, 0n}
    case Some{T.Item{+original, v, d}}: effect(~K, ~same, V, zero_key, zero_value, CapturedOldest{original}, E.read(~K, ~same, V, s, original, False{}, events))

def oldest_order(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>, zero_key: K, zero_value: V, events: List<&2, Clock.ClockEvent>) -> CmdResult<K, V>:
  match order:
    case Nil{}: Returned{s, Oldest{zero_key, zero_value, False{}}, events, 0n}
    case Con{first, tail}: oldest_binding(~K, ~same, V, s, zero_key, zero_value, events, S.find(~K, ~same, V, bindings, first))

def oldest(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, zero_key: K, zero_value: V, events: List<&2, Clock.ClockEvent>) -> CmdResult<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  oldest_order(~K, ~same, V, s, bindings, order, zero_key, zero_value, events)

def metrics(-K: Data, -V: Data, +s: S.Model<K, V>, events: List<&2, Clock.ClockEvent>) -> CmdResult<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Returned{s, Counters{counts}, events, 0n}

def reset(-K: Data, -V: Data, s: S.Model<K, V>, events: List<&2, Clock.ClockEvent>) -> CmdResult<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Returned{S.Abstract{cap, bindings, order, life, T.zero_metrics(), cb}, Counters{counts}, events, 0n}

# Leaves counts the bound keys of the abstract finite map (the entries reachable
# through the recency list); it is independent of binding-list storage order.
def diagnostics(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, events: List<&2, Clock.ClockEvent>) -> CmdResult<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Returned{s, Storage{List.length(&2, T.Entry<K, V>, O.all_entries(~K, ~same, V, s)), List.length(&2, K, order), cap, counts}, events, 0n}

# All typed commands have explicit independent semantics. Invalid transport and
# rejected host arguments need a separate marshalling relation; they are not
# silently coerced into one of these legal typed commands.
def execute(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, zero_key: K, zero_value: V, events: List<&2, Clock.ClockEvent>, command: S.Command<K, V>) -> CmdResult<K, V>:
  match command:
    case S.Add{k, v}: effect(~K, ~same, V, zero_key, zero_value, Flag{}, E.add(~K, ~same, V, s, k, v, events))
    case S.AddWithLifetime{k, v, ns}: effect(~K, ~same, V, zero_key, zero_value, Flag{}, E.add_with_lifetime(~K, ~same, V, s, k, v, ns, events))
    case S.Get{k}: effect(~K, ~same, V, zero_key, zero_value, ValueOnly{}, E.read(~K, ~same, V, s, k, True{}, events))
    case S.GetAndRefresh{k, ns}: effect(~K, ~same, V, zero_key, zero_value, ValueOnly{}, E.refresh(~K, ~same, V, s, k, ns, events))
    case S.Peek{k}: effect(~K, ~same, V, zero_key, zero_value, ValueOnly{}, E.read(~K, ~same, V, s, k, False{}, events))
    case S.Contains{k}: effect(~K, ~same, V, zero_key, zero_value, Flag{}, E.read(~K, ~same, V, s, k, False{}, events))
    case S.Remove{k}: observation(~K, ~same, V, zero_key, zero_value, Flag{}, S.remove(~K, ~same, V, s, k), events, 0n)
    case S.RemoveOldest{}: observation(~K, ~same, V, zero_key, zero_value, RemovedOldest{}, O.remove_oldest(~K, ~same, V, s), events, 0n)
    case S.GetOldest{}: oldest(~K, ~same, V, s, zero_key, zero_value, events)
    case S.Keys{}: effect(~K, ~same, V, zero_key, zero_value, Keys{}, A.purge_expired(~K, ~same, V, s, events))
    case S.Values{}: effect(~K, ~same, V, zero_key, zero_value, Values{}, A.purge_expired(~K, ~same, V, s, events))
    case S.PurgeExpired{}: effect(~K, ~same, V, zero_key, zero_value, Nothing{}, A.purge_expired(~K, ~same, V, s, events))
    case S.Purge{}: Returned{S.purged(K, V, s), NoReply{}, events, 0n}
    case S.Len{}: Returned{s, Length{S.length(K, V, s)}, events, 0n}
    case S.SetLifetime{ns}: Returned{S.set_lifetime(K, V, s, ns), NoReply{}, events, 0n}
    case S.Metrics{}: metrics(K, V, s, events)
    case S.ResetMetrics{}: reset(K, V, s, events)
    case S.Diagnostics{}: diagnostics(~K, ~same, V, s, events)
