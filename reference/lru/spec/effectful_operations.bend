import Base
import ../types/model.bend as T
import ./cache.bend as S
import ./operations.bend as O
import ./numeric.bend as N
import ./clock.bend as Clock

# Independent Add/refresh clock effects, including the state committed before a
# failed request. No implementation or proof import and no successful-transport
# premise occurs here. Public marshalling and host composition remain separate.
type Outcome<-K: Data, -V: Data> is Data:
  Returned{observation: S.Observation<K, V>, remaining: List<&2, Clock.Event>, requests: Nat}
  Failed{state: S.Model<K, V>, error: Clock.Error, remaining: List<&2, Clock.Event>, requests: Nat}

type PreparedAdd<-K: Data, -V: Data> is Data:
  Prepared{state: S.Model<K, V>, original: K, evicted: Bool}

def evicted(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, old: T.Entry<K, V>) -> PreparedAdd<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  T.Item{+oldkey, oldvalue, olddeadline} = old
  Prepared{S.Abstract{cap, S.erase(~K, ~same, V, bindings, oldkey), S.unlist(~K, ~same, order, oldkey), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb}, key, True{}}

def evict_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, old: Maybe<&2, T.Entry<K, V>>) -> PreparedAdd<K, V>:
  match old:
    case None{}: Prepared{s, key, False{}}
    case Some{entry}: evicted(~K, ~same, V, s, key, entry)

def evict_first(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>) -> PreparedAdd<K, V>:
  match order:
    case Nil{}: Prepared{s, key, False{}}
    case Con{old, tail}: evict_found(~K, ~same, V, s, key, S.find(~K, ~same, V, bindings, old))

def room(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>, full: Bool) -> PreparedAdd<K, V>:
  match full:
    case False{}: Prepared{s, key, False{}}
    case True{}: evict_first(~K, ~same, V, s, key, bindings, order)

def absent_add(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K) -> PreparedAdd<K, V>:
  S.Abstract{cap, bindings, +order, life, counts, cb} = s
  room(~K, ~same, V, s, key, bindings, order, Nat.is_ge(List.length(&2, K, order), cap))

def prepare_found(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, found: Maybe<&2, T.Entry<K, V>>) -> PreparedAdd<K, V>:
  match found:
    case Some{T.Item{original, value, deadline}}: Prepared{s, original, False{}}
    case None{}: absent_add(~K, ~same, V, s, key)

def prepare_add(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K) -> PreparedAdd<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  prepare_found(~K, ~same, V, s, key, S.find(~K, ~same, V, bindings, key))

def sampled_add(~K: Data, ~same: K -> K -> Bool, -V: Data, prepared: PreparedAdd<K, V>, value: V, ns: T.Int64, reply: Clock.Reply) -> Outcome<K, V>:
  Prepared{s, key, was_evicted} = prepared
  match reply:
    case Clock.Rejected{error, remaining}: Failed{s, error, remaining, 1n}
    case Clock.Accepted{now, remaining}: Returned{O.write(~K, ~same, V, s, key, value, N.deadline(now, ns), was_evicted, Nil{}), remaining, 1n}

def immortal_add(~K: Data, ~same: K -> K -> Bool, -V: Data, prepared: PreparedAdd<K, V>, value: V, events: List<&2, Clock.Event>) -> Outcome<K, V>:
  Prepared{s, key, was_evicted} = prepared
  Returned{O.write(~K, ~same, V, s, key, value, T.I64{Word.zero(64n)}, was_evicted, Nil{}), events, 0n}

def add_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, prepared: PreparedAdd<K, V>, value: V, ns: T.Int64, events: List<&2, Clock.Event>, immortal: Bool) -> Outcome<K, V>:
  match immortal:
    case True{}: immortal_add(~K, ~same, V, prepared, value, events)
    case False{}: sampled_add(~K, ~same, V, prepared, value, ns, Clock.request(events))

def add_with_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, ns: T.Int64, events: List<&2, Clock.Event>) -> Outcome<K, V>:
  T.I64{+bits} = ns
  add_lifetime(~K, ~same, V, prepare_add(~K, ~same, V, s, key), value, T.I64{bits}, events, N.zero(bits))

def add(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, value: V, events: List<&2, Clock.Event>) -> Outcome<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  add_with_lifetime(~K, ~same, V, s, key, value, life, events)

# Refresh has already moved recency and counted the hit when its clock is read.
# Updating the deadline must not count that hit a second time.
def refresh_deadline(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, entry: T.Entry<K, V>, +deadline: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  T.Item{+key, +value, old} = entry
  S.Observed{S.Abstract{cap, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, bindings, key)}, order, life, counts, cb}, Some{T.Item{key, value, deadline}}, True{}, Nil{}}

def sampled_refresh(~K: Data, ~same: K -> K -> Bool, -V: Data, prepared: S.Model<K, V>, entry: T.Entry<K, V>, ns: T.Int64, reply: Clock.Reply) -> Outcome<K, V>:
  match reply:
    case Clock.Rejected{error, remaining}: Failed{prepared, error, remaining, 1n}
    case Clock.Accepted{now, remaining}: Returned{refresh_deadline(~K, ~same, V, prepared, entry, N.deadline(now, ns)), remaining, 1n}

def refresh_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, prepared: S.Model<K, V>, entry: T.Entry<K, V>, ns: T.Int64, events: List<&2, Clock.Event>, immortal: Bool) -> Outcome<K, V>:
  match immortal:
    case True{}: Returned{refresh_deadline(~K, ~same, V, prepared, entry, T.I64{Word.zero(64n)}), events, 0n}
    case False{}: sampled_refresh(~K, ~same, V, prepared, entry, ns, Clock.request(events))

def refresh_hit(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, ns: T.Int64, events: List<&2, Clock.Event>, entry: T.Entry<K, V>) -> Outcome<K, V>:
  T.I64{+bits} = ns
  T.Item{+key, value, deadline} = entry
  refresh_lifetime(~K, ~same, V, O.hit_state(~K, ~same, V, s, key, True{}), T.Item{key, value, deadline}, T.I64{bits}, events, N.zero(bits))

def refresh_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, ns: T.Int64, events: List<&2, Clock.Event>, found: Maybe<&2, T.Entry<K, V>>) -> Outcome<K, V>:
  match found:
    case None{}: Returned{S.missing_get(K, V, s), events, 0n}
    case Some{entry}: refresh_hit(~K, ~same, V, s, ns, events, entry)

def refresh(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, ns: T.Int64, events: List<&2, Clock.Event>) -> Outcome<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  refresh_found(~K, ~same, V, s, ns, events, S.find(~K, ~same, V, bindings, key))

# Get/Peek/Contains sample only for a present finite deadline. Their state is
# unchanged if the request fails; hit/miss accounting occurs after that point.
def sampled_read(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, entry: T.Entry<K, V>, tracked: Bool, reply: Clock.Reply) -> Outcome<K, V>:
  match reply:
    case Clock.Rejected{error, remaining}: Failed{s, error, remaining, 1n}
    case Clock.Accepted{now, remaining}: Returned{O.read_found(~K, ~same, V, s, key, now, tracked, Some{entry}), remaining, 1n}

def read_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, entry: T.Entry<K, V>, tracked: Bool, events: List<&2, Clock.Event>, immortal: Bool) -> Outcome<K, V>:
  match immortal:
    case True{}: Returned{O.read_decide(~K, ~same, V, s, key, entry, tracked, False{}), events, 0n}
    case False{}: sampled_read(~K, ~same, V, s, key, entry, tracked, Clock.request(events))

def read_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, tracked: Bool, events: List<&2, Clock.Event>, found: Maybe<&2, T.Entry<K, V>>) -> Outcome<K, V>:
  match found:
    case None{}: Returned{S.Observed{O.count_miss(K, V, s, tracked), None{}, False{}, Nil{}}, events, 0n}
    case Some{T.Item{original, value, T.I64{+bits}}}: read_lifetime(~K, ~same, V, s, key, T.Item{original, value, T.I64{bits}}, tracked, events, N.zero(bits))

def read(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, tracked: Bool, events: List<&2, Clock.Event>) -> Outcome<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  read_found(~K, ~same, V, s, key, tracked, events, S.find(~K, ~same, V, bindings, key))
