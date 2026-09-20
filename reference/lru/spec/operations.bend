import Base
import ../types/model.bend as T
import ./cache.bend as S
import ./numeric.bend as N

# Independent finite-map transition semantics. No implementation/proof imports.
# Supplied 'now' is the explicit sample at the operation's clock-read point.
# User callbacks are excluded. Legacy event fields are inert on initial states.
def write(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K, value: V, deadline: T.Int64, evicted: Bool, events: List<&2, T.Event<K, V>>) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  S.Observed{S.Abstract{cap, Con{T.Item{key, value, deadline}, S.erase(~K, ~same, V, bindings, key)}, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}}), life, T.Counts{Word.inc(64n, i), e, r, h, m}, cb}, None{}, evicted, events}

# Abstract state immediately after capacity eviction, before the new write.
# This factors the state already used by after_eviction below; no clock is read.
def evicted_state(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K) -> S.Model<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  S.Abstract{cap, S.erase(~K, ~same, V, bindings, key), S.unlist(~K, ~same, order, key), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb}

def after_eviction(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, old: T.Entry<K, V>) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, +cb} = s
  T.Item{+oldkey, oldvalue, olddeadline} = old
  write(~K, ~same, V, S.Abstract{cap, S.erase(~K, ~same, V, bindings, oldkey), S.unlist(~K, ~same, order, oldkey), life, T.Counts{i, Word.inc(64n, e), r, h, m}, cb}, key, value, deadline, True{}, S.callbacks(K, V, Con{T.Item{oldkey, oldvalue, olddeadline}, Nil{}}, cb))

def evict_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, old: Maybe<&2, T.Entry<K, V>>) -> S.Observation<K, V>:
  match old:
    case None{}:
      write(~K, ~same, V, s, key, value, deadline, False{}, Nil{})
    case Some{entry}:
      after_eviction(~K, ~same, V, s, key, value, deadline, entry)

def evict_first(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>) -> S.Observation<K, V>:
  match order:
    case Nil{}:
      write(~K, ~same, V, s, key, value, deadline, False{}, Nil{})
    case Con{old, tail}:
      evict_found(~K, ~same, V, s, key, value, deadline, S.find(~K, ~same, V, bindings, old))

def new_room(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, bindings: List<&2, T.Entry<K, V>>, order: List<&2, K>, full: Bool) -> S.Observation<K, V>:
  match full:
    case False{}:
      write(~K, ~same, V, s, key, value, deadline, False{}, Nil{})
    case True{}:
      evict_first(~K, ~same, V, s, key, value, deadline, bindings, order)

def absent_add(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, value: V, deadline: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, +order, life, counts, cb} = s
  new_room(~K, ~same, V, s, key, value, deadline, bindings, order, Nat.is_ge(List.length(&2, K, order), cap))

def add_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, value: V, deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>) -> S.Observation<K, V>:
  match found:
    case None{}:
      absent_add(~K, ~same, V, s, key, value, deadline)
    case Some{T.Item{original, oldvalue, olddeadline}}:
      write(~K, ~same, V, s, original, value, deadline, False{}, Nil{})

def add_with_lifetime(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, value: V, ns: T.Int64, now: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  add_found(~K, ~same, V, s, key, value, N.deadline(now, ns), S.find(~K, ~same, V, bindings, key))

def add(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, value: V, now: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  add_with_lifetime(~K, ~same, V, s, key, value, life, now)

def count_miss(-K: Data, -V: Data, s: S.Model<K, V>, tracked: Bool) -> S.Model<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  match tracked:
    case False{}:
      S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}
    case True{}:
      S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, Word.inc(64n, m)}, cb}

def expired_result(-K: Data, -V: Data, result: S.Observation<K, V>, tracked: Bool) -> S.Observation<K, V>:
  S.Observed{s, item, flag, events} = result
  S.Observed{count_miss(K, V, s, tracked), item, False{}, events}

def hit_state(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K, tracked: Bool) -> S.Model<K, V>:
  S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb} = s
  match tracked:
    case False{}:
      S.Abstract{cap, bindings, order, life, T.Counts{i, e, r, h, m}, cb}
    case True{}:
      S.Abstract{cap, bindings, List.append(&2, K, S.unlist(~K, ~same, order, key), Con{key, Nil{}}), life, T.Counts{i, e, r, Word.inc(64n, h), m}, cb}

def read_decide(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, +key: K, entry: T.Entry<K, V>, tracked: Bool, expired: Bool) -> S.Observation<K, V>:
  match expired:
    case True{}:
      expired_result(K, V, S.remove(~K, ~same, V, s, key), tracked)
    case False{}:
      S.Observed{hit_state(~K, ~same, V, s, key, tracked), Some{entry}, True{}, Nil{}}

def read_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, key: K, now: T.Int64, tracked: Bool, found: Maybe<&2, T.Entry<K, V>>) -> S.Observation<K, V>:
  match found:
    case None{}:
      S.Observed{count_miss(K, V, s, tracked), None{}, False{}, Nil{}}
    case Some{T.Item{k, v, +d}}:
      read_decide(~K, ~same, V, s, key, T.Item{k, v, d}, tracked, N.expired(d, now))

def read(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, +key: K, now: T.Int64, tracked: Bool) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  read_found(~K, ~same, V, s, key, now, tracked, S.find(~K, ~same, V, bindings, key))

def refreshed(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, entry: T.Entry<K, V>, +deadline: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  T.Item{+k, +v, olddeadline} = entry
  S.Observed{hit_state(~K, ~same, V, S.Abstract{cap, Con{T.Item{k, v, deadline}, S.erase(~K, ~same, V, bindings, k)}, order, life, counts, cb}, k, True{}), Some{T.Item{k, v, deadline}}, True{}, Nil{}}

def refresh_found(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, ns: T.Int64, now: T.Int64, found: Maybe<&2, T.Entry<K, V>>) -> S.Observation<K, V>:
  match found:
    case None{}:
      S.missing_get(K, V, s)
    case Some{entry}:
      refreshed(~K, ~same, V, s, entry, N.deadline(now, ns))

def refresh(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, key: K, ns: T.Int64, now: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  refresh_found(~K, ~same, V, s, ns, now, S.find(~K, ~same, V, bindings, key))

def oldest_remove(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, order: List<&2, K>) -> S.Observation<K, V>:
  match order:
    case Nil{}:
      S.missing_remove(K, V, s)
    case Con{k, tail}:
      S.remove(~K, ~same, V, s, k)

def remove_oldest(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  oldest_remove(~K, ~same, V, s, order)

def oldest_read(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, order: List<&2, K>, now: T.Int64) -> S.Observation<K, V>:
  match order:
    case Nil{}:
      S.Observed{s, None{}, False{}, Nil{}}
    case Con{k, tail}:
      read(~K, ~same, V, s, k, now, False{})

# Internal snapshot only. public_oldest.bend supplies the complete public
# key/value/found observation, clock consumption and missing-input failures.
def get_oldest(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, now: T.Int64) -> S.Observation<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  oldest_read(~K, ~same, V, s, order, now)

def collect(-K: Data, -V: Data, found: Maybe<&2, T.Entry<K, V>>, rest: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match found:
    case None{}:
      rest
    case Some{e}:
      Con{e, rest}

def ordered(~K: Data, ~same: K -> K -> Bool, -V: Data, order: List<&2, K>, +bindings: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match order:
    case Nil{}:
      Nil{}
    case Con{k, tail}:
      collect(K, V, S.find(~K, ~same, V, bindings, k), ordered(~K, ~same, V, tail, bindings))

def all_entries(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>) -> List<&2, T.Entry<K, V>>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  ordered(~K, ~same, V, order, bindings)

def observed_state(-K: Data, -V: Data, result: S.Observation<K, V>) -> S.Model<K, V>:
  S.Observed{s, item, present, callbacks} = result
  s

def remove_entries(~K: Data, ~same: K -> K -> Bool, -V: Data, entries: List<&2, T.Entry<K, V>>, s: S.Model<K, V>) -> S.Model<K, V>:
  match entries:
    case Nil{}:
      s
    case Con{T.Item{k, v, d}, tail}:
      remove_entries(~K, ~same, V, tail, observed_state(K, V, S.remove(~K, ~same, V, s, k)))

type AggregateFailure<-K: Data, -V: Data> is Data:
  AggregateFailed{error: String, state: S.Model<K, V>, unused_clock: List<&2, T.Int64>}

type AggregateResult<-K: Data, -V: Data> is Data:
  Aggregate{state: S.Model<K, V>, keys: List<&2, K>, values: List<&2, V>, callbacks: List<&2, T.Event<K, V>>, unused_clock: List<&2, T.Int64>}

def entry_keys(-K: Data, -V: Data, entries: List<&2, T.Entry<K, V>>) -> List<&2, K>:
  match entries:
    case Nil{}:
      Nil{}
    case Con{T.Item{k, v, d}, tail}:
      Con{k, entry_keys(K, V, tail)}

def entry_values(-K: Data, -V: Data, entries: List<&2, T.Entry<K, V>>) -> List<&2, V>:
  match entries:
    case Nil{}:
      Nil{}
    case Con{T.Item{k, v, d}, tail}:
      Con{v, entry_values(K, V, tail)}

# The aggregate exposes both projections so Keys and Values share exactly the
# same expiry/removal/clock semantics; consumers choose the return field.
def prefix_result(~K: Data, ~same: K -> K -> Bool, -V: Data, s: S.Model<K, V>, enabled: Bool, prefix: Result<&2, &2, S.PrefixFailure<K, V>, S.ExpiredPrefix<K, V>>) -> Result<&2, &2, AggregateFailure<K, V>, AggregateResult<K, V>>:
  match prefix:
    case Fail{S.PrefixFailed{err, removed, retained, times}}:
      Fail{AggregateFailed{err, remove_entries(~K, ~same, V, removed, s), times}}
    case Done{S.Prefix{+removed, +retained, times}}:
      Done{Aggregate{remove_entries(~K, ~same, V, removed, s), entry_keys(K, V, retained), entry_values(K, V, retained), S.callbacks(K, V, removed, enabled), times}}

def purge_expired(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>, times: List<&2, T.Int64>) -> Result<&2, &2, AggregateFailure<K, V>, AggregateResult<K, V>>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  prefix_result(~K, ~same, V, s, cb, S.expired_prefix(K, V, all_entries(~K, ~same, V, s), times))

def purge(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: S.Model<K, V>) -> AggregateResult<K, V>:
  S.Abstract{cap, bindings, order, life, counts, cb} = s
  Aggregate{S.purged(K, V, s), Nil{}, Nil{}, S.callbacks(K, V, all_entries(~K, ~same, V, s), cb), Nil{}}
