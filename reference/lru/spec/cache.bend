import Base
import ./numeric.bend as N
import ../types/model.bend as T

# Independent abstract finite-map representation. Well-formed states have one
# binding per key and a recency permutation of exactly those keys. No native Map,
# implementation, codec, or proof imports occur in this specification.
# Binding-list order is not observable: full refinement must compare finite-map
# lookup extensionally (or canonicalize bindings), while recency order is exact.
type Model<-K: Data, -V: Data> is Data:
  Abstract{capacity: Nat, bindings: List<&2, T.Entry<K, V>>, recency: List<&2, K>, lifetime: T.Int64, counts: T.Metrics, callback: Bool}

type Observation<-K: Data, -V: Data> is Data:
  Observed{state: Model<K, V>, returned: Maybe<&2, T.Entry<K, V>>, present: Bool, callbacks: List<&2, T.Event<K, V>>}

def initial(-K: Data, -V: Data, capacity: Nat) -> Model<K, V>:
  Abstract{capacity, Nil{}, Nil{}, T.I64{Word.zero(64n)}, T.zero_metrics(), False{}}

def length(-K: Data, -V: Data, s: Model<K, V>) -> Nat:
  Abstract{cap, bindings, recency, life, counts, cb} = s
  List.length(&2, K, recency)

def set_lifetime(-K: Data, -V: Data, s: Model<K, V>, lifetime: T.Int64) -> Model<K, V>:
  Abstract{cap, bindings, recency, old, counts, cb} = s
  Abstract{cap, bindings, recency, lifetime, counts, cb}

def reset_metrics(-K: Data, -V: Data, s: Model<K, V>) -> Model<K, V> & T.Metrics:
  Abstract{cap, bindings, recency, life, counts, cb} = s
  (Abstract{cap, bindings, recency, life, T.zero_metrics(), cb}, counts)

def missing_get(-K: Data, -V: Data, s: Model<K, V>) -> Observation<K, V>:
  Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, m}, cb} = s
  Observed{Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, Word.inc(64n, m)}, cb}, None{}, False{}, Nil{}}

def missing_remove(-K: Data, -V: Data, s: Model<K, V>) -> Observation<K, V>:
  Observed{s, None{}, False{}, Nil{}}

# Signed comparisons, including sentinel, specified independently.
def is_expired(deadline: T.Int64, now: T.Int64) -> Bool:
  N.expired(deadline, now)

# Legacy pure event metadata. Supported initial states disable it and expose
# no registration command; no user function is represented or executed here.
def callbacks(-K: Data, -V: Data, entries: List<&2, T.Entry<K, V>>, +enabled: Bool) -> List<&2, T.Event<K, V>>:
  match entries enabled:
    case Nil{} b:
      Nil{}
    case Con{entry, tail} False{}:
      Nil{}
    case Con{T.Item{k, v, deadline}, tail} True{}:
      Con{T.Evicted{k, v}, callbacks(K, V, tail, True{})}

# Full purge is defined from the ordered entries, not from implementation steps.
def purged(-K: Data, -V: Data, s: Model<K, V>) -> Model<K, V>:
  Abstract{cap, bindings, recency, life, counts, cb} = s
  Abstract{cap, Nil{}, Nil{}, life, T.zero_metrics(), cb}

# Typed public commands. Independent observations and clock effects are defined
# in public_commands.bend, and finite caller traces in traces.bend.
type Command<-K: Data, -V: Data> is Data:
  Add{key: K, value: V}
  AddWithLifetime{key: K, value: V, nanoseconds: T.Int64}
  Get{key: K}
  GetAndRefresh{key: K, nanoseconds: T.Int64}
  Peek{key: K}
  Contains{key: K}
  Remove{key: K}
  RemoveOldest{}
  GetOldest{}
  Keys{}
  Values{}
  Purge{}
  PurgeExpired{}
  Len{}
  SetLifetime{nanoseconds: T.Int64}
  Metrics{}
  ResetMetrics{}
  Diagnostics{}

# Abstract finite-map operations use user-key equality, never encoding or Map.
def choose_entry(-K: Data, -V: Data, entry: T.Entry<K, V>, rest: Maybe<&2, T.Entry<K, V>>, equal: Bool) -> Maybe<&2, T.Entry<K, V>>:
  match equal:
    case True{}:
      Some{entry}
    case False{}:
      rest

def find(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, +key: K) -> Maybe<&2, T.Entry<K, V>>:
  match bindings:
    case Nil{}:
      None{}
    case Con{T.Item{+k, v, d}, tail}:
      choose_entry(K, V, T.Item{k, v, d}, find(~K, ~same, V, tail, key), same(k)(key))

def omit_entry(-K: Data, -V: Data, entry: T.Entry<K, V>, rest: List<&2, T.Entry<K, V>>, equal: Bool) -> List<&2, T.Entry<K, V>>:
  match equal:
    case True{}:
      rest
    case False{}:
      Con{entry, rest}

def erase(~K: Data, ~same: K -> K -> Bool, -V: Data, bindings: List<&2, T.Entry<K, V>>, +key: K) -> List<&2, T.Entry<K, V>>:
  match bindings:
    case Nil{}:
      Nil{}
    case Con{T.Item{+k, v, d}, tail}:
      omit_entry(K, V, T.Item{k, v, d}, erase(~K, ~same, V, tail, key), same(k)(key))

def omit_key(-K: Data, key: K, rest: List<&2, K>, equal: Bool) -> List<&2, K>:
  match equal:
    case True{}:
      rest
    case False{}:
      Con{key, rest}

def unlist(~K: Data, ~same: K -> K -> Bool, order: List<&2, K>, +key: K) -> List<&2, K>:
  match order:
    case Nil{}:
      Nil{}
    case Con{+h, tail}:
      omit_key(K, h, unlist(~K, ~same, tail, key), same(h)(key))

def remove_existing(~K: Data, ~same: K -> K -> Bool, -V: Data, s: Model<K, V>, +key: K, +entry: T.Entry<K, V>) -> Observation<K, V>:
  Abstract{cap, bindings, recency, life, T.Counts{i, e, r, h, m}, +cb} = s
  Observed{Abstract{cap, erase(~K, ~same, V, bindings, key), unlist(~K, ~same, recency, key), life, T.Counts{i, e, Word.inc(64n, r), h, m}, cb}, Some{entry}, True{}, callbacks(K, V, Con{entry, Nil{}}, cb)}

def remove_decision(~K: Data, ~same: K -> K -> Bool, -V: Data, s: Model<K, V>, key: K, found: Maybe<&2, T.Entry<K, V>>) -> Observation<K, V>:
  match found:
    case None{}:
      missing_remove(K, V, s)
    case Some{entry}:
      remove_existing(~K, ~same, V, s, key, entry)

def remove(~K: Data, ~same: K -> K -> Bool, -V: Data, +s: Model<K, V>, +key: K) -> Observation<K, V>:
  Abstract{cap, bindings, recency, life, counts, cb} = s
  remove_decision(~K, ~same, V, s, key, find(~K, ~same, V, bindings, key))

# Expiration consumes a clock sample only when the current oldest deadline is
# finite. A finite future deadline stops; an immortal oldest also stops without
# looking at any subsequent binding. This model returns removed oldest entries
# plus unused clock samples; transport exhaustion is an explicit failure.
type PrefixFailure<-K: Data, -V: Data> is Data:
  PrefixFailed{error: String, removed: List<&2, T.Entry<K, V>>, retained: List<&2, T.Entry<K, V>>, unused_clock: List<&2, T.Int64>}

type ExpiredPrefix<-K: Data, -V: Data> is Data:
  Prefix{removed: List<&2, T.Entry<K, V>>, retained: List<&2, T.Entry<K, V>>, unused_clock: List<&2, T.Int64>}

def prefix_prepend(-K: Data, -V: Data, entry: T.Entry<K, V>, rest: Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>) -> Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>:
  match rest:
    case Fail{PrefixFailed{err, removed, retained, times}}:
      Fail{PrefixFailed{err, Con{entry, removed}, retained, times}}
    case Done{Prefix{removed, retained, times}}:
      Done{Prefix{Con{entry, removed}, retained, times}}

def prefix_decide(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, times: List<&2, T.Int64>, expired: Bool, rest: Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>) -> Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>:
  match expired:
    case False{}:
      Done{Prefix{Nil{}, Con{entry, tail}, times}}
    case True{}:
      prefix_prepend(K, V, entry, rest)

def prefix_missing(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, immortal: Bool) -> Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>:
  match immortal:
    case True{}:
      Done{Prefix{Nil{}, Con{entry, tail}, Nil{}}}
    case False{}:
      Fail{PrefixFailed{"clock sample missing", Nil{}, Con{entry, tail}, Nil{}}}

def prefix_sampled(-K: Data, -V: Data, entry: T.Entry<K, V>, tail: List<&2, T.Entry<K, V>>, now: T.Int64, times: List<&2, T.Int64>, expired: Bool, rest: Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>, immortal: Bool) -> Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>:
  match immortal:
    case True{}:
      Done{Prefix{Nil{}, Con{entry, tail}, Con{now, times}}}
    case False{}:
      prefix_decide(K, V, entry, tail, times, expired, rest)

def expired_prefix(-K: Data, -V: Data, ordered: List<&2, T.Entry<K, V>>, times: List<&2, T.Int64>) -> Result<&2, &2, PrefixFailure<K, V>, ExpiredPrefix<K, V>>:
  match ordered times:
    case Nil{} samples:
      Done{Prefix{Nil{}, Nil{}, samples}}
    case Con{T.Item{k, v, T.I64{+w}}, tail} Nil{}:
      prefix_missing(K, V, T.Item{k, v, T.I64{w}}, tail, N.zero(w))
    case Con{T.Item{k, v, T.I64{+w}}, +tail} Con{+now, +samples}:
      prefix_sampled(K, V, T.Item{k, v, T.I64{w}}, tail, now, samples, is_expired(T.I64{w}, now), expired_prefix(K, V, tail, samples), N.zero(w))

def create_decision(-K: Data, -V: Data, capacity: Nat, valid: Bool) -> Result<&2, &2, String, Model<K, V>>:
  match valid:
    case False{}:
      Fail{"invalid capacity or size"}
    case True{}:
      Done{initial(K, V, capacity)}

def construct(-K: Data, -V: Data, capacity: U32, size: U32, zero: Bool, reserved: Bool, small: Bool) -> Result<&2, &2, String, Model<K, V>>:
  match zero reserved small:
    case True{} a b:
      Fail{"capacity must be positive"}
    case False{} True{} b:
      Fail{"size must not be 0XFFFFFFFF"}
    case False{} False{} True{}:
      Fail{"size (" ++ U32.show(size) ++ ") is smaller than capacity (" ++ U32.show(capacity) ++ ")"}
    case False{} False{} False{}:
      Done{initial(K, V, U32.to_nat(capacity))}

def new_with_size(-K: Data, -V: Data, +capacity: U32, +size: U32) -> Result<&2, &2, String, Model<K, V>>:
  construct(K, V, capacity, size, U32.is_eq(capacity, 0), U32.is_eq(size, 4294967295), U32.is_lt(size, capacity))
