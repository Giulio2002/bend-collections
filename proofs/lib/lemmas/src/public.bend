import Base
import ../types/model.bend as T
import ./cache.bend as C
import ./entry_ops.bend as Entry
import ./time.bend as Time

# Callback-free public dispatcher. Through src/host.bend the adapter starts one
# Request and answers every Waiting progress with exactly one provider event:
# a validated sample resumes; a failed provider adopts abandon(pending).
# No user code runs here and no event list is ever produced for the host.
type Request<-K: Data, -V: Data> is Data:
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

type Answer<-K: Data, -V: Data> is Data:
  Empty{}
  Boolean{value: Bool}
  Value{value: V, found: Bool}
  Oldest{key: K, value: V, found: Bool}
  KeyList{keys: List<&2, K>}
  ValueList{values: List<&2, V>}
  Length{length: Nat}
  Counters{metrics: T.Metrics}
  Storage{leaves: Nat, recency: Nat, capacity: Nat, metrics: T.Metrics}

type Shape<-K: Data> is Data:
  Flag{}
  ValueOnly{}
  Captured{key: K}
  Nothing{}
  AllKeys{}
  AllValues{}

type Pending<-K: Data, -V: Data> is Data:
  AddWait{cache: C.Cache<K, V>, code: String, key: K, value: V, nanoseconds: T.Int64, evicted: Bool}
  ReadWait{cache: C.Cache<K, V>, code: String, tracked: Bool, shape: Shape<K>}
  RefreshWait{cache: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, nanoseconds: T.Int64}
  ExpireWait{cache: C.Cache<K, V>, remaining: Nat, shape: Shape<K>}

type Progress<-K: Data, -V: Data> is Data:
  Finished{cache: C.Cache<K, V>, answer: Answer<K, V>}
  Waiting{pending: Pending<K, V>}

def zero_time() -> T.Int64:
  T.I64{Word.zero(64n)}

def item_value(-K: Data, -V: Data, zero: V, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> V:
  match item present:
    case Some{T.Item{k, v, d}} True{}: v
    case x y: zero

def item_key(-K: Data, -V: Data, zero: K, item: Maybe<&2, T.Entry<K, V>>, present: Bool) -> K:
  match item present:
    case Some{T.Item{k, v, d}} True{}: k
    case x y: zero

def shaped(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, +item: Maybe<&2, T.Entry<K, V>>, +present: Bool, shape: Shape<K>) -> Answer<K, V>:
  match shape:
    case Flag{}: Boolean{present}
    case ValueOnly{}: Value{item_value(K, V, zero_value, item, present), present}
    case Captured{key}: Oldest{key, item_value(K, V, zero_value, item, present), present}
    case Nothing{}: Empty{}
    case AllKeys{}: KeyList{Entry.keys_of(K, V, C.entries(K, V, c))}
    case AllValues{}: ValueList{Entry.values_of(K, V, C.entries(K, V, c))}

def finish_step(-K: Data, -V: Data, zero_value: V, step: C.Step<K, V>, shape: Shape<K>) -> Progress<K, V>:
  C.Out{+c, item, flag, events} = step
  Finished{c, shaped(K, V, zero_value, c, item, flag, shape)}

# Add: room is made (and the eviction counted) before the clock is requested.
def prepare_room(-K: Data, -V: Data, +c: C.Cache<K, V>, full: Bool) -> C.Step<K, V>:
  match full:
    case False{}: C.Out{c, None{}, False{}, Nil{}}
    case True{}: C.remove_oldest(K, V, c, True{})

def prepare_found(-K: Data, -V: Data, +c: C.Cache<K, V>, found: Maybe<&2, T.Entry<K, V>>) -> C.Step<K, V>:
  match found:
    case Some{entry}: C.Out{c, None{}, False{}, Nil{}}
    case None{}: prepare_room(K, V, c, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)))

def prepare_add(-K: Data, -V: Data, +c: C.Cache<K, V>, code: String) -> C.Step<K, V>:
  prepare_found(K, V, c, C.lookup(K, V, c, code))

# A present key keeps its stored original key; an absent key is inserted as given.
def retained_key(-K: Data, -V: Data, key: K, found: Maybe<&2, T.Entry<K, V>>) -> K:
  match found:
    case Some{T.Item{original, v, d}}: original
    case None{}: key

# After the optional clock sample the prepared cache has room (or holds the key),
# so the insertion is one store; its flag is the pre-clock eviction result.
def finish_add(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, key: K, value: V, deadline: T.Int64, evicted: Bool) -> Progress<K, V>:
  finish_step(K, V, zero_value, C.store(K, V, c, code, key, value, deadline, evicted, Nil{}), Flag{})

def add_lifetime(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, key: K, value: V, ns: T.Int64, evicted: Bool, immortal: Bool) -> Progress<K, V>:
  match immortal:
    case True{}: finish_add(K, V, zero_value, c, code, key, value, zero_time(), evicted)
    case False{}: Waiting{AddWait{c, code, key, value, ns, evicted}}

def add_prepared(-K: Data, -V: Data, zero_value: V, step: C.Step<K, V>, code: String, key: K, value: V, +ns: T.Int64) -> Progress<K, V>:
  C.Out{c, item, flag, events} = step
  add_lifetime(K, V, zero_value, c, code, key, value, ns, flag, Time.is_zero(ns))

def add_found(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, key: K, value: V, ns: T.Int64, +found: Maybe<&2, T.Entry<K, V>>) -> Progress<K, V>:
  add_prepared(K, V, zero_value, prepare_found(K, V, c, found), code, retained_key(K, V, key, found), value, ns)

def add_with_lifetime(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, +code: String, key: K, value: V, ns: T.Int64) -> Progress<K, V>:
  add_found(K, V, zero_value, c, code, key, value, ns, C.lookup(K, V, c, code))

def add(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, key: K, value: V) -> Progress<K, V>:
  C.State{cap, table, order, +life, counts, cb} = c
  add_with_lifetime(K, V, zero_value, C.State{cap, table, order, life, counts, cb}, code, key, value, life)

# Reads request the clock only for a present entry with a finite deadline.
def finish_read(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, now: T.Int64, tracked: Bool, shape: Shape<K>) -> Progress<K, V>:
  finish_step(K, V, zero_value, C.read_encoded(K, V, c, code, now, tracked), shape)

def read_lifetime(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, tracked: Bool, shape: Shape<K>, immortal: Bool) -> Progress<K, V>:
  match immortal:
    case True{}: finish_read(K, V, zero_value, c, code, zero_time(), tracked, shape)
    case False{}: Waiting{ReadWait{c, code, tracked, shape}}

def read_found(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, code: String, tracked: Bool, shape: Shape<K>, found: Maybe<&2, T.Entry<K, V>>) -> Progress<K, V>:
  match found:
    case None{}: finish_read(K, V, zero_value, c, code, zero_time(), tracked, shape)
    case Some{T.Item{k, v, d}}: read_lifetime(K, V, zero_value, c, code, tracked, shape, Time.is_zero(d))

def read(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, +code: String, tracked: Bool, shape: Shape<K>) -> Progress<K, V>:
  read_found(K, V, zero_value, c, code, tracked, shape, C.lookup(K, V, c, code))

# GetOldest captures the stored original key before the untracked read; an
# expired oldest entry is removed while its key is still returned.
def oldest_found(-K: Data, -V: Data, zero_key: K, zero_value: V, +c: C.Cache<K, V>, +code: String, found: Maybe<&2, T.Entry<K, V>>) -> Progress<K, V>:
  match found:
    case None{}: Finished{c, Oldest{zero_key, zero_value, False{}}}
    case Some{T.Item{k, v, d}}: read(K, V, zero_value, c, code, False{}, Captured{k})

def oldest_order(-K: Data, -V: Data, zero_key: K, zero_value: V, +c: C.Cache<K, V>, order: List<&2, String>) -> Progress<K, V>:
  match order:
    case Nil{}: Finished{c, Oldest{zero_key, zero_value, False{}}}
    case Con{+code, rest}: oldest_found(K, V, zero_key, zero_value, c, code, C.lookup(K, V, c, code))

def get_oldest(-K: Data, -V: Data, zero_key: K, zero_value: V, c: C.Cache<K, V>) -> Progress<K, V>:
  C.State{cap, table, +order, life, counts, cb} = c
  oldest_order(K, V, zero_key, zero_value, C.State{cap, table, order, life, counts, cb}, order)

# Refresh counts the hit and moves recency before its clock request. A zero
# lifetime (only then is the immortal branch taken) stores the zero sentinel.
def finish_refresh(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, ns: T.Int64, now: T.Int64) -> Progress<K, V>:
  T.Item{k, +v, d} = entry
  Finished{Entry.refresh_at(K, V, c, code, T.Item{k, v, d}, ns, now), Value{v, True{}}}

def refresh_lifetime(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, +entry: T.Entry<K, V>, ns: T.Int64, immortal: Bool) -> Progress<K, V>:
  match immortal:
    case True{}: finish_refresh(K, V, c, code, entry, zero_time(), zero_time())
    case False{}: Waiting{RefreshWait{c, code, entry, ns}}

def refresh_prepared(-K: Data, -V: Data, zero_value: V, code: String, +ns: T.Int64, step: C.Step<K, V>) -> Progress<K, V>:
  match step:
    case C.Out{c, Some{entry}, True{}, events}: refresh_lifetime(K, V, c, code, entry, ns, Time.is_zero(ns))
    case C.Out{c, item, flag, events}: Finished{c, Value{zero_value, False{}}}

def refresh(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, +code: String, ns: T.Int64) -> Progress<K, V>:
  refresh_prepared(K, V, zero_value, code, ns, Entry.refresh_prepare(K, V, c, code))

# Keys, Values and PurgeExpired process only the oldest expired prefix. Each
# inspected finite oldest entry costs exactly one clock request.
def complete(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, shape: Shape<K>) -> Progress<K, V>:
  Finished{c, shaped(K, V, zero_value, c, None{}, False{}, shape)}

def expire_lifetime(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, remaining: Nat, shape: Shape<K>, immortal: Bool) -> Progress<K, V>:
  match immortal:
    case True{}: complete(K, V, zero_value, c, shape)
    case False{}: Waiting{ExpireWait{c, remaining, shape}}

def expire_entry(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, remaining: Nat, shape: Shape<K>, entry: Maybe<&2, T.Entry<K, V>>) -> Progress<K, V>:
  match entry:
    case None{}: complete(K, V, zero_value, c, shape)
    case Some{T.Item{k, v, d}}: expire_lifetime(K, V, zero_value, c, remaining, shape, Time.is_zero(d))

def expire_next(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, remaining: Nat, shape: Shape<K>) -> Progress<K, V>:
  match remaining:
    case 0n: complete(K, V, zero_value, c, shape)
    case 1n+p: expire_entry(K, V, zero_value, c, p, shape, C.oldest_entry(K, V, c))

def expire_decide(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, remaining: Nat, shape: Shape<K>, expired: Bool) -> Progress<K, V>:
  match expired:
    case False{}: complete(K, V, zero_value, c, shape)
    case True{}: expire_next(K, V, zero_value, C.step_cache(K, V, C.remove_oldest(K, V, c, False{})), remaining, shape)

def expire_sampled(-K: Data, -V: Data, zero_value: V, c: C.Cache<K, V>, remaining: Nat, shape: Shape<K>, now: T.Int64, entry: Maybe<&2, T.Entry<K, V>>) -> Progress<K, V>:
  match entry:
    case None{}: complete(K, V, zero_value, c, shape)
    case Some{T.Item{k, v, d}}: expire_decide(K, V, zero_value, c, remaining, shape, Time.expired(d, now))

def expire(-K: Data, -V: Data, zero_value: V, +c: C.Cache<K, V>, shape: Shape<K>) -> Progress<K, V>:
  expire_next(K, V, zero_value, c, C.len(K, V, c), shape)

# With no removal observer, full Purge is one native Map.new replacement.
def purge(-K: Data, -V: Data, c: C.Cache<K, V>) -> C.Cache<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  C.State{cap, Map.new(&2, Maybe<&2, T.Entry<K, V>>), Nil{}, life, T.zero_metrics(), cb}

def removed_oldest(-K: Data, -V: Data, zero_key: K, zero_value: V, step: C.Step<K, V>) -> Progress<K, V>:
  C.Out{c, +item, +flag, events} = step
  Finished{c, Oldest{item_key(K, V, zero_key, item, flag), item_value(K, V, zero_value, item, flag), flag}}

def start(-K: Data, -V: Data, encode: K -> String, zero_key: K, zero_value: V, +c: C.Cache<K, V>, request: Request<K, V>) -> Progress<K, V>:
  match request:
    case Add{+k, v}: add(K, V, zero_value, c, encode(k), k, v)
    case AddWithLifetime{+k, v, ns}: add_with_lifetime(K, V, zero_value, c, encode(k), k, v, ns)
    case Get{k}: read(K, V, zero_value, c, encode(k), True{}, ValueOnly{})
    case GetAndRefresh{k, ns}: refresh(K, V, zero_value, c, encode(k), ns)
    case Peek{k}: read(K, V, zero_value, c, encode(k), False{}, ValueOnly{})
    case Contains{k}: read(K, V, zero_value, c, encode(k), False{}, Flag{})
    case Remove{k}: finish_step(K, V, zero_value, C.remove(K, V, encode, c, k), Flag{})
    case RemoveOldest{}: removed_oldest(K, V, zero_key, zero_value, C.remove_oldest(K, V, c, False{}))
    case GetOldest{}: get_oldest(K, V, zero_key, zero_value, c)
    case Keys{}: expire(K, V, zero_value, c, AllKeys{})
    case Values{}: expire(K, V, zero_value, c, AllValues{})
    case Purge{}: Finished{purge(K, V, c), Empty{}}
    case PurgeExpired{}: expire(K, V, zero_value, c, Nothing{})
    case Len{}: Finished{c, Length{C.len(K, V, c)}}
    case SetLifetime{ns}: Finished{C.set_lifetime(K, V, c, ns), Empty{}}
    case Metrics{}: Finished{c, Counters{C.metrics(K, V, c)}}
    case ResetMetrics{}: Finished{C.clear_metrics(K, V, c), Counters{C.metrics(K, V, c)}}
    case Diagnostics{}: Finished{c, Storage{C.map_size(K, V, c), C.len(K, V, c), C.capacity(K, V, c), C.metrics(K, V, c)}}

# Exactly one accepted sample answers one Waiting progress.
def resume(-K: Data, -V: Data, zero_value: V, pending: Pending<K, V>, now: T.Int64) -> Progress<K, V>:
  match pending:
    case AddWait{c, code, key, value, ns, evicted}: finish_add(K, V, zero_value, c, code, key, value, Time.deadline(now, ns), evicted)
    case ReadWait{c, code, tracked, shape}: finish_read(K, V, zero_value, c, code, now, tracked, shape)
    case RefreshWait{c, code, entry, ns}: finish_refresh(K, V, c, code, entry, ns, now)
    case ExpireWait{+c, remaining, shape}: expire_sampled(K, V, zero_value, c, remaining, shape, now, C.oldest_entry(K, V, c))

# State retained by the host when the awaited clock request fails.
def abandon(-K: Data, -V: Data, pending: Pending<K, V>) -> C.Cache<K, V>:
  match pending:
    case AddWait{c, code, key, value, ns, evicted}: c
    case ReadWait{c, code, tracked, shape}: c
    case RefreshWait{c, code, entry, ns}: c
    case ExpireWait{c, remaining, shape}: c
