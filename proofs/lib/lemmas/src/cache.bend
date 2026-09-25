import Base
import ../types/model.bend as T
import ./time.bend as Time

# The list is oldest first; it contains only encoded keys, never values.
type Cache<-K: Data, -V: Data> is Data:
  State{capacity: Nat, table: Map<&2, Maybe<&2, T.Entry<K, V>>>, order: List<&2, String>, lifetime: T.Int64, counts: T.Metrics, callback: Bool}

type Step<-K: Data, -V: Data> is Data:
  Out{cache: Cache<K, V>, item: Maybe<&2, T.Entry<K, V>>, flag: Bool, events: List<&2, T.LruEvent<K, V>>}

def init(-K: Data, -V: Data, capacity: Nat) -> Cache<K, V>:
  State{capacity, Map.new(&2, Maybe<&2, T.Entry<K, V>>), Nil{}, T.I64{Word.zero(64n)}, T.zero_metrics(), False{}}

def new_checked(-K: Data, -V: Data, capacity: Nat, valid: Bool) -> Result<&2, &2, String, Cache<K, V>>:
  match valid:
    case False{}:
      Fail{"invalid capacity or size"}
    case True{}:
      Done{init(K, V, capacity)}

def construct(-K: Data, -V: Data, capacity: U32, size: U32, zero: Bool, reserved: Bool, small: Bool) -> Result<&2, &2, String, Cache<K, V>>:
  match zero reserved small:
    case True{} a b:
      Fail{"capacity must be positive"}
    case False{} True{} b:
      Fail{"size must not be 0XFFFFFFFF"}
    case False{} False{} True{}:
      Fail{"size (" ++ U32.show(size) ++ ") is smaller than capacity (" ++ U32.show(capacity) ++ ")"}
    case False{} False{} False{}:
      Done{init(K, V, U32.to_nat(capacity))}

def new_with_size(-K: Data, -V: Data, +capacity: U32, +size: U32) -> Result<&2, &2, String, Cache<K, V>>:
  construct(K, V, capacity, size, U32.is_eq(capacity, 0), U32.is_eq(size, 4294967295), U32.is_lt(size, capacity))

def new(-K: Data, -V: Data, +capacity: U32) -> Result<&2, &2, String, Cache<K, V>>:
  new_with_size(K, V, capacity, capacity)

def len(-K: Data, -V: Data, +c: Cache<K, V>) -> Nat:
  State{cap, m, order, life, counts, cb} = c
  List.length(&2, String, order)

law without:
  for xs: List<&2, String>
  for +key: String
  List<&2, String>

def without_keep(h: String, tail: List<&2, String>, eq: Bool) -> List<&2, String>:
  match eq:
    case True{}:
      tail
    case False{}:
      Con{h, tail}

def without(xs, key):
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, tail}:
      without_keep(h, without(tail, key), String.eq(h, key))

def events(-K: Data, -V: Data, cb: Bool, e: T.Entry<K, V>) -> List<&2, T.LruEvent<K, V>>:
  match cb:
    case False{}:
      Nil{}
    case True{}:
      T.Item{k, v, d} = e
      Con{T.Evicted{k, v}, Nil{}}

def removal_counts(m: T.Metrics, capacity_eviction: Bool) -> T.Metrics:
  T.Counts{i, e, r, h, s} = m
  match capacity_eviction:
    case True{}:
      T.Counts{i, Word.inc(64n, e), r, h, s}
    case False{}:
      T.Counts{i, e, Word.inc(64n, r), h, s}

def lookup_result(-K: Data, -V: Data, result: Map<&2, Maybe<&2, T.Entry<K, V>>> & Maybe<&2, T.Entry<K, V>>) -> Maybe<&2, T.Entry<K, V>>:
  (m, found) = result
  found

def lookup(-K: Data, -V: Data, c: Cache<K, V>, code: String) -> Maybe<&2, T.Entry<K, V>>:
  State{cap, m, order, life, counts, cb} = c
  lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, m, code))

def remove_present(-K: Data, -V: Data, c: Cache<K, V>, +key: String, evict: Bool, +entry: T.Entry<K, V>) -> Step<K, V>:
  State{cap, m, order, life, counts, +cb} = c
  Out{State{cap, Map.del(&2, Maybe<&2, T.Entry<K, V>>, m, key), without(order, key), life, removal_counts(counts, evict), cb}, Some{entry}, True{}, events(K, V, cb, entry)}

def remove_found(-K: Data, -V: Data, c: Cache<K, V>, key: String, evict: Bool, found: Maybe<&2, T.Entry<K, V>>) -> Step<K, V>:
  match found:
    case None{}:
      Out{c, None{}, False{}, Nil{}}
    case Some{entry}:
      remove_present(K, V, c, key, evict, entry)

def remove_encoded(-K: Data, -V: Data, +c: Cache<K, V>, +key: String, evict: Bool) -> Step<K, V>:
  remove_found(K, V, c, key, evict, lookup(K, V, c, key))

def remove(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, key: K) -> Step<K, V>:
  remove_encoded(K, V, c, encode(key), False{})

def oldest_remove(-K: Data, -V: Data, +c: Cache<K, V>, order: List<&2, String>, evict: Bool) -> Step<K, V>:
  match order:
    case Nil{}:
      Out{c, None{}, False{}, Nil{}}
    case Con{k, rest}:
      remove_encoded(K, V, c, k, evict)

def remove_oldest(-K: Data, -V: Data, +c: Cache<K, V>, evict: Bool) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  oldest_remove(K, V, c, order, evict)

def store(-K: Data, -V: Data, +c: Cache<K, V>, +code: String, key: K, value: V, deadline: T.Int64, flag: Bool, evs: List<&2, T.LruEvent<K, V>>) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  T.Counts{i, e, r, h, s} = counts
  Out{State{cap, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{T.Item{key, value, deadline}}), List.append(&2, String, without(order, code), Con{code, Nil{}}), life, T.Counts{Word.inc(64n, i), e, r, h, s}, cb}, None{}, flag, evs}

def store_after_evict(-K: Data, -V: Data, code: String, key: K, value: V, deadline: T.Int64, step: Step<K, V>) -> Step<K, V>:
  Out{c, item, flag, evs} = step
  store(K, V, c, code, key, value, deadline, flag, evs)

def add_room(-K: Data, -V: Data, +c: Cache<K, V>, code: String, key: K, value: V, deadline: T.Int64, full: Bool) -> Step<K, V>:
  match full:
    case False{}:
      store(K, V, c, code, key, value, deadline, False{}, Nil{})
    case True{}:
      store_after_evict(K, V, code, key, value, deadline, remove_oldest(K, V, c, True{}))

def capacity(-K: Data, -V: Data, c: Cache<K, V>) -> Nat:
  State{cap, m, order, life, counts, cb} = c
  cap

def add_found(-K: Data, -V: Data, +c: Cache<K, V>, code: String, key: K, value: V, deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>) -> Step<K, V>:
  match found:
    case None{}:
      add_room(K, V, c, code, key, value, deadline, Nat.is_ge(len(K, V, c), capacity(K, V, c)))
    case Some{T.Item{original, old, expiry}}:
      store(K, V, c, code, original, value, deadline, False{}, Nil{})

def add_with_lifetime(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, +key: K, value: V, ns: T.Int64, now: T.Int64) -> Step<K, V>:
  +code = encode(key)
  add_found(K, V, c, code, key, value, Time.deadline(now, ns), lookup(K, V, c, code))

def add(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, key: K, value: V, now: T.Int64) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  add_with_lifetime(K, V, encode, c, key, value, life, now)

def hit_counts(m: T.Metrics, +tracked: Bool, hit: Bool) -> T.Metrics:
  T.Counts{i, e, r, h, s} = m
  match tracked hit:
    case False{} unused:
      T.Counts{i, e, r, h, s}
    case True{} True{}:
      T.Counts{i, e, r, Word.inc(64n, h), s}
    case True{} False{}:
      T.Counts{i, e, r, h, Word.inc(64n, s)}

def counted(-K: Data, -V: Data, step: Step<K, V>, +tracked: Bool, hit: Bool) -> Step<K, V>:
  Out{State{cap, m, order, life, counts, cb}, item, flag, evs} = step
  Out{State{cap, m, order, life, hit_counts(counts, tracked, hit), cb}, item, flag, evs}

def miss_after_remove(-K: Data, -V: Data, step: Step<K, V>, +tracked: Bool) -> Step<K, V>:
  Out{c, item, flag, evs} = step
  counted(K, V, Out{c, item, False{}, evs}, tracked, False{})

def touch_order(order: List<&2, String>, +code: String, touch: Bool) -> List<&2, String>:
  match touch:
    case False{}:
      order
    case True{}:
      List.append(&2, String, without(order, code), Con{code, Nil{}})

def read_live(-K: Data, -V: Data, +c: Cache<K, V>, code: String, +entry: T.Entry<K, V>, +tracked: Bool) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  Out{State{cap, m, touch_order(order, code, tracked), life, hit_counts(counts, tracked, True{}), cb}, Some{entry}, True{}, Nil{}}

def read_expiry(-K: Data, -V: Data, +c: Cache<K, V>, code: String, entry: T.Entry<K, V>, +tracked: Bool, expired: Bool) -> Step<K, V>:
  match expired:
    case False{}:
      read_live(K, V, c, code, entry, tracked)
    case True{}:
      miss_after_remove(K, V, remove_encoded(K, V, c, code, False{}), tracked)

def read_found(-K: Data, -V: Data, +c: Cache<K, V>, code: String, now: T.Int64, +tracked: Bool, found: Maybe<&2, T.Entry<K, V>>) -> Step<K, V>:
  match found:
    case None{}:
      counted(K, V, Out{c, None{}, False{}, Nil{}}, tracked, False{})
    case Some{T.Item{k, v, +d}}:
      read_expiry(K, V, c, code, T.Item{k, v, d}, tracked, Time.expired(d, now))

def read_encoded(-K: Data, -V: Data, +c: Cache<K, V>, +code: String, now: T.Int64, +tracked: Bool) -> Step<K, V>:
  read_found(K, V, c, code, now, tracked, lookup(K, V, c, code))

def get(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, key: K, now: T.Int64) -> Step<K, V>:
  read_encoded(K, V, c, encode(key), now, True{})

def peek(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, key: K, now: T.Int64) -> Step<K, V>:
  read_encoded(K, V, c, encode(key), now, False{})

def refresh_present(-K: Data, -V: Data, c: Cache<K, V>, +code: String, +entry: T.Entry<K, V>) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  read_live(K, V, State{cap, Map.set(&2, Maybe<&2, T.Entry<K, V>>, m, code, Some{entry}), order, life, counts, cb}, code, entry, True{})

def refresh_found(-K: Data, -V: Data, +c: Cache<K, V>, +code: String, deadline: T.Int64, found: Maybe<&2, T.Entry<K, V>>) -> Step<K, V>:
  match found:
    case None{}:
      counted(K, V, Out{c, None{}, False{}, Nil{}}, True{}, False{})
    case Some{T.Item{k, v, old}}:
      +entry = {T.Item{k, v, deadline} : T.Entry<K, V>}
      refresh_present(K, V, c, code, entry)

def get_and_refresh(-K: Data, -V: Data, encode: K -> String, +c: Cache<K, V>, key: K, ns: T.Int64, now: T.Int64) -> Step<K, V>:
  +code = encode(key)
  refresh_found(K, V, c, code, Time.deadline(now, ns), lookup(K, V, c, code))

def set_lifetime(-K: Data, -V: Data, +c: Cache<K, V>, ns: T.Int64) -> Cache<K, V>:
  State{cap, m, order, life, counts, cb} = c
  State{cap, m, order, ns, counts, cb}

def metrics(-K: Data, -V: Data, +c: Cache<K, V>) -> T.Metrics:
  State{cap, m, order, life, counts, cb} = c
  counts

def reset_metrics(-K: Data, -V: Data, +c: Cache<K, V>) -> Cache<K, V> & T.Metrics:
  State{cap, m, order, life, counts, cb} = c
  (State{cap, m, order, life, T.zero_metrics(), cb}, counts)

def oldest_read(-K: Data, -V: Data, +c: Cache<K, V>, order: List<&2, String>, now: T.Int64) -> Step<K, V>:
  match order:
    case Nil{}:
      Out{c, None{}, False{}, Nil{}}
    case Con{k, rest}:
      read_encoded(K, V, c, k, now, False{})

def get_oldest(-K: Data, -V: Data, +c: Cache<K, V>, now: T.Int64) -> Step<K, V>:
  State{cap, m, order, life, counts, cb} = c
  oldest_read(K, V, c, order, now)

def step_cache(-K: Data, -V: Data, s: Step<K, V>) -> Cache<K, V>:
  Out{c, item, flag, evs} = s
  c

def step_events(-K: Data, -V: Data, s: Step<K, V>) -> List<&2, T.LruEvent<K, V>>:
  Out{c, item, flag, evs} = s
  evs

def clear_metrics(-K: Data, -V: Data, c: Cache<K, V>) -> Cache<K, V>:
  State{cap, m, order, life, counts, cb} = c
  State{cap, m, order, life, T.zero_metrics(), cb}

# No accumulated event log is stored in the cache itself.
def purge_loop(-K: Data, -V: Data, fuel: Nat, c: Cache<K, V>) -> Step<K, V>:
  match fuel:
    case 0n:
      Out{clear_metrics(K, V, c), None{}, False{}, Nil{}}
    case 1n+p:
      +step = remove_oldest(K, V, c, False{})
      +rest = purge_loop(K, V, p, step_cache(K, V, step))
      Out{step_cache(K, V, rest), None{}, False{}, List.append(&2, T.LruEvent<K, V>, step_events(K, V, step), step_events(K, V, rest))}

def purge(-K: Data, -V: Data, +c: Cache<K, V>) -> Step<K, V>:
  purge_loop(K, V, len(K, V, c), c)

def first_entry(-K: Data, -V: Data, c: Cache<K, V>, order: List<&2, String>) -> Maybe<&2, T.Entry<K, V>>:
  match order:
    case Nil{}:
      None{}
    case Con{k, rest}:
      lookup(K, V, c, k)

def oldest_entry(-K: Data, -V: Data, +c: Cache<K, V>) -> Maybe<&2, T.Entry<K, V>>:
  State{cap, m, order, life, counts, cb} = c
  first_entry(K, V, c, order)

def finite_entry(-K: Data, -V: Data, e: Maybe<&2, T.Entry<K, V>>) -> Bool:
  match e:
    case None{}:
      False{}
    case Some{T.Item{k, v, d}}:
      Bool.not(Time.is_zero(d))

# One oldest inspection. Immortal or empty means stop and consumes no clock read.
def purge_needs_clock(-K: Data, -V: Data, c: Cache<K, V>) -> Bool:
  finite_entry(K, V, oldest_entry(K, V, c))

def collect_entry(-K: Data, -V: Data, entry: Maybe<&2, T.Entry<K, V>>, rest: List<&2, T.Entry<K, V>>) -> List<&2, T.Entry<K, V>>:
  match entry:
    case None{}:
      rest
    case Some{e}:
      Con{e, rest}

def entries_go(-K: Data, -V: Data, order: List<&2, String>, +table: Map<&2, Maybe<&2, T.Entry<K, V>>>) -> List<&2, T.Entry<K, V>>:
  match order:
    case Nil{}:
      Nil{}
    case Con{k, rest}:
      collect_entry(K, V, lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, k)), entries_go(K, V, rest, table))

# Raw enumeration. Public protocol Keys/Values first finish the oldest-only purge.
def entries(-K: Data, -V: Data, c: Cache<K, V>) -> List<&2, T.Entry<K, V>>:
  State{cap, table, order, life, counts, cb} = c
  entries_go(K, V, order, table)

def map_size(-K: Data, -V: Data, c: Cache<K, V>) -> Nat:
  State{cap, m, order, life, counts, cb} = c
  Map.size(&2, Maybe<&2, T.Entry<K, V>>, m)
