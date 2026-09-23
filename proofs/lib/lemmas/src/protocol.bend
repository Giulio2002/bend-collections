import Base
import ../types/model.bend as T
import ./cache.bend as C
import ./time.bend as Time
import ./entry_ops.bend as Entry

# Historical phase API retained for checked lemmas. The public runtime imports
# entry_ops directly; do not build new public behavior on this legacy protocol.

# At this explicit removal boundary the key is absent and Len is decremented,
# but Removals/Evictions/Misses/Inserts have NOT yet changed.
def detach_present(-K: Data, -V: Data, c: C.Cache<K, V>, +code: String, +entry: T.Entry<K, V>) -> C.Step<K, V>:
  C.State{cap, table, order, life, counts, +cb} = c
  C.Out{C.State{cap, Map.del(&2, Maybe<&2, T.Entry<K, V>>, table, code), C.without(order, code), life, counts, cb}, Some{entry}, True{}, C.events(K, V, cb, entry)}

def detach_found(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, found: Maybe<&2, T.Entry<K, V>>) -> C.Step<K, V>:
  match found:
    case None{}:
      C.Out{c, None{}, False{}, Nil{}}
    case Some{entry}:
      detach_present(K, V, c, code, entry)

def detach(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String) -> C.Step<K, V>:
  detach_found(K, V, c, code, C.lookup(K, V, c, code))

def detach_first(-K: Data, -V: Data, c: C.Cache<K, V>, order: List<&2, String>) -> C.Step<K, V>:
  match order:
    case Nil{}:
      C.Out{c, None{}, False{}, Nil{}}
    case Con{code, rest}:
      detach(K, V, c, code)

def detach_oldest(-K: Data, -V: Data, +c: C.Cache<K, V>) -> C.Step<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  detach_first(K, V, c, order)

def finish_removal(-K: Data, -V: Data, c: C.Cache<K, V>, evict: Bool) -> C.Cache<K, V>:
  C.State{cap, table, order, life, counts, cb} = c
  C.State{cap, table, order, life, C.removal_counts(counts, evict), cb}

def finish_miss(-K: Data, -V: Data, c: C.Cache<K, V>, tracked: Bool) -> C.Cache<K, V>:
  Entry.finish_miss(K, V, c, tracked)

def prepare_room(-K: Data, -V: Data, c: C.Cache<K, V>, full: Bool) -> C.Step<K, V>:
  match full:
    case False{}:
      C.Out{c, None{}, False{}, Nil{}}
    case True{}:
      detach_oldest(K, V, c)

def prepare_found(-K: Data, -V: Data, +c: C.Cache<K, V>, found: Maybe<&2, T.Entry<K, V>>) -> C.Step<K, V>:
  match found:
    case Some{entry}:
      C.Out{c, None{}, False{}, Nil{}}
    case None{}:
      prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)))

def prepare_add(-K: Data, -V: Data, +c: C.Cache<K, V>, code: String) -> C.Step<K, V>:
  prepare_found(K, V, c, C.lookup(K, V, c, code))

type Read<-K: Data, -V: Data> is Data:
  Reading{step: C.Step<K, V>, removed: Bool}

def expired_read(-K: Data, -V: Data, step: C.Step<K, V>) -> Read<K, V>:
  C.Out{c, item, flag, events} = step
  Reading{C.Out{c, item, False{}, events}, True{}}

def decide_read(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, tracked: Bool, expired: Bool) -> Read<K, V>:
  match expired:
    case False{}:
      Reading{C.read_live(K, V, c, code, entry, tracked), False{}}
    case True{}:
      expired_read(K, V, detach(K, V, c, code))

def read_found(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, now: T.Int64, tracked: Bool, found: Maybe<&2, T.Entry<K, V>>) -> Read<K, V>:
  match found:
    case None{}:
      Reading{C.Out{finish_miss(K, V, c, tracked), None{}, False{}, Nil{}}, False{}}
    case Some{T.Item{k, v, +d}}:
      decide_read(K, V, c, code, T.Item{k, v, d}, tracked, Time.expired(d, now))

def read(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String, now: T.Int64, tracked: Bool) -> Read<K, V>:
  read_found(K, V, c, code, now, tracked, C.lookup(K, V, c, code))

type Mode is Data:
  All{}
  Expired{}
  KeyList{}
  ValueList{}

# Closed aggregate mode prevents invalid numeric mode values.
# These are internal removal and clock requests. No user code runs at removal.
type Aggregate<-K: Data, -V: Data> is Data:
  Complete{cache: C.Cache<K, V>, keys: List<&2, K>, values: List<&2, V>}
  NeedClock{cache: C.Cache<K, V>, remaining: Nat, kind: Mode}
  RemovalReady{step: C.Step<K, V>, remaining: Nat, kind: Mode}

def keys_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, K>:
  Entry.keys_of(K, V, xs)

def values_of(-K: Data, -V: Data, xs: List<&2, T.Entry<K, V>>) -> List<&2, V>:
  Entry.values_of(K, V, xs)

def complete(-K: Data, -V: Data, +c: C.Cache<K, V>, kind: Mode) -> Aggregate<K, V>:
  match kind:
    case All{}:
      Complete{C.clear_metrics(K, V, c), Nil{}, Nil{}}
    case KeyList{}:
      Complete{c, keys_of(K, V, C.entries(K, V, c)), Nil{}}
    case ValueList{}:
      Complete{c, Nil{}, values_of(K, V, C.entries(K, V, c))}
    case Expired{}:
      Complete{c, Nil{}, Nil{}}

def need_clock(-K: Data, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: Mode, finite: Bool) -> Aggregate<K, V>:
  match finite:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      NeedClock{c, remaining, kind}

def aggregate_next(-K: Data, -V: Data, remaining: Nat, +c: C.Cache<K, V>, kind: Mode) -> Aggregate<K, V>:
  match remaining kind:
    case 0n k:
      complete(K, V, c, k)
    case 1n+p All{}:
      RemovalReady{detach_oldest(K, V, c), p, All{}}
    case 1n+p k:
      need_clock(K, V, c, p, k, C.purge_needs_clock(K, V, c))

def after_removal(-K: Data, -V: Data, remaining: Nat, c: C.Cache<K, V>, kind: Mode) -> Aggregate<K, V>:
  aggregate_next(K, V, remaining, finish_removal(K, V, c, False{}), kind)

def clock_decide(-K: Data, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: Mode, expired: Bool) -> Aggregate<K, V>:
  match expired:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      RemovalReady{detach_oldest(K, V, c), remaining, kind}

def clock_entry(-K: Data, -V: Data, c: C.Cache<K, V>, remaining: Nat, kind: Mode, now: T.Int64, entry: Maybe<&2, T.Entry<K, V>>) -> Aggregate<K, V>:
  match entry:
    case None{}:
      complete(K, V, c, kind)
    case Some{T.Item{k, v, d}}:
      clock_decide(K, V, c, remaining, kind, Time.expired(d, now))

def after_clock(-K: Data, -V: Data, +c: C.Cache<K, V>, remaining: Nat, kind: Mode, now: T.Int64) -> Aggregate<K, V>:
  clock_entry(K, V, c, remaining, kind, now, C.oldest_entry(K, V, c))

def purge(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Aggregate<K, V>:
  aggregate_next(K, V, C.len(K, V, c), c, All{})

def purge_expired(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Aggregate<K, V>:
  aggregate_next(K, V, C.len(K, V, c), c, Expired{})

def keys(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Aggregate<K, V>:
  aggregate_next(K, V, C.len(K, V, c), c, KeyList{})

def values(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Aggregate<K, V>:
  aggregate_next(K, V, C.len(K, V, c), c, ValueList{})

def refresh_prepare_found(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, found: Maybe<&2, T.Entry<K, V>>) -> C.Step<K, V>:
  Entry.refresh_prepare_found(K, V, c, code, found)

def refresh_prepare(-K: Data, -V: Data, +c: C.Cache<K, V>, +code: String) -> C.Step<K, V>:
  Entry.refresh_prepare(K, V, c, code)

def refresh_at(-K: Data, -V: Data, c: C.Cache<K, V>, code: String, entry: T.Entry<K, V>, lifetime: T.Int64, now: T.Int64) -> C.Cache<K, V>:
  Entry.refresh_at(K, V, c, code, entry, lifetime, now)

# Pure fold of detach and count-update phases. The callback-free host performs
# these internal phases without invoking user code.
def finish_detached(-K: Data, -V: Data, step: C.Step<K, V>, evict: Bool) -> C.Step<K, V>:
  C.Out{c, item, flag, events} = step
  match flag:
    case False{}:
      C.Out{c, item, False{}, events}
    case True{}:
      C.Out{finish_removal(K, V, c, evict), item, True{}, events}
