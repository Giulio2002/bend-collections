import Base
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ../src/time.bend as Time

# Legacy metadata cannot enable callbacks along the actual supported operations.
# These projections describe existing records, not an alternative cache.
def flag(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  cb

def step_flag(-K: Data, -V: Data, s: C.Step<K, V>) -> Bool:
  C.Out{c, item, found, events} = s
  flag(K, V, c)

law initial:
  for -K: Data
  for -V: Data
  for cap: Nat
  {flag(K, V, C.init(K, V, cap)) == False{} : Bool}
def initial(K, V, cap):
  {==}

law detach_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for found: Maybe<&2, T.Entry<K, V>>
  {step_flag(K, V, P.detach_found(K, V, c, code, found)) == flag(K, V, c) : Bool}
def detach_found(K, V, c, code, found):
  C.State{cap, table, order, life, counts, cb} = c
  match found:
    case None{}:
      {==}
    case Some{entry}:
      {==}

law detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  {step_flag(K, V, P.detach(K, V, c, code)) == flag(K, V, c) : Bool}
def detach(K, V, c, code):
  detach_found(K, V, c, code, C.lookup(K, V, c, code))

law detach_first:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  {step_flag(K, V, P.detach_first(K, V, c, order)) == flag(K, V, c) : Bool}
def detach_first(K, V, c, order):
  match order:
    case Nil{}:
      {==}
    case Con{code, rest}:
      detach(K, V, c, code)

law detach_oldest:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  {step_flag(K, V, P.detach_oldest(K, V, c)) == flag(K, V, c) : Bool}
def detach_oldest(K, V, c):
  C.State{cap, table, +order, life, counts, cb} = c
  detach_first(K, V, c, order)

law finish_removal:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for evict: Bool
  {flag(K, V, P.finish_removal(K, V, c, evict)) == flag(K, V, c) : Bool}
def finish_removal(K, V, c, evict):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law finish_miss:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for tracked: Bool
  {flag(K, V, P.finish_miss(K, V, c, tracked)) == flag(K, V, c) : Bool}
def finish_miss(K, V, c, tracked):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law store:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for found: Bool
  for events: List<&2, T.LruEvent<K, V>>
  {step_flag(K, V, C.store(K, V, c, code, key, value, deadline, found, events)) == flag(K, V, c) : Bool}
def store(K, V, c, code, key, value, deadline, found, events):
  C.State{cap, table, order, life, counts, cb} = c
  T.Counts{i, e, r, h, s} = counts
  {==}

law read_live:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for tracked: Bool
  {step_flag(K, V, C.read_live(K, V, c, code, entry, tracked)) == flag(K, V, c) : Bool}
def read_live(K, V, c, code, entry, tracked):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law refresh_at:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for lifetime: T.Int64
  for now: T.Int64
  {flag(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == flag(K, V, c) : Bool}
def refresh_at(K, V, c, code, entry, lifetime, now):
  C.State{cap, table, order, life, counts, cb} = c
  T.Item{k, v, old} = entry
  {==}

law set_lifetime:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for lifetime: T.Int64
  {flag(K, V, C.set_lifetime(K, V, c, lifetime)) == flag(K, V, c) : Bool}
def set_lifetime(K, V, c, lifetime):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law clear_metrics:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  {flag(K, V, C.clear_metrics(K, V, c)) == flag(K, V, c) : Bool}
def clear_metrics(K, V, c):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law prepare_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for full: Bool
  {step_flag(K, V, P.prepare_room(K, V, c, full)) == flag(K, V, c) : Bool}
def prepare_room(K, V, c, full):
  match full:
    case False{}:
      {==}
    case True{}:
      detach_oldest(K, V, c)

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for found: Maybe<&2, T.Entry<K, V>>
  {step_flag(K, V, P.prepare_found(K, V, c, found)) == flag(K, V, c) : Bool}
def prepare_found(K, V, c, found):
  match found:
    case None{}:
      prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)))
    case Some{entry}:
      {==}

law prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  {step_flag(K, V, P.prepare_add(K, V, c, code)) == flag(K, V, c) : Bool}
def prepare_add(K, V, c, code):
  prepare_found(K, V, c, C.lookup(K, V, c, code))

law remove_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  {step_flag(K, V, C.remove_found(K, V, c, code, evict, found)) == flag(K, V, c) : Bool}
def remove_found(K, V, c, code, evict, found):
  C.State{cap, table, order, life, counts, cb} = c
  match found:
    case None{}:
      {==}
    case Some{entry}:
      {==}

law remove_encoded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for evict: Bool
  {step_flag(K, V, C.remove_encoded(K, V, c, code, evict)) == flag(K, V, c) : Bool}
def remove_encoded(K, V, c, code, evict):
  remove_found(K, V, c, code, evict, C.lookup(K, V, c, code))

law oldest_remove:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for evict: Bool
  {step_flag(K, V, C.oldest_remove(K, V, c, order, evict)) == flag(K, V, c) : Bool}
def oldest_remove(K, V, c, order, evict):
  match order:
    case Nil{}:
      {==}
    case Con{code, rest}:
      remove_encoded(K, V, c, code, evict)

law remove_oldest:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for evict: Bool
  {step_flag(K, V, C.remove_oldest(K, V, c, evict)) == flag(K, V, c) : Bool}
def remove_oldest(K, V, c, evict):
  C.State{cap, table, +order, life, counts, cb} = c
  oldest_remove(K, V, c, order, evict)

law store_after_evict:
  for -K: Data
  for -V: Data
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for +step: C.Step<K, V>
  {step_flag(K, V, C.store_after_evict(K, V, code, key, value, deadline, step)) == step_flag(K, V, step) : Bool}
def store_after_evict(K, V, code, key, value, deadline, step):
  C.Out{c, item, found, events} = step
  store(K, V, c, code, key, value, deadline, found, events)

law add_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for full: Bool
  {step_flag(K, V, C.add_room(K, V, c, code, key, value, deadline, full)) == flag(K, V, c) : Bool}
def add_room(K, V, c, code, key, value, deadline, full):
  match full:
    case False{}:
      store(K, V, c, code, key, value, deadline, False{}, Nil{})
    case True{}:
      Equal.trans(Bool, step_flag(K, V, C.store_after_evict(K, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{}))), step_flag(K, V, C.remove_oldest(K, V, c, True{})), flag(K, V, c), store_after_evict(K, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{})), remove_oldest(K, V, c, True{}))

law add_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for found: Maybe<&2, T.Entry<K, V>>
  {step_flag(K, V, C.add_found(K, V, c, code, key, value, deadline, found)) == flag(K, V, c) : Bool}
def add_found(K, V, c, code, key, value, deadline, found):
  match found:
    case None{}:
      add_room(K, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)))
    case Some{T.Item{original, old, expiry}}:
      store(K, V, c, code, original, value, deadline, False{}, Nil{})

law add_with_lifetime:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for +c: C.Cache<K, V>
  for +key: K
  for value: V
  for ns: T.Int64
  for now: T.Int64
  {step_flag(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now)) == flag(K, V, c) : Bool}
def add_with_lifetime(K, V, encode, c, key, value, ns, now):
  +code = encode(key)
  add_found(K, V, c, code, key, value, Time.deadline(now, ns), C.lookup(K, V, c, code))

def read_flag(-K: Data, -V: Data, pending: P.Read<K, V>) -> Bool:
  P.Reading{step, removed} = pending
  step_flag(K, V, step)

law expired_read:
  for -K: Data
  for -V: Data
  for s: C.Step<K, V>
  {read_flag(K, V, P.expired_read(K, V, s)) == step_flag(K, V, s) : Bool}
def expired_read(K, V, s):
  C.Out{c, item, found, events} = s
  {==}

law decide_read:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for tracked: Bool
  for expired: Bool
  {read_flag(K, V, P.decide_read(K, V, c, code, entry, tracked, expired)) == flag(K, V, c) : Bool}
def decide_read(K, V, c, code, entry, tracked, expired):
  match expired:
    case False{}:
      read_live(K, V, c, code, entry, tracked)
    case True{}:
      Equal.trans(Bool, read_flag(K, V, P.expired_read(K, V, P.detach(K, V, c, code))), step_flag(K, V, P.detach(K, V, c, code)), flag(K, V, c), expired_read(K, V, P.detach(K, V, c, code)), detach(K, V, c, code))

law read_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for now: T.Int64
  for tracked: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  {read_flag(K, V, P.read_found(K, V, c, code, now, tracked, found)) == flag(K, V, c) : Bool}
def read_found(K, V, c, code, now, tracked, found):
  match found:
    case None{}:
      finish_miss(K, V, c, tracked)
    case Some{T.Item{k, v, +d}}:
      decide_read(K, V, c, code, T.Item{k, v, d}, tracked, Time.expired(d, now))

law read:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for now: T.Int64
  for tracked: Bool
  {read_flag(K, V, P.read(K, V, c, code, now, tracked)) == flag(K, V, c) : Bool}
def read(K, V, c, code, now, tracked):
  read_found(K, V, c, code, now, tracked, C.lookup(K, V, c, code))

law refresh_prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for found: Maybe<&2, T.Entry<K, V>>
  {step_flag(K, V, P.refresh_prepare_found(K, V, c, code, found)) == flag(K, V, c) : Bool}
def refresh_prepare_found(K, V, c, code, found):
  match found:
    case None{}:
      finish_miss(K, V, c, True{})
    case Some{entry}:
      read_live(K, V, c, code, entry, True{})

law refresh_prepare:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  {step_flag(K, V, P.refresh_prepare(K, V, c, code)) == flag(K, V, c) : Bool}
def refresh_prepare(K, V, c, code):
  refresh_prepare_found(K, V, c, code, C.lookup(K, V, c, code))

def aggregate_flag(-K: Data, -V: Data, a: P.Aggregate<K, V>) -> Bool:
  match a:
    case P.Complete{c, keys, values}:
      flag(K, V, c)
    case P.NeedClock{c, remaining, kind}:
      flag(K, V, c)
    case P.RemovalReady{s, remaining, kind}:
      step_flag(K, V, s)

law complete:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for kind: P.Mode
  {aggregate_flag(K, V, P.complete(K, V, c, kind)) == flag(K, V, c) : Bool}
def complete(K, V, c, kind):
  match kind:
    case P.All{}:
      clear_metrics(K, V, c)
    case P.Expired{}:
      {==}
    case P.KeyList{}:
      {==}
    case P.ValueList{}:
      {==}

law need_clock:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for finite: Bool
  {aggregate_flag(K, V, P.need_clock(K, V, c, remaining, kind, finite)) == flag(K, V, c) : Bool}
def need_clock(K, V, c, remaining, kind, finite):
  match finite:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      {==}

law aggregate_next:
  for -K: Data
  for -V: Data
  for remaining: Nat
  for +c: C.Cache<K, V>
  for kind: P.Mode
  {aggregate_flag(K, V, P.aggregate_next(K, V, remaining, c, kind)) == flag(K, V, c) : Bool}
def aggregate_next(K, V, remaining, c, kind):
  match remaining kind:
    case 0n k:
      complete(K, V, c, k)
    case 1n+p P.All{}:
      detach_oldest(K, V, c)
    case 1n+p P.Expired{}:
      need_clock(K, V, c, p, P.Expired{}, C.purge_needs_clock(K, V, c))
    case 1n+p P.KeyList{}:
      need_clock(K, V, c, p, P.KeyList{}, C.purge_needs_clock(K, V, c))
    case 1n+p P.ValueList{}:
      need_clock(K, V, c, p, P.ValueList{}, C.purge_needs_clock(K, V, c))

law after_removal:
  for -K: Data
  for -V: Data
  for remaining: Nat
  for +c: C.Cache<K, V>
  for kind: P.Mode
  {aggregate_flag(K, V, P.after_removal(K, V, remaining, c, kind)) == flag(K, V, c) : Bool}
def after_removal(K, V, remaining, c, kind):
  Equal.trans(Bool, aggregate_flag(K, V, P.after_removal(K, V, remaining, c, kind)), flag(K, V, P.finish_removal(K, V, c, False{})), flag(K, V, c), aggregate_next(K, V, remaining, P.finish_removal(K, V, c, False{}), kind), finish_removal(K, V, c, False{}))

law clock_decide:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for expired: Bool
  {aggregate_flag(K, V, P.clock_decide(K, V, c, remaining, kind, expired)) == flag(K, V, c) : Bool}
def clock_decide(K, V, c, remaining, kind, expired):
  match expired:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      detach_oldest(K, V, c)

law clock_entry:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for now: T.Int64
  for entry: Maybe<&2, T.Entry<K, V>>
  {aggregate_flag(K, V, P.clock_entry(K, V, c, remaining, kind, now, entry)) == flag(K, V, c) : Bool}
def clock_entry(K, V, c, remaining, kind, now, entry):
  match entry:
    case None{}:
      complete(K, V, c, kind)
    case Some{T.Item{k, v, d}}:
      clock_decide(K, V, c, remaining, kind, Time.expired(d, now))

law after_clock:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for now: T.Int64
  {aggregate_flag(K, V, P.after_clock(K, V, c, remaining, kind, now)) == flag(K, V, c) : Bool}
def after_clock(K, V, c, remaining, kind, now):
  clock_entry(K, V, c, remaining, kind, now, C.oldest_entry(K, V, c))
