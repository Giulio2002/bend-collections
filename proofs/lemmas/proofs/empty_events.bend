import Base
import ../src/time.bend as S
import ../types/model.bend as T
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ./disabled.bend as D

# Existing host commit rejects nonempty legacy metadata. These laws show its
# event check cannot reject these actual protocol steps from disabled states.
# They do not prove the TypeScript commit/dispatch bridge.
def empty(-K: Data, -V: Data, step: C.Step<K, V>) -> Type:
  {C.step_events(K, V, step) == Nil{} : List<&2, T.Event<K, V>>}

law detach_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.detach_present(K, V, c, code, entry))
def detach_present(K, V, c, code, entry, disabled):
  C.State{cap, table, order, life, counts, cb} = c
  Equal.cong(Bool, List<&2, T.Event<K, V>>, b => C.events(K, V, b, entry), cb, False{}, disabled)

law detach_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for found: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.detach_found(K, V, c, code, found))
def detach_found(K, V, c, code, found, disabled):
  match found:
    case None{}:
      {==}
    case Some{entry}:
      detach_present(K, V, c, code, entry, disabled)

law detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.detach(K, V, c, code))
def detach(K, V, c, code, disabled):
  detach_found(K, V, c, code, C.lookup(K, V, c, code), disabled)

law detach_first:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.detach_first(K, V, c, order))
def detach_first(K, V, c, order, disabled):
  match order:
    case Nil{}:
      {==}
    case Con{code, rest}:
      detach(K, V, c, code, disabled)

law detach_oldest:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.detach_oldest(K, V, c))
def detach_oldest(K, V, c, disabled):
  C.State{cap, table, order, life, counts, cb} = c
  detach_first(K, V, c, order, disabled)

law prepare_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for full: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.prepare_room(K, V, c, full))
def prepare_room(K, V, c, full, disabled):
  match full:
    case False{}:
      {==}
    case True{}:
      detach_oldest(K, V, c, disabled)

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for found: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.prepare_found(K, V, c, found))
def prepare_found(K, V, c, found, disabled):
  match found:
    case None{}:
      prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), disabled)
    case Some{entry}:
      {==}

law prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, P.prepare_add(K, V, c, code))
def prepare_add(K, V, c, code, disabled):
  prepare_found(K, V, c, C.lookup(K, V, c, code), disabled)

law live:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for tracked: Bool
  empty(K, V, C.read_live(K, V, c, code, entry, tracked))
def live(K, V, c, code, entry, tracked):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

def read_empty(-K: Data, -V: Data, reading: P.Read<K, V>) -> Type:
  P.Reading{step, removed} = reading
  empty(K, V, step)

law expired:
  for -K: Data
  for -V: Data
  for step: C.Step<K, V>
  for no_events: empty(K, V, step)
  read_empty(K, V, P.expired_read(K, V, step))
def expired(K, V, step, no_events):
  C.Out{c, item, flag, events} = step
  no_events

law decide:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for tracked: Bool
  for expired: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  read_empty(K, V, P.decide_read(K, V, c, code, entry, tracked, expired))
def decide(K, V, c, code, entry, tracked, exp, disabled):
  match exp:
    case False{}:
      live(K, V, c, code, entry, tracked)
    case True{}:
      expired(K, V, P.detach(K, V, c, code), detach(K, V, c, code, disabled))

law read_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for now: T.Int64
  for tracked: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  read_empty(K, V, P.read_found(K, V, c, code, now, tracked, found))
def read_found(K, V, c, code, now, tracked, found, disabled):
  match found:
    case None{}:
      {==}
    case Some{T.Item{k, v, +d}}:
      decide(K, V, c, code, T.Item{k, v, d}, tracked, S.expired(d, now), disabled)

law read:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for now: T.Int64
  for tracked: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  read_empty(K, V, P.read(K, V, c, code, now, tracked))
def read(K, V, c, code, now, tracked, disabled):
  read_found(K, V, c, code, now, tracked, C.lookup(K, V, c, code), disabled)

def aggregate_empty(-K: Data, -V: Data, result: P.Aggregate<K, V>) -> Type:
  match result:
    case P.Complete{c, keys, values}:
      Unit
    case P.NeedClock{c, remaining, kind}:
      Unit
    case P.RemovalReady{step, remaining, kind}:
      empty(K, V, step)

law complete:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for kind: P.Mode
  aggregate_empty(K, V, P.complete(K, V, c, kind))
def complete(K, V, c, kind):
  match kind:
    case P.All{}: Unit{}
    case P.Expired{}: Unit{}
    case P.KeyList{}: Unit{}
    case P.ValueList{}: Unit{}

law need_clock:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for finite: Bool
  aggregate_empty(K, V, P.need_clock(K, V, c, remaining, kind, finite))
def need_clock(K, V, c, remaining, kind, finite):
  match finite:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      Unit{}

law aggregate_next:
  for -K: Data
  for -V: Data
  for remaining: Nat
  for +c: C.Cache<K, V>
  for kind: P.Mode
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  aggregate_empty(K, V, P.aggregate_next(K, V, remaining, c, kind))
def aggregate_next(K, V, remaining, c, kind, disabled):
  match remaining kind:
    case 0n k:
      complete(K, V, c, k)
    case 1n+p P.All{}:
      detach_oldest(K, V, c, disabled)
    case 1n+p P.Expired{}:
      need_clock(K, V, c, p, P.Expired{}, C.purge_needs_clock(K, V, c))
    case 1n+p P.KeyList{}:
      need_clock(K, V, c, p, P.KeyList{}, C.purge_needs_clock(K, V, c))
    case 1n+p P.ValueList{}:
      need_clock(K, V, c, p, P.ValueList{}, C.purge_needs_clock(K, V, c))

law clock_decide:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for expired: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  aggregate_empty(K, V, P.clock_decide(K, V, c, remaining, kind, expired))
def clock_decide(K, V, c, remaining, kind, exp, disabled):
  match exp:
    case False{}:
      complete(K, V, c, kind)
    case True{}:
      detach_oldest(K, V, c, disabled)

law clock_entry:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for now: T.Int64
  for entry: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  aggregate_empty(K, V, P.clock_entry(K, V, c, remaining, kind, now, entry))
def clock_entry(K, V, c, remaining, kind, now, entry, disabled):
  match entry:
    case None{}:
      complete(K, V, c, kind)
    case Some{T.Item{k, v, d}}:
      clock_decide(K, V, c, remaining, kind, S.expired(d, now), disabled)

law after_clock:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for remaining: Nat
  for kind: P.Mode
  for now: T.Int64
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  aggregate_empty(K, V, P.after_clock(K, V, c, remaining, kind, now))
def after_clock(K, V, c, remaining, kind, now, disabled):
  clock_entry(K, V, c, remaining, kind, now, C.oldest_entry(K, V, c), disabled)

law after_removal:
  for -K: Data
  for -V: Data
  for remaining: Nat
  for +c: C.Cache<K, V>
  for kind: P.Mode
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  aggregate_empty(K, V, P.after_removal(K, V, remaining, c, kind))
def after_removal(K, V, remaining, c, kind, disabled):
  aggregate_next(K, V, remaining, P.finish_removal(K, V, c, False{}), kind, Equal.trans(Bool, D.flag(K, V, P.finish_removal(K, V, c, False{})), D.flag(K, V, c), False{}, D.finish_removal(K, V, c, False{}), disabled))

law refresh_found:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for found: Maybe<&2, T.Entry<K, V>>
  empty(K, V, P.refresh_prepare_found(K, V, c, code, found))
def refresh_found(K, V, c, code, found):
  match found:
    case None{}:
      {==}
    case Some{entry}:
      live(K, V, c, code, entry, True{})

law refresh_prepare:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  empty(K, V, P.refresh_prepare(K, V, c, code))
def refresh_prepare(K, V, c, code):
  refresh_found(K, V, c, code, C.lookup(K, V, c, code))

law remove_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for +entry: T.Entry<K, V>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.remove_present(K, V, c, code, evict, entry))
def remove_present(K, V, c, code, evict, entry, disabled):
  C.State{cap, table, order, life, counts, cb} = c
  Equal.cong(Bool, List<&2, T.Event<K, V>>, b => C.events(K, V, b, entry), cb, False{}, disabled)

law remove_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.remove_found(K, V, c, code, evict, found))
def remove_found(K, V, c, code, evict, found, disabled):
  match found:
    case None{}:
      {==}
    case Some{entry}:
      remove_present(K, V, c, code, evict, entry, disabled)

law oldest_remove:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for evict: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.oldest_remove(K, V, c, order, evict))
def oldest_remove(K, V, c, order, evict, disabled):
  match order:
    case Nil{}:
      {==}
    case Con{+code, rest}:
      remove_found(K, V, c, code, evict, C.lookup(K, V, c, code), disabled)

law remove_oldest:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for evict: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.remove_oldest(K, V, c, evict))
def remove_oldest(K, V, c, evict, disabled):
  C.State{cap, table, order, life, counts, cb} = c
  oldest_remove(K, V, c, order, evict, disabled)

law store:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.Event<K, V>>
  {C.step_events(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)) == events : List<&2, T.Event<K, V>>}
def store(K, V, c, code, key, value, deadline, flag, events):
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  {==}

law after_evict:
  for -K: Data
  for -V: Data
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for step: C.Step<K, V>
  for no_events: empty(K, V, step)
  empty(K, V, C.store_after_evict(K, V, code, key, value, deadline, step))
def after_evict(K, V, code, key, value, deadline, step, no_events):
  C.Out{+c, item, +flag, +events} = step
  Equal.trans(List<&2, T.Event<K, V>>, C.step_events(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)), events, Nil{}, store(K, V, c, code, key, value, deadline, flag, events), no_events)

law add_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for full: Bool
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.add_room(K, V, c, code, key, value, deadline, full))
def add_room(K, V, c, code, key, value, deadline, full, disabled):
  match full:
    case False{}:
      store(K, V, c, code, key, value, deadline, False{}, Nil{})
    case True{}:
      after_evict(K, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{}), remove_oldest(K, V, c, True{}, disabled))

law add_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for found: Maybe<&2, T.Entry<K, V>>
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.add_found(K, V, c, code, key, value, deadline, found))
def add_found(K, V, c, code, key, value, deadline, found, disabled):
  match found:
    case None{}:
      add_room(K, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)), disabled)
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
  for disabled: {D.flag(K, V, c) == False{} : Bool}
  empty(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))
def add_with_lifetime(K, V, encode, c, key, value, ns, now, disabled):
  +code = encode(key)
  add_found(K, V, c, code, key, value, S.deadline(now, ns), C.lookup(K, V, c, code), disabled)
