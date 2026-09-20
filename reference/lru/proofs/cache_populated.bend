import Base
import ./map_populated.bend as Pop
import ../src/time.bend as Time
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./map_delete_populated.bend as D

# This component excludes stored None. It does not imply key identity or recency.
def storage_populated(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Pop.populated(T.Entry<K, V>, table)

law initial_populated:
  for -K: Data
  for -V: Data
  for cap: Nat
  {storage_populated(K, V, C.init(K, V, cap)) == True{} : Bool}
def initial_populated(K, V, cap):
  {==}

law detach_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry))) == True{} : Bool}
def detach_present(K, V, c, code, entry, valid):
  C.State{cap, table, order, life, counts, cb} = c
  D.preserves_populated(T.Entry<K, V>, table, code, valid)

law detach_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.detach_found(K, V, c, code, found))) == True{} : Bool}
def detach_found(K, V, c, code, found, valid):
  match found:
    case None{}: valid
    case Some{entry}: detach_present(K, V, c, code, entry, valid)

law detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.detach(K, V, c, code))) == True{} : Bool}
def detach(K, V, c, code, valid):
  detach_found(K, V, c, code, C.lookup(K, V, c, code), valid)

law detach_first:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.detach_first(K, V, c, order))) == True{} : Bool}
def detach_first(K, V, c, order, valid):
  match order:
    case Nil{}: valid
    case Con{code, rest}: detach(K, V, c, code, valid)

law detach_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c))) == True{} : Bool}
def detach_oldest(K, V, c, valid):
  C.State{cap, table, +order, life, counts, cb} = c
  detach_first(K, V, C.State{cap, table, order, life, counts, cb}, order, valid)

law prepare_room:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for full: Bool
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))) == True{} : Bool}
def prepare_room(K, V, c, full, valid):
  match full:
    case False{}: valid
    case True{}: detach_oldest(K, V, c, valid)

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, found))) == True{} : Bool}
def prepare_found(K, V, c, found, valid):
  match found:
    case Some{entry}: valid
    case None{}: prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), valid)

law prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for valid: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))) == True{} : Bool}
def prepare_add(K, V, c, code, valid):
  prepare_found(K, V, c, C.lookup(K, V, c, code), valid)

law finish_removal:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  {storage_populated(K, V, P.finish_removal(K, V, c, evict)) == storage_populated(K, V, c) : Bool}
def finish_removal(K, V, c, evict):
  C.State{cap, table, order, life, counts, cb} = c
  {==}


law refresh_at:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for lifetime: T.Int64
  for now: T.Int64
  for invariant: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}
def refresh_at(K, V, c, code, entry, lifetime, now, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  T.Item{key, value, old} = entry
  Pop.set_preserves_populated(T.Entry<K, V>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}}, {==}, invariant)

law store_preserves_populated:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.Event<K, V>>
  for invariant: {storage_populated(K, V, c) == True{} : Bool}
  {storage_populated(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}
def store_preserves_populated(K, V, c, code, key, value, deadline, flag, events, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  T.Counts{i, e, r, h, misses} = counts
  Pop.set_preserves_populated(T.Entry<K, V>, table, code, Some{T.Item{key, value, deadline}}, {==}, invariant)

