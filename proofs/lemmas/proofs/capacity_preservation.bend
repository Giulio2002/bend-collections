import Base
import ../src/cache.bend as C
import ../types/model.bend as T

law remove_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  {C.capacity(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == C.capacity(K, V, c) : Nat}
def remove_present(K, V, c, code, evict, entry):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law remove_found:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  {C.capacity(K, V, C.step_cache(K, V, C.remove_found(K, V, c, code, evict, found))) == C.capacity(K, V, c) : Nat}
def remove_found(K, V, c, code, evict, found):
  match found:
    case None{}: {==}
    case Some{entry}: remove_present(K, V, c, code, evict, entry)

law oldest_remove:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for evict: Bool
  {C.capacity(K, V, C.step_cache(K, V, C.oldest_remove(K, V, c, order, evict))) == C.capacity(K, V, c) : Nat}
def oldest_remove(K, V, c, order, evict):
  match order:
    case Nil{}: {==}
    case Con{+code, tail}: remove_found(K, V, c, code, evict, C.lookup(K, V, c, code))

law remove_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  {C.capacity(K, V, C.step_cache(K, V, C.remove_oldest(K, V, c, evict))) == C.capacity(K, V, c) : Nat}
def remove_oldest(K, V, c, evict):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  oldest_remove(K, V, C.State{cap, table, order, life, counts, cb}, order, evict)

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
  {C.capacity(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == C.capacity(K, V, c) : Nat}
def store(K, V, c, code, key, value, deadline, flag, events):
  C.State{cap, table, order, life, T.Counts{i, e, r, h, m}, cb} = c
  {==}
