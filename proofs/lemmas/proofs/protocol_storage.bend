import Base
import ./map_set_critbit.bend as SetCritbit
import ../src/time.bend as Time
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../types/model.bend as T
import ./refinement.bend as R
import ./map_delete_critbit.bend as D

law detach_present:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for entry: T.Entry<K, V>
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry))) == True{} : Bool}
def detach_present(K, V, c, code, entry, valid):
  C.State{cap, table, order, life, counts, cb} = c
  D.preserves_critbit(Maybe<&2, T.Entry<K, V>>, table, code, valid)

law detach_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.detach_found(K, V, c, code, found))) == True{} : Bool}
def detach_found(K, V, c, code, found, valid):
  match found:
    case None{}: valid
    case Some{entry}: detach_present(K, V, c, code, entry, valid)

law detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.detach(K, V, c, code))) == True{} : Bool}
def detach(K, V, c, code, valid):
  detach_found(K, V, c, code, C.lookup(K, V, c, code), valid)

law detach_first:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for order: List<&2, String>
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.detach_first(K, V, c, order))) == True{} : Bool}
def detach_first(K, V, c, order, valid):
  match order:
    case Nil{}: valid
    case Con{code, rest}: detach(K, V, c, code, valid)

law detach_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c))) == True{} : Bool}
def detach_oldest(K, V, c, valid):
  C.State{cap, table, +order, life, counts, cb} = c
  detach_first(K, V, C.State{cap, table, order, life, counts, cb}, order, valid)

law prepare_room:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for full: Bool
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))) == True{} : Bool}
def prepare_room(K, V, c, full, valid):
  match full:
    case False{}: valid
    case True{}: detach_oldest(K, V, c, valid)

law prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for found: Maybe<&2, T.Entry<K, V>>
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, found))) == True{} : Bool}
def prepare_found(K, V, c, found, valid):
  match found:
    case Some{entry}: valid
    case None{}: prepare_room(K, V, c, Nat.is_eq(C.len(K, V, c), C.capacity(K, V, c)), valid)

law prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for valid: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))) == True{} : Bool}
def prepare_add(K, V, c, code, valid):
  prepare_found(K, V, c, C.lookup(K, V, c, code), valid)

law finish_removal:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  {R.storage_critbit(K, V, P.finish_removal(K, V, c, evict)) == R.storage_critbit(K, V, c) : Bool}
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
  for invariant: {R.storage_critbit(K, V, c) == True{} : Bool}
  {R.storage_critbit(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}
def refresh_at(K, V, c, code, entry, lifetime, now, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  T.Item{key, value, old} = entry
  SetCritbit.preserves_critbit(Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}}, invariant)
