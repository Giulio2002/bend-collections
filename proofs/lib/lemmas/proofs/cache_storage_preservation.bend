import Base
import ./map_keys_unique.bend as UniqueKeys
import ./invariants.bend as Inv
import ./cache_refresh_membership.bend as Refresh
import ../src/protocol.bend as P
import ./protocol_storage.bend as PS
import ../src/cache.bend as C
import ../src/time.bend as Time
import ../types/model.bend as T
import ./refinement.bend as F
import ./cache_populated.bend as Pop
import ./cache_delete_membership.bend as D
import ./cache_store_membership.bend as S
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And

# Storage component only: this deliberately does not claim full representation.
def storage(-K: Data, -V: Data, +c: C.Cache<K, V>) -> Bool:
  F.storage_critbit(K, V, c) && (Pop.storage_populated(K, V, c) && D.membership(K, V, c))

law initial:
  for -K: Data
  for -V: Data
  for cap: Nat
  {storage(K, V, C.init(K, V, cap)) == True{} : Bool}
def initial(K, V, cap):
  {==}

law pack:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {D.membership(K, V, c) == True{} : Bool}
  {storage(K, V, c) == True{} : Bool}
def pack(K, V, c, valid, populated, included):
  And.conjunction(F.storage_critbit(K, V, c), Pop.storage_populated(K, V, c) && D.membership(K, V, c), valid, And.conjunction(Pop.storage_populated(K, V, c), D.membership(K, V, c), populated, included))

law valid:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for invariant: {storage(K, V, c) == True{} : Bool}
  {F.storage_critbit(K, V, c) == True{} : Bool}
def valid(K, V, c, invariant):
  R.and_left(F.storage_critbit(K, V, c), Pop.storage_populated(K, V, c) && D.membership(K, V, c), invariant)

law populated:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for invariant: {storage(K, V, c) == True{} : Bool}
  {Pop.storage_populated(K, V, c) == True{} : Bool}
def populated(K, V, c, invariant):
  R.and_left(Pop.storage_populated(K, V, c), D.membership(K, V, c), R.and_right(F.storage_critbit(K, V, c), Pop.storage_populated(K, V, c) && D.membership(K, V, c), invariant))

law membership:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for invariant: {storage(K, V, c) == True{} : Bool}
  {D.membership(K, V, c) == True{} : Bool}
def membership(K, V, c, invariant):
  R.and_right(Pop.storage_populated(K, V, c), D.membership(K, V, c), R.and_right(F.storage_critbit(K, V, c), Pop.storage_populated(K, V, c) && D.membership(K, V, c), invariant))

law remove_populated:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  for invariant: {Pop.storage_populated(K, V, c) == True{} : Bool}
  {Pop.storage_populated(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == True{} : Bool}
def remove_populated(K, V, c, code, evict, entry, invariant):
  C.State{cap, table, order, life, counts, cb} = c
  Pop.detach_present(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, invariant)

law remove_present:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +evict: Bool
  for +entry: T.Entry<K, V>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))) == True{} : Bool}
def remove_present(K, V, c, code, evict, entry, invariant):
  pack(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry)),
    F.removal_preserves_storage_critbit(K, V, c, code, evict, entry, valid(K, V, c, invariant)),
    remove_populated(K, V, c, code, evict, entry, populated(K, V, c, invariant)),
    D.core_remove_present(K, V, c, code, evict, entry, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law remove_found:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for found: Maybe<&2, T.Entry<K, V>>
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.remove_found(K, V, c, code, evict, found))) == True{} : Bool}
def remove_found(K, V, c, code, evict, found, invariant):
  match found:
    case None{}: invariant
    case Some{entry}: remove_present(K, V, c, code, evict, entry, invariant)

law remove_encoded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for evict: Bool
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.remove_encoded(K, V, c, code, evict))) == True{} : Bool}
def remove_encoded(K, V, c, code, evict, invariant):
  remove_found(K, V, c, code, evict, C.lookup(K, V, c, code), invariant)

law oldest_remove:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for order: List<&2, String>
  for evict: Bool
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.oldest_remove(K, V, c, order, evict))) == True{} : Bool}
def oldest_remove(K, V, c, order, evict, invariant):
  match order:
    case Nil{}: invariant
    case Con{code, rest}: remove_encoded(K, V, c, code, evict, invariant)

law remove_oldest:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.remove_oldest(K, V, c, evict))) == True{} : Bool}
def remove_oldest(K, V, c, evict, invariant):
  C.State{cap, table, +order, life, counts, cb} = c
  oldest_remove(K, V, C.State{cap, table, order, life, counts, cb}, order, evict, invariant)

law store:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +key: K
  for +value: V
  for +deadline: T.Int64
  for +flag: Bool
  for +events: List<&2, T.Event<K, V>>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}
def store(K, V, c, code, key, value, deadline, flag, events, invariant):
  pack(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events)),
    F.store_preserves_storage_critbit(K, V, c, code, key, value, deadline, flag, events, valid(K, V, c, invariant)),
    Pop.store_preserves_populated(K, V, c, code, key, value, deadline, flag, events, populated(K, V, c, invariant)),
    S.store(K, V, c, code, key, value, deadline, flag, events, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law store_after_evict:
  for -K: Data
  for -V: Data
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for step: C.Step<K, V>
  for invariant: {storage(K, V, C.step_cache(K, V, step)) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.store_after_evict(K, V, code, key, value, deadline, step))) == True{} : Bool}
def store_after_evict(K, V, code, key, value, deadline, step, invariant):
  C.Out{c, item, flag, events} = step
  store(K, V, c, code, key, value, deadline, flag, events, invariant)

law add_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for full: Bool
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.add_room(K, V, c, code, key, value, deadline, full))) == True{} : Bool}
def add_room(K, V, c, code, key, value, deadline, full, invariant):
  match full:
    case False{}: store(K, V, c, code, key, value, deadline, False{}, Nil{}, invariant)
    case True{}: store_after_evict(K, V, code, key, value, deadline, C.remove_oldest(K, V, c, True{}), remove_oldest(K, V, c, True{}, invariant))

law add_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for found: Maybe<&2, T.Entry<K, V>>
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.add_found(K, V, c, code, key, value, deadline, found))) == True{} : Bool}
def add_found(K, V, c, code, key, value, deadline, found, invariant):
  match found:
    case None{}: add_room(K, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)), invariant)
    case Some{T.Item{original, old, expiry}}: store(K, V, c, code, original, value, deadline, False{}, Nil{}, invariant)

law add_with_lifetime:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for +c: C.Cache<K, V>
  for +key: K
  for value: V
  for ns: T.Int64
  for now: T.Int64
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))) == True{} : Bool}
def add_with_lifetime(K, V, encode, c, key, value, ns, now, invariant):
  +code = encode(key)
  add_found(K, V, c, code, key, value, Time.deadline(now, ns), C.lookup(K, V, c, code), invariant)

law protocol_detach_present:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry))) == True{} : Bool}
def protocol_detach_present(K, V, c, code, entry, invariant):
  pack(K, V, C.step_cache(K, V, P.detach_present(K, V, c, code, entry)),
    PS.detach_present(K, V, c, code, entry, valid(K, V, c, invariant)),
    Pop.detach_present(K, V, c, code, entry, populated(K, V, c, invariant)),
    D.detach_present(K, V, c, code, entry, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_detach_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +found: Maybe<&2, T.Entry<K, V>>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.detach_found(K, V, c, code, found))) == True{} : Bool}
def protocol_detach_found(K, V, c, code, found, invariant):
  pack(K, V, C.step_cache(K, V, P.detach_found(K, V, c, code, found)),
    PS.detach_found(K, V, c, code, found, valid(K, V, c, invariant)),
    Pop.detach_found(K, V, c, code, found, populated(K, V, c, invariant)),
    D.detach_found(K, V, c, code, found, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_detach:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.detach(K, V, c, code))) == True{} : Bool}
def protocol_detach(K, V, c, code, invariant):
  pack(K, V, C.step_cache(K, V, P.detach(K, V, c, code)),
    PS.detach(K, V, c, code, valid(K, V, c, invariant)),
    Pop.detach(K, V, c, code, populated(K, V, c, invariant)),
    D.detach(K, V, c, code, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_detach_first:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +order: List<&2, String>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.detach_first(K, V, c, order))) == True{} : Bool}
def protocol_detach_first(K, V, c, order, invariant):
  pack(K, V, C.step_cache(K, V, P.detach_first(K, V, c, order)),
    PS.detach_first(K, V, c, order, valid(K, V, c, invariant)),
    Pop.detach_first(K, V, c, order, populated(K, V, c, invariant)),
    D.detach_first(K, V, c, order, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_detach_oldest:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c))) == True{} : Bool}
def protocol_detach_oldest(K, V, c, invariant):
  pack(K, V, C.step_cache(K, V, P.detach_oldest(K, V, c)),
    PS.detach_oldest(K, V, c, valid(K, V, c, invariant)),
    Pop.detach_oldest(K, V, c, populated(K, V, c, invariant)),
    D.detach_oldest(K, V, c, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_prepare_room:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +full: Bool
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full))) == True{} : Bool}
def protocol_prepare_room(K, V, c, full, invariant):
  pack(K, V, C.step_cache(K, V, P.prepare_room(K, V, c, full)),
    PS.prepare_room(K, V, c, full, valid(K, V, c, invariant)),
    Pop.prepare_room(K, V, c, full, populated(K, V, c, invariant)),
    D.prepare_room(K, V, c, full, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_prepare_found:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +found: Maybe<&2, T.Entry<K, V>>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, found))) == True{} : Bool}
def protocol_prepare_found(K, V, c, found, invariant):
  pack(K, V, C.step_cache(K, V, P.prepare_found(K, V, c, found)),
    PS.prepare_found(K, V, c, found, valid(K, V, c, invariant)),
    Pop.prepare_found(K, V, c, found, populated(K, V, c, invariant)),
    D.prepare_found(K, V, c, found, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law protocol_prepare_add:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code))) == True{} : Bool}
def protocol_prepare_add(K, V, c, code, invariant):
  pack(K, V, C.step_cache(K, V, P.prepare_add(K, V, c, code)),
    PS.prepare_add(K, V, c, code, valid(K, V, c, invariant)),
    Pop.prepare_add(K, V, c, code, populated(K, V, c, invariant)),
    D.prepare_add(K, V, c, code, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant)))

law add:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for c: C.Cache<K, V>
  for key: K
  for value: V
  for now: T.Int64
  for invariant: {storage(K, V, c) == True{} : Bool}
  {storage(K, V, C.step_cache(K, V, C.add(K, V, encode, c, key, value, now))) == True{} : Bool}
def add(K, V, encode, c, key, value, now, invariant):
  C.State{cap, table, order, +life, counts, cb} = c
  add_with_lifetime(K, V, encode, C.State{cap, table, order, life, counts, cb}, key, value, life, now, invariant)

law finish_removal:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for evict: Bool
  {storage(K, V, P.finish_removal(K, V, c, evict)) == storage(K, V, c) : Bool}
def finish_removal(K, V, c, evict):
  C.State{cap, table, order, life, counts, cb} = c
  {==}

law refresh_at:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for +lifetime: T.Int64
  for +now: T.Int64
  for +invariant: {storage(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {storage(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}
def refresh_at(K, V, c, code, entry, lifetime, now, invariant, found):
  pack(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now),
    PS.refresh_at(K, V, c, code, entry, lifetime, now, valid(K, V, c, invariant)),
    Pop.refresh_at(K, V, c, code, entry, lifetime, now, populated(K, V, c, invariant)),
    Refresh.refresh_at(K, V, c, code, entry, lifetime, now, valid(K, V, c, invariant), populated(K, V, c, invariant), membership(K, V, c, invariant), found))

def native_keys_unique(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Inv.unique(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table))

# Native key uniqueness is derived from the proved storage component, rather
# than supplied as another preservation premise.
law storage_has_unique_keys:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +invariant: {storage(K, V, c) == True{} : Bool}
  {native_keys_unique(K, V, c) == True{} : Bool}
def storage_has_unique_keys(K, V, c, invariant):
  C.State{+cap, +table, +order, +life, +counts, +cb} = c
  UniqueKeys.unique_keys(T.Entry<K, V>, table,
    valid(K, V, C.State{cap, table, order, life, counts, cb}, invariant),
    populated(K, V, C.State{cap, table, order, life, counts, cb}, invariant))
