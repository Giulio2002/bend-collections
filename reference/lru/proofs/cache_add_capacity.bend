import Base
import ../src/time.bend as Time
import ../src/cache.bend as C
import ../types/model.bend as T
import ./cache_oldest_available.bend as O
import ./cache_prepare_capacity.bend as Prep
import ./cache_populated.bend as Pop
import ./cache_order.bend as Order
import ./refinement.bend as F
import ./recency_capacity.bend as Bound
import ./recency_bounds.bend as B
import ./map_routing.bend as R

law evict_then_store_bounded:
  for -K: Data
  for -V: Data
  for +cap: Nat
  for +table: Map<&2, Maybe<&2, T.Entry<K, V>>>
  for +oldest: String
  for +rest: List<&2, String>
  for +life: T.Int64
  for counts: T.Metrics
  for +cb: Bool
  for +code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for bound: {Nat.is_le(1n+List.length(&2, String, rest), cap) == True{} : Bool}
  for w: O.available(K, V, C.State{cap, table, Con{oldest, rest}, life, counts, cb}, oldest)
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, C.State{cap, table, Con{oldest, rest}, life, counts, cb}, code, key, value, deadline, True{}))), cap) == True{} : Bool}
def evict_then_store_bounded(K, V, cap, table, oldest, rest, life, counts, cb, code, key, value, deadline, bound, w):
  T.Counts{+i, +e, +r, +h, +misses} = counts
  (+entry, found) = w
  %Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup(K, V, C.State{cap, table, Con{oldest, rest}, life, T.Counts{i, e, r, h, misses}, cb}, oldest), Some{entry}, found) : {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store_after_evict(K, V, code, key, value, deadline, C.remove_found(K, V, C.State{cap, table, Con{oldest, rest}, life, T.Counts{i, e, r, h, misses}, cb}, oldest, True{}, _)))), cap) == True{} : Bool}
  Bound.move_with_room(C.without(Con{oldest, rest}, oldest), code, cap, B.le_transitive(1n+List.length(&2, String, C.without(Con{oldest, rest}, oldest)), 1n+List.length(&2, String, rest), cap, Bound.present_frees_slot(Con{oldest, rest}, oldest, O.head_member(oldest, rest)), bound))

law full_add_bounded:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for full: {Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, c, code, key, value, deadline, True{}))), C.capacity(K, V, c)) == True{} : Bool}
def full_add_bounded(K, V, c, code, key, value, deadline, positive, bound, full, valid, populated, included):
  match c:
    case C.State{cap, +table, order, +life, +counts, +cb}:
      match cap order:
        case 0n xs:
          Empty.absurd({Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, C.State{0n, table, xs, life, counts, cb}, code, key, value, deadline, True{}))), 0n) == True{} : Bool}, R.false_true(positive))
        case 1n++n Nil{}:
          Empty.absurd({Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, C.State{1n+n, table, Nil{}, life, counts, cb}, code, key, value, deadline, True{}))), 1n+n) == True{} : Bool}, R.false_true(full))
        case 1n++n Con{+oldest, +rest}:
          evict_then_store_bounded(K, V, 1n+n, table, oldest, rest, life, counts, cb, code, key, value, deadline, bound, O.ordered_lookup(K, V, C.State{1n+n, table, Con{oldest, rest}, life, counts, cb}, oldest, valid, populated, included, O.head_member(oldest, rest)))

law room_ready:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for room: {Nat.is_le(1n+C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  Bound.room_or_present(K, V, c, code)
def room_ready(K, V, c, code, room):
  C.State{cap, table, order, life, counts, cb} = c
  Inl{room}

law room_branch_bounded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for full: Bool
  for decision: {Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)) == full : Bool}
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_room(K, V, c, code, key, value, deadline, full))), C.capacity(K, V, c)) == True{} : Bool}
def room_branch_bounded(K, V, c, code, key, value, deadline, full, decision, positive, bound, valid, populated, included):
  match full:
    case False{}:
      Bound.store_preserves_bound(K, V, c, code, key, value, deadline, False{}, Nil{}, bound, room_ready(K, V, c, code, Prep.not_full_has_room(C.len(K, V, c), C.capacity(K, V, c), decision)))
    case True{}:
      full_add_bounded(K, V, c, code, key, value, deadline, positive, bound, decision, valid, populated, included)

law found_branch_bounded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for found: Maybe<&2, T.Entry<K, V>>
  for decision: {C.lookup(K, V, c, code) == found : Maybe<&2, T.Entry<K, V>>}
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  for reverse: {Order.keys_in_order(K, V, c) == True{} : Bool}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_found(K, V, c, code, key, value, deadline, found))), C.capacity(K, V, c)) == True{} : Bool}
def found_branch_bounded(K, V, c, code, key, value, deadline, found, decision, positive, bound, valid, populated, included, reverse):
  match found:
    case None{}:
      room_branch_bounded(K, V, c, code, key, value, deadline, Nat.is_ge(C.len(K, V, c), C.capacity(K, V, c)), {==}, positive, bound, valid, populated, included)
    case Some{T.Item{original, old, expiry}}:
      Order.replacement_bounded(K, V, c, code, original, old, expiry, key, value, deadline, bound, reverse, decision)

# This is a capacity theorem for the actual complete AddWithLifetime core,
# not yet a joint representation or observable-refinement theorem.
law add_with_lifetime_bounded:
  for -K: Data
  for -V: Data
  for encode: K -> String
  for +c: C.Cache<K, V>
  for +key: K
  for value: V
  for ns: T.Int64
  for now: T.Int64
  for positive: {Nat.is_gt(C.capacity(K, V, c), 0n) == True{} : Bool}
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for populated: {Pop.storage_populated(K, V, c) == True{} : Bool}
  for included: {O.order_in_keys(K, V, c) == True{} : Bool}
  for reverse: {Order.keys_in_order(K, V, c) == True{} : Bool}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_with_lifetime(K, V, encode, c, key, value, ns, now))), C.capacity(K, V, c)) == True{} : Bool}
def add_with_lifetime_bounded(K, V, encode, c, key, value, ns, now, positive, bound, valid, populated, included, reverse):
  +code = encode(key)
  found_branch_bounded(K, V, c, code, key, value, Time.deadline(now, ns), C.lookup(K, V, c, code), {==}, positive, bound, valid, populated, included, reverse)
