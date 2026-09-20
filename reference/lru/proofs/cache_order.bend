import Base
import ../src/cache.bend as C
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_lookup.bend as L
import ./map_insert.bend as I
import ./refinement.bend as F
import ./map_key_membership.bend as Keys
import ./recency_capacity.bend as Bound

def keys_in_order(-K: Data, -V: Data, c: C.Cache<K, V>) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order)

def ordered(-K: Data, -V: Data, c: C.Cache<K, V>, code: String) -> Bool:
  C.State{cap, table, order, life, counts, cb} = c
  Inv.member(order, code)

# Discharge the presence premise for successful native cache lookup using the
# actual map/order representation component, not an assumed output property.
law lookup_is_ordered:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for included: {keys_in_order(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {ordered(K, V, c, code) == True{} : Bool}
def lookup_is_ordered(K, V, c, code, entry, included, found):
  match c:
    case C.State{cap, +table, +order, life, counts, cb}:
      Keys.included_member(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order, code, included, Keys.leaf_member(T.Entry<K, V>, table, Nil{}, code, entry, L.returned_value_is_stored(T.Entry<K, V>, table, code, entry, Equal.trans(Maybe<&2, T.Entry<K, V>>, I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), Some{entry}, Equal.sym(Maybe<&2, T.Entry<K, V>>, C.lookup_result(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code)), I.lookup(Maybe<&2, T.Entry<K, V>>, None{}, table, code), F.lookup_projection_bridge(K, V, Map.get(Maybe<&2, T.Entry<K, V>>, None{}, table, code))), found))))

law replacement_ready:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for included: {keys_in_order(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  Bound.room_or_present(K, V, c, code)
def replacement_ready(K, V, c, code, entry, included, found):
  match c:
    case C.State{+cap, +table, +order, +life, +counts, +cb}:
      Inr{lookup_is_ordered(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, included, found)}

law replacement_bounded:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +original: K
  for +old: V
  for +expiry: T.Int64
  for key: K
  for value: V
  for deadline: T.Int64
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for included: {keys_in_order(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{T.Item{original, old, expiry}} : Maybe<&2, T.Entry<K, V>>}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.add_found(K, V, c, code, key, value, deadline, Some{T.Item{original, old, expiry}}))), C.capacity(K, V, c)) == True{} : Bool}
def replacement_bounded(K, V, c, code, original, old, expiry, key, value, deadline, bound, included, found):
  Bound.store_preserves_bound(K, V, c, code, original, value, deadline, False{}, Nil{}, bound, replacement_ready(K, V, c, code, T.Item{original, old, expiry}, included, found))

law live_read_does_not_grow:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +entry: T.Entry<K, V>
  for tracked: Bool
  for included: {keys_in_order(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.read_live(K, V, c, code, entry, tracked))), C.len(K, V, c)) == True{} : Bool}
def live_read_does_not_grow(K, V, c, code, entry, tracked, included, found):
  match c:
    case C.State{+cap, +table, +order, +life, +counts, +cb}:
      Bound.touch_does_not_grow(order, code, tracked, lookup_is_ordered(K, V, C.State{cap, table, order, life, counts, cb}, code, entry, included, found))
