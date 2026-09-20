import Base
import ./map_enumeration.bend as E
import ../src/cache.bend as C
import ../src/protocol.bend as P
import ../src/time.bend as Time
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_set_membership.bend as Set
import ./map_populated.bend as Pop
import ./map_key_membership.bend as Keys
import ./map_lookup.bend as L
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./cache_delete_membership.bend as D
import ./cache_populated.bend as Packed
import ./refinement.bend as F

law into_updated:
  for -V: Data
  for xs: List<&2, String>
  for +table: Map<&2, Maybe<&2, V>>
  for +code: String
  for +value: V
  for +valid: {Inv.critbit(Maybe<&2, V>, table) == True{} : Bool}
  for +populated: {Pop.populated(V, table) == True{} : Bool}
  for +present: {Inv.member(Map.keys(&2, Maybe<&2, V>, table), code) == True{} : Bool}
  for +included: {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, table)) == True{} : Bool}
  {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))) == True{} : Bool}
def into_updated(V, xs, table, code, value, valid, populated, present, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))),
        Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.member(Map.keys(&2, Maybe<&2, V>, table), head), True{}, Set.existing(V, table, code, value, head, valid, populated, present), R.and_left(Inv.member(Map.keys(&2, Maybe<&2, V>, table), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, table)), included)),
        into_updated(V, tail, table, code, value, valid, populated, present, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, V>, table), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, table)), included)))

law from_updated:
  for -V: Data
  for xs: List<&2, String>
  for +table: Map<&2, Maybe<&2, V>>
  for +code: String
  for +value: V
  for +order: List<&2, String>
  for +valid: {Inv.critbit(Maybe<&2, V>, table) == True{} : Bool}
  for +populated: {Pop.populated(V, table) == True{} : Bool}
  for +present: {Inv.member(Map.keys(&2, Maybe<&2, V>, table), code) == True{} : Bool}
  for +included: {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))) == True{} : Bool}
  for +ordered: {Inv.included(Map.keys(&2, Maybe<&2, V>, table), order) == True{} : Bool}
  {Inv.included(xs, order) == True{} : Bool}
def from_updated(V, xs, table, code, value, order, valid, populated, present, included, ordered):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(order, head), Inv.included(tail, order),
        Keys.included_member(Map.keys(&2, Maybe<&2, V>, table), order, head, ordered,
          Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, table), head), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), True{}, Equal.sym(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.member(Map.keys(&2, Maybe<&2, V>, table), head), Set.existing(V, table, code, value, head, valid, populated, present)), R.and_left(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))), included))),
        from_updated(V, tail, table, code, value, order, valid, populated, present, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))), included), ordered))

# Refresh updates only an already stored code; successful actual lookup discharges
# that premise. The prior entry may be expired: no expiry assumption is needed.
law refresh_at:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for entry: T.Entry<K, V>
  for +lifetime: T.Int64
  for +now: T.Int64
  for +valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for +populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for +included: {D.membership(K, V, c) == True{} : Bool}
  for found: {C.lookup(K, V, c, code) == Some{entry} : Maybe<&2, T.Entry<K, V>>}
  {D.membership(K, V, P.refresh_at(K, V, c, code, entry, lifetime, now)) == True{} : Bool}
def refresh_at(K, V, c, code, entry, lifetime, now, valid, populated, included, found):
  C.State{cap, +table, +order, life, counts, cb} = c
  T.Item{+key, +value, +old} = entry

  +present = Keys.leaf_member(T.Entry<K, V>, table, Nil{}, code, T.Item{key, value, old},
    E.enumerated_is_leaf(T.Entry<K, V>, table, code, T.Item{key, value, old},
      F.lookup_enumerated(K, V, cap, table, order, life, counts, cb, code, T.Item{key, value, old}, found)))
  +forward = R.and_left(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), included)
  +backward = R.and_right(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), included)
  And.conjunction(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}}))), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}})), order),
    into_updated(T.Entry<K, V>, order, table, code, T.Item{key, value, Time.deadline(now, lifetime)}, valid, populated, present, forward),
    from_updated(T.Entry<K, V>, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}})), table, code, T.Item{key, value, Time.deadline(now, lifetime)}, order, valid, populated, present, D.included_self(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, Time.deadline(now, lifetime)}}))), backward))
