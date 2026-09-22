import Base
import ../src/cache.bend as C
import ../types/model.bend as T
import ./invariants.bend as Inv
import ./map_key_membership.bend as Keys
import ./map_routing.bend as R
import ./map_delete_prefix.bend as And
import ./map_set_membership.bend as Set
import ./recency_update_membership.bend as Move
import ./map_populated.bend as Pop
import ./cache_delete_membership.bend as D
import ./cache_populated.bend as Packed
import ./refinement.bend as F

law equivalent_case:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +query: String
  for a: Bool
  for b: Bool
  for left: {Inv.member(xs, query) == a : Bool}
  for right: {Inv.member(ys, query) == b : Bool}
  for forward: {Inv.included(xs, ys) == True{} : Bool}
  for backward: {Inv.included(ys, xs) == True{} : Bool}
  {a == b : Bool}
def equivalent_case(xs, ys, query, a, b, left, right, forward, backward):
  match a:
    case False{}:
      match b:
        case False{}: {==}
        case True{}:
          Equal.trans(Bool, False{}, Inv.member(xs, query), True{}, Equal.sym(Bool, Inv.member(xs, query), False{}, left), Keys.included_member(ys, xs, query, backward, right))
    case True{}:
      Equal.trans(Bool, True{}, Inv.member(ys, query), b, Equal.sym(Bool, Inv.member(ys, query), True{}, Keys.included_member(xs, ys, query, forward, left)), right)

law equivalent:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +query: String
  for forward: {Inv.included(xs, ys) == True{} : Bool}
  for backward: {Inv.included(ys, xs) == True{} : Bool}
  {Inv.member(xs, query) == Inv.member(ys, query) : Bool}
def equivalent(xs, ys, query, forward, backward):
  equivalent_case(xs, ys, query, Inv.member(xs, query), Inv.member(ys, query), {==}, {==}, forward, backward)

law updated:
  for -V: Data
  for +table: Map<&2, Maybe<&2, V>>
  for +order: List<&2, String>
  for +code: String
  for +value: V
  for +query: String
  for valid: {Inv.critbit(Maybe<&2, V>, table) == True{} : Bool}
  for populated: {Pop.populated(V, table) == True{} : Bool}
  for forward: {Inv.included(order, Map.keys(&2, Maybe<&2, V>, table)) == True{} : Bool}
  for backward: {Inv.included(Map.keys(&2, Maybe<&2, V>, table), order) == True{} : Bool}
  {Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), query) == Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), query) : Bool}
def updated(V, table, order, code, value, query, valid, populated, forward, backward):
  Equal.trans(Bool, Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), query), String.eq(query, code) || Inv.member(order, query), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), query), Move.move(order, code, query),
    Equal.trans(Bool, String.eq(query, code) || Inv.member(order, query), String.eq(query, code) || Inv.member(Map.keys(&2, Maybe<&2, V>, table), query), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), query),
      Equal.cong(Bool, Bool, b => String.eq(query, code) || b, Inv.member(order, query), Inv.member(Map.keys(&2, Maybe<&2, V>, table), query), equivalent(order, Map.keys(&2, Maybe<&2, V>, table), query, forward, backward)),
      Equal.sym(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), query), String.eq(query, code) || Inv.member(Map.keys(&2, Maybe<&2, V>, table), query), Set.membership(V, table, code, value, query, valid, populated))))

law into_table:
  for -V: Data
  for xs: List<&2, String>
  for +table: Map<&2, Maybe<&2, V>>
  for +order: List<&2, String>
  for +code: String
  for +value: V
  for +valid: {Inv.critbit(Maybe<&2, V>, table) == True{} : Bool}
  for +populated: {Pop.populated(V, table) == True{} : Bool}
  for +forward: {Inv.included(order, Map.keys(&2, Maybe<&2, V>, table)) == True{} : Bool}
  for +backward: {Inv.included(Map.keys(&2, Maybe<&2, V>, table), order) == True{} : Bool}
  for +included: {Inv.included(xs, List.append(&2, String, C.without(order, code), Con{code, Nil{}})) == True{} : Bool}
  {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))) == True{} : Bool}
def into_table(V, xs, table, order, code, value, valid, populated, forward, backward, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))),
        Equal.trans(Bool, Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), True{}, Equal.sym(Bool, Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), updated(V, table, order, code, value, head, valid, populated, forward, backward)), R.and_left(Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), Inv.included(tail, List.append(&2, String, C.without(order, code), Con{code, Nil{}})), included)),
        into_table(V, tail, table, order, code, value, valid, populated, forward, backward, R.and_right(Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), Inv.included(tail, List.append(&2, String, C.without(order, code), Con{code, Nil{}})), included)))

law into_order:
  for -V: Data
  for xs: List<&2, String>
  for +table: Map<&2, Maybe<&2, V>>
  for +order: List<&2, String>
  for +code: String
  for +value: V
  for +valid: {Inv.critbit(Maybe<&2, V>, table) == True{} : Bool}
  for +populated: {Pop.populated(V, table) == True{} : Bool}
  for +forward: {Inv.included(order, Map.keys(&2, Maybe<&2, V>, table)) == True{} : Bool}
  for +backward: {Inv.included(Map.keys(&2, Maybe<&2, V>, table), order) == True{} : Bool}
  for +included: {Inv.included(xs, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))) == True{} : Bool}
  {Inv.included(xs, List.append(&2, String, C.without(order, code), Con{code, Nil{}})) == True{} : Bool}
def into_order(V, xs, table, order, code, value, valid, populated, forward, backward, included):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      And.conjunction(Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), Inv.included(tail, List.append(&2, String, C.without(order, code), Con{code, Nil{}})),
        Equal.trans(Bool, Inv.member(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), head), Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), True{}, updated(V, table, order, code, value, head, valid, populated, forward, backward), R.and_left(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))), included)),
        into_order(V, tail, table, order, code, value, valid, populated, forward, backward, R.and_right(Inv.member(Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value})), head), Inv.included(tail, Map.keys(&2, Maybe<&2, V>, Map.set(&2, Maybe<&2, V>, table, code, Some{value}))), included)))

# Joint bidirectional membership preservation for the actual cache store.
law store:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for +code: String
  for +key: K
  for +value: V
  for +deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.Event<K, V>>
  for +valid: {F.storage_critbit(K, V, c) == True{} : Bool}
  for +populated: {Packed.storage_populated(K, V, c) == True{} : Bool}
  for +included: {D.membership(K, V, c) == True{} : Bool}
  {D.membership(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))) == True{} : Bool}
def store(K, V, c, code, key, value, deadline, flag, events, valid, populated, included):
  C.State{cap, +table, +order, life, counts, cb} = c
  T.Counts{i, e, r, h, misses} = counts
  +forward = R.and_left(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), included)
  +backward = R.and_right(Inv.included(order, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table)), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, table), order), included)
  And.conjunction(Inv.included(List.append(&2, String, C.without(order, code), Con{code, Nil{}}), Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}}))), Inv.included(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}})), List.append(&2, String, C.without(order, code), Con{code, Nil{}})),
    into_table(T.Entry<K, V>, List.append(&2, String, C.without(order, code), Con{code, Nil{}}), table, order, code, T.Item{key, value, deadline}, valid, populated, forward, backward, D.included_self(List.append(&2, String, C.without(order, code), Con{code, Nil{}}))),
    into_order(T.Entry<K, V>, Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}})), table, order, code, T.Item{key, value, deadline}, valid, populated, forward, backward, D.included_self(Map.keys(&2, Maybe<&2, T.Entry<K, V>>, Map.set(&2, Maybe<&2, T.Entry<K, V>>, table, code, Some{T.Item{key, value, deadline}})))))
