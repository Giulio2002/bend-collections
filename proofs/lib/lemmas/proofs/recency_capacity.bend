import Base
import ./recency_bounds.bend as B
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ../src/cache.bend as C
import ../types/model.bend as T

law append_one_length:
  for xs: List<&2, String>
  for +key: String
  {List.length(&2, String, List.append(&2, String, xs, Con{key, Nil{}})) == 1n+List.length(&2, String, xs) : Nat}
def append_one_length(xs, key):
  match xs:
    case Nil{}: {==}
    case Con{head, +tail}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, List.append(&2, String, tail, Con{key, Nil{}})), 1n+List.length(&2, String, tail), append_one_length(tail, key))

law present_branch:
  for +head: String
  for +tail: List<&2, String>
  for +key: String
  for equal: Bool
  for present: {equal || Inv.member(tail, key) == True{} : Bool}
  for smaller: {Inv.member(tail, key) == True{} : Bool} -> {Nat.is_le(1n+List.length(&2, String, C.without(tail, key)), List.length(&2, String, tail)) == True{} : Bool}
  {Nat.is_le(1n+List.length(&2, String, C.without_keep(head, C.without(tail, key), equal)), 1n+List.length(&2, String, tail)) == True{} : Bool}
def present_branch(head, tail, key, equal, present, smaller):
  match equal:
    case True{}: B.without_bound(tail, key)
    case False{}: smaller(present)

# Removing a present code frees at least one recency slot, even if the input
# order is malformed and contains duplicates. No assumed output bound is used.
law present_frees_slot:
  for xs: List<&2, String>
  for +key: String
  for present: {Inv.member(xs, key) == True{} : Bool}
  {Nat.is_le(1n+List.length(&2, String, C.without(xs, key)), List.length(&2, String, xs)) == True{} : Bool}
def present_frees_slot(xs, key, present):
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, R.false_true(present))
    case Con{+head, +tail}:
      present_branch(head, tail, key, String.eq(head, key), present, p => present_frees_slot(tail, key, p))

law move_does_not_grow:
  for +xs: List<&2, String>
  for +key: String
  for present: {Inv.member(xs, key) == True{} : Bool}
  {Nat.is_le(List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), List.length(&2, String, xs)) == True{} : Bool}
def move_does_not_grow(xs, key, present):
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), 1n+List.length(&2, String, C.without(xs, key)), append_one_length(C.without(xs, key), key)) : {Nat.is_le(_, List.length(&2, String, xs)) == True{} : Bool}
  present_frees_slot(xs, key, present)

law move_with_room:
  for +xs: List<&2, String>
  for +key: String
  for +cap: Nat
  for room: {Nat.is_le(1n+List.length(&2, String, xs), cap) == True{} : Bool}
  {Nat.is_le(List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), cap) == True{} : Bool}
def move_with_room(xs, key, cap, room):
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), 1n+List.length(&2, String, C.without(xs, key)), append_one_length(C.without(xs, key), key)) : {Nat.is_le(_, cap) == True{} : Bool}
  B.le_transitive(1n+List.length(&2, String, C.without(xs, key)), 1n+List.length(&2, String, xs), cap, B.without_bound(xs, key), room)

def room_or_present(-K: Data, -V: Data, c: C.Cache<K, V>, code: String) -> Type:
  C.State{cap, table, order, life, counts, cb} = c
  Either<&1, &1, {Nat.is_le(1n+List.length(&2, String, order), cap) == True{} : Bool}, {Inv.member(order, code) == True{} : Bool}>

law move_bounded:
  for +xs: List<&2, String>
  for +key: String
  for +cap: Nat
  for bound: {Nat.is_le(List.length(&2, String, xs), cap) == True{} : Bool}
  for ready: Either<&1, &1, {Nat.is_le(1n+List.length(&2, String, xs), cap) == True{} : Bool}, {Inv.member(xs, key) == True{} : Bool}>
  {Nat.is_le(List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), cap) == True{} : Bool}
def move_bounded(xs, key, cap, bound, ready):
  match ready:
    case Inl{room}: move_with_room(xs, key, cap, room)
    case Inr{present}:
      B.le_transitive(List.length(&2, String, List.append(&2, String, C.without(xs, key), Con{key, Nil{}})), List.length(&2, String, xs), cap, move_does_not_grow(xs, key, present), bound)

# Actual store: the room/presence premise is explicit and still needs to be
# supplied by the public add preparation and map/order correspondence proofs.
law store_preserves_bound:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for key: K
  for value: V
  for deadline: T.Int64
  for flag: Bool
  for events: List<&2, T.Event<K, V>>
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  for ready: room_or_present(K, V, c, code)
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.store(K, V, c, code, key, value, deadline, flag, events))), C.capacity(K, V, c)) == True{} : Bool}
def store_preserves_bound(K, V, c, code, key, value, deadline, flag, events, bound, ready):
  C.State{cap, table, order, life, counts, cb} = c
  T.Counts{i, e, r, h, misses} = counts
  move_bounded(order, code, cap, bound, ready)

law le_reflexive:
  for n: Nat
  {Nat.is_le(n, n) == True{} : Bool}
def le_reflexive(n):
  match n:
    case 0n: {==}
    case 1n+p: le_reflexive(p)

law touch_does_not_grow:
  for +xs: List<&2, String>
  for +key: String
  for touch: Bool
  for present: {Inv.member(xs, key) == True{} : Bool}
  {Nat.is_le(List.length(&2, String, C.touch_order(xs, key, touch)), List.length(&2, String, xs)) == True{} : Bool}
def touch_does_not_grow(xs, key, touch, present):
  match touch:
    case False{}: le_reflexive(List.length(&2, String, xs))
    case True{}: move_does_not_grow(xs, key, present)
