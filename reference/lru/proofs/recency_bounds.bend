import Base
import ../src/cache.bend as C
import ../types/model.bend as T
import ./map_routing.bend as Logic

law le_weaken:
  for a: Nat
  for b: Nat
  for e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}
def le_weaken(a, b, e):
  match a b:
    case 0n q: {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, Logic.false_true(e))
    case 1n+p 1n+q:
      le_weaken(p, q, e)

law le_transitive:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}
def le_transitive(a, b, c, ab, bc):
  match a b c:
    case 0n q 0n: {==}
    case 0n q 1n+r: {==}
    case 1n+p 0n r:
      Empty.absurd({Nat.is_le(1n+p, r) == True{} : Bool}, Logic.false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, Logic.false_true(bc))
    case 1n+p 1n+q 1n+r:
      le_transitive(p, q, r, ab, bc)

law keep_bound:
  for head: String
  for +tail: List<&2, String>
  for size: Nat
  for eq: Bool
  for bound: {Nat.is_le(List.length(&2, String, tail), size) == True{} : Bool}
  {Nat.is_le(List.length(&2, String, C.without_keep(head, tail, eq)), 1n+size) == True{} : Bool}
def keep_bound(head, tail, size, eq, bound):
  match eq:
    case False{}:
      bound
    case True{}:
      le_weaken(List.length(&2, String, tail), size, bound)

law without_bound:
  for xs: List<&2, String>
  for +key: String
  {Nat.is_le(List.length(&2, String, C.without(xs, key)), List.length(&2, String, xs)) == True{} : Bool}
def without_bound(xs, key):
  match xs:
    case Nil{}: {==}
    case Con{+head, +tail}:
      keep_bound(head, C.without(tail, key), List.length(&2, String, tail), String.eq(head, key), without_bound(tail, key))

# Actual removal never grows recency metadata, even for malformed input states.
law removal_does_not_grow:
  for -K: Data
  for -V: Data
  for c: C.Cache<K, V>
  for code: String
  for evict: Bool
  for entry: T.Entry<K, V>
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))), C.len(K, V, c)) == True{} : Bool}
def removal_does_not_grow(K, V, c, code, evict, entry):
  C.State{cap, table, order, life, counts, cb} = c
  without_bound(order, code)

law removal_preserves_capacity_bound:
  for -K: Data
  for -V: Data
  for +c: C.Cache<K, V>
  for +code: String
  for +evict: Bool
  for +entry: T.Entry<K, V>
  for bound: {Nat.is_le(C.len(K, V, c), C.capacity(K, V, c)) == True{} : Bool}
  {Nat.is_le(C.len(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry))), C.capacity(K, V, C.step_cache(K, V, C.remove_present(K, V, c, code, evict, entry)))) == True{} : Bool}
def removal_preserves_capacity_bound(K, V, c, code, evict, entry, bound):
  C.State{+cap, table, +order, life, counts, cb} = c
  le_transitive(List.length(&2, String, C.without(order, code)), List.length(&2, String, order), cap, without_bound(order, code), bound)
