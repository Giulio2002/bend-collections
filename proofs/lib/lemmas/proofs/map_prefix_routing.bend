import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P
import ./map_prefix_algebra.bend as A
import ./map_prefix_bounds.bend as B
import ./map_difference_order.bend as O

law bit_at:
  for +a: String
  for +b: String
  for +limit: Nat
  for +position: Nat
  for earlier: {Nat.is_lt(position, limit) == True{} : Bool}
  for prefix: {Inv.same_prefix(a, b, limit) == True{} : Bool}
  {Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, position)), Inv.bit_value(Map.bit(b, position)))) == True{} : Bool}
def bit_at(a, b, limit, position, earlier, prefix):
  R.and_left(Bool.not(Bool.xor(Inv.bit_value(Map.bit(a, position)), Inv.bit_value(Map.bit(b, position)))), Inv.same_prefix(a, b, position), B.weaken(a, b, limit, 1n+position, O.strict_successor(position, limit, earlier), prefix))

# Agreement on the prefix fixes every leaf's routing bit at an earlier position.
law prefix_routing:
  for -V: Data
  for tree: Map<&2, V>
  for +query: String
  for +limit: Nat
  for +position: Nat
  for +side: Bool
  for +earlier: {Nat.is_lt(position, limit) == True{} : Bool}
  for +prefix: {Inv.prefix_against(V, query, tree, limit) == True{} : Bool}
  for +route: {Bool.not(Bool.xor(Inv.bit_value(Map.bit(query, position)), side)) == True{} : Bool}
  {Inv.routed(V, tree, position, side) == True{} : Bool}
def prefix_routing(V, tree, query, limit, position, side, earlier, prefix, route):
  match tree:
    case MTip{}: {==}
    case MLeaf{+stored, value}:
      A.bit_transitive(Inv.bit_value(Map.bit(stored, position)), Inv.bit_value(Map.bit(query, position)), side, bit_at(stored, query, limit, position, earlier, A.symmetric(query, stored, limit, prefix)), route)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.routed(V, lo, position, side), Inv.routed(V, hi, position, side), prefix_routing(V, lo, query, limit, position, side, earlier, R.and_left(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), prefix), route), prefix_routing(V, hi, query, limit, position, side, earlier, R.and_right(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), prefix), route))
