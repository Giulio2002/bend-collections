import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_routes.bend as D
import ./map_delete_prefix.bend as P
import ./map_string_prefix.bend as Prefix

law leaf_boolean:
  for +key: String
  for +position: Nat
  for +side: Bool
  for route: {Map.bit(key, position) == (key, side) : String & Bool}
  {Bool.not(Bool.xor(Inv.bit_value(Map.bit(key, position)), side)) == True{} : Bool}
def leaf_boolean(key, position, side, route):
  %Equal.sym(String & Bool, Map.bit(key, position), (key, side), route) : {Bool.not(Bool.xor(Inv.bit_value(_), side)) == True{} : Bool}
  Equal.cong(Bool, Bool, Bool.not, Bool.xor(side, side), False{}, Prefix.xor_self(side))

law routed_boolean:
  for -V: Data
  for tree: Map<&2, V>
  for +position: Nat
  for +side: Bool
  for route: R.routed(V, tree, position, side)
  {Inv.routed(V, tree, position, side) == True{} : Bool}
def routed_boolean(V, tree, position, side, route):
  match tree:
    case MTip{}: {==}
    case MLeaf{key, value}: leaf_boolean(key, position, side, route)
    case MNode{p, +lo, +hi}:
      (left, right) = route
      P.conjunction(Inv.routed(V, lo, position, side), Inv.routed(V, hi, position, side), routed_boolean(V, lo, position, side, left), routed_boolean(V, hi, position, side, right))

law deletion_preserves:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +position: Nat
  for +side: Bool
  for route: {Inv.routed(V, tree, position, side) == True{} : Bool}
  {Inv.routed(V, Map.del(&2, V, tree, key), position, side) == True{} : Bool}
def deletion_preserves(V, tree, key, position, side, route):
  routed_boolean(V, Map.del(&2, V, tree, key), position, side, D.preserves_routing(V, tree, key, position, side, R.routed_certificate(V, tree, position, side, route)))
