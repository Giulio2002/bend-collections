import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_routing.bend as R

def selected_route(position: Nat, side: Bool, found: Maybe<&2, String>) -> Bool:
  match found:
    case None{}: True{}
    case Some{stored}: Bool.not(Bool.xor(Inv.bit_value(Map.bit(stored, position)), side))

law branch:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for route: {Map.bit(key, p) == (key, bit) : String & Bool}
  for +position: Nat
  for +side: Bool
  for left: {selected_route(position, side, I.seek_found(V, Map.seek(&2, V, lo, key))) == True{} : Bool}
  for right: {selected_route(position, side, I.seek_found(V, Map.seek(&2, V, hi, key))) == True{} : Bool}
  {selected_route(position, side, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key))) == True{} : Bool}
def branch(V, lo, hi, p, key, bit, route, position, side, left, right):
  match bit:
    case False{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, p, key, route)) : {selected_route(position, side, _) == True{} : Bool}
      left
    case True{}:
      %Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, p, key, route)) : {selected_route(position, side, _) == True{} : Bool}
      right

# Actual seek inherits every routing constraint imposed on all leaves.
law selected_has_route:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +position: Nat
  for +side: Bool
  for +prefix: {Inv.routed(V, tree, position, side) == True{} : Bool}
  {selected_route(position, side, I.seek_found(V, Map.seek(&2, V, tree, key))) == True{} : Bool}
def selected_has_route(V, tree, key, position, side, prefix):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: prefix
    case MNode{+p, +lo, +hi}:
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), position, side,
        selected_has_route(V, lo, key, position, side, R.and_left(Inv.routed(V, lo, position, side), Inv.routed(V, hi, position, side), prefix)),
        selected_has_route(V, hi, key, position, side, R.and_right(Inv.routed(V, lo, position, side), Inv.routed(V, hi, position, side), prefix)))

law found_has_route:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +position: Nat
  for +side: Bool
  for +stored: String
  for prefix: {Inv.routed(V, tree, position, side) == True{} : Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  {Bool.not(Bool.xor(Inv.bit_value(Map.bit(stored, position)), side)) == True{} : Bool}
def found_has_route(V, tree, key, position, side, stored, prefix, found):
  %found : {selected_route(position, side, _) == True{} : Bool}
  selected_has_route(V, tree, key, position, side, prefix)
