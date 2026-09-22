import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_seek_routes.bend as Seek
import ./map_difference.bend as D
import ./map_string_prefix.bend as Prefix
import ./map_prefix_algebra.bend as A
import ./map_routing.bend as R

law branch:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for bit: Bool
  for route: {Map.bit(key, position) == (key, bit) : String & Bool}
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for left: {Inv.routed(V, lo, position, False{}) == True{} : Bool}
  for right: {Inv.routed(V, hi, position, True{}) == True{} : Bool}
  {Bool.not(Bool.xor(Inv.bit_value(Map.bit(stored, position)), bit)) == True{} : Bool}
def branch(V, lo, hi, position, key, stored, bit, route, found, left, right):
  match bit:
    case False{}:
      Seek.found_has_route(V, lo, key, position, False{}, stored, left, Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, position, key, route)), found))
    case True{}:
      Seek.found_has_route(V, hi, key, position, True{}, stored, right, Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, position, key, route)), found))

law not_xor_true:
  for b: Bool
  for yes: {b == True{} : Bool}
  for no: {Bool.not(b) == True{} : Bool}
  Empty
def not_xor_true(b, yes, no):
  match b:
    case False{}: R.false_true(yes)
    case True{}: R.false_true(no)

# The new discriminator cannot coincide with the root followed by seek: at
# that root the input key and selected key route to the same child.
law difference_not_root:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +position: Nat
  for +key: String
  for +stored: String
  for distinct: D.different(key, stored)
  for found: {I.seek_found(V, Map.seek(&2, V, MNode{position, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for left: {Inv.routed(V, lo, position, False{}) == True{} : Bool}
  for right: {Inv.routed(V, hi, position, True{}) == True{} : Bool}
  for equal: {Map.diff(key, stored) == position : Nat}
  Empty
def difference_not_root(V, lo, hi, position, key, stored, distinct, found, left, right, equal):
  agreement = branch(V, lo, hi, position, key, stored, I.route_bit(Map.bit(key, position)), I.route_shape(key, position), found, left, right)
  converted = Equal.trans(Bool, Bool.not(Bool.xor(I.route_bit(Map.bit(stored, position)), I.route_bit(Map.bit(key, position)))), Bool.not(Bool.xor(Inv.bit_value(Map.bit(stored, position)), I.route_bit(Map.bit(key, position)))), True{}, Equal.cong(Bool, Bool, b => Bool.not(Bool.xor(b, I.route_bit(Map.bit(key, position)))), I.route_bit(Map.bit(stored, position)), Inv.bit_value(Map.bit(stored, position)), Equal.sym(Bool, Inv.bit_value(Map.bit(stored, position)), I.route_bit(Map.bit(stored, position)), Prefix.invariant_bit(Map.bit(stored, position)))), agreement)
  symmetric = Equal.trans(Bool, Bool.not(Bool.xor(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(stored, position)))), Bool.not(Bool.xor(I.route_bit(Map.bit(stored, position)), I.route_bit(Map.bit(key, position)))), True{}, A.bit_symmetric(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(stored, position))), converted)
  differs = Equal.trans(Bool, Bool.xor(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(stored, position))), D.distinguishes(key, stored), True{}, Equal.cong(Nat, Bool, p => Bool.xor(I.route_bit(Map.bit(key, p)), I.route_bit(Map.bit(stored, p))), position, Map.diff(key, stored), Equal.sym(Nat, Map.diff(key, stored), position, equal)), D.native_difference(key, stored, distinct))
  not_xor_true(Bool.xor(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(stored, position))), differs, symmetric)
