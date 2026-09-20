import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_key_lookup.bend as Keys
import ./map_populated.bend as Pop

law witnessed_route:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +position: Nat
  for +side: Bool
  for route: {Inv.routed(Maybe<&2, V>, tree, position, side) == True{} : Bool}
  for witness: Keys.witness(V, tree, key)
  {I.route_bit(Map.bit(key, position)) == side : Bool}
def witnessed_route(V, tree, key, position, side, route, witness):
  (+value, leaf) = witness
  Equal.cong(String & Bool, Bool, I.route_bit, Map.bit(key, position), (key, side),
    R.member_routed(V, tree, key, value, position, side, R.routed_certificate(Maybe<&2, V>, tree, position, side, route), leaf))

law member_route:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +position: Nat
  for +side: Bool
  for route: {Inv.routed(Maybe<&2, V>, tree, position, side) == True{} : Bool}
  for populated: {Pop.populated(V, tree) == True{} : Bool}
  for member: {Inv.member(Map.keys(&2, Maybe<&2, V>, tree), key) == True{} : Bool}
  {I.route_bit(Map.bit(key, position)) == side : Bool}
def member_route(V, tree, key, position, side, route, populated, member):
  witnessed_route(V, tree, key, position, side, route, Keys.key_has_leaf(V, tree, key, populated, member))

law opposite_case:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +key: String
  for +position: Nat
  for bit: Bool
  for decision: {Inv.member(Map.keys(&2, Maybe<&2, V>, hi), key) == bit : Bool}
  for left_route: {Inv.routed(Maybe<&2, V>, lo, position, False{}) == True{} : Bool}
  for right_route: {Inv.routed(Maybe<&2, V>, hi, position, True{}) == True{} : Bool}
  for left_populated: {Pop.populated(V, lo) == True{} : Bool}
  for right_populated: {Pop.populated(V, hi) == True{} : Bool}
  for left_member: {Inv.member(Map.keys(&2, Maybe<&2, V>, lo), key) == True{} : Bool}
  {bit == False{} : Bool}
def opposite_case(V, lo, hi, key, position, bit, decision, left_route, right_route, left_populated, right_populated, left_member):
  match bit:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, True{}, I.route_bit(Map.bit(key, position)), False{},
        Equal.sym(Bool, I.route_bit(Map.bit(key, position)), True{}, member_route(V, hi, key, position, True{}, right_route, right_populated, decision)),
        member_route(V, lo, key, position, False{}, left_route, left_populated, left_member))

# Native enumerations of oppositely routed populated trees share no key.
# This uses the actual Base bit and keys algorithms, not hash injectivity.
law opposite:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +key: String
  for +position: Nat
  for left_route: {Inv.routed(Maybe<&2, V>, lo, position, False{}) == True{} : Bool}
  for right_route: {Inv.routed(Maybe<&2, V>, hi, position, True{}) == True{} : Bool}
  for left_populated: {Pop.populated(V, lo) == True{} : Bool}
  for right_populated: {Pop.populated(V, hi) == True{} : Bool}
  for left_member: {Inv.member(Map.keys(&2, Maybe<&2, V>, lo), key) == True{} : Bool}
  {Inv.member(Map.keys(&2, Maybe<&2, V>, hi), key) == False{} : Bool}
def opposite(V, lo, hi, key, position, left_route, right_route, left_populated, right_populated, left_member):
  opposite_case(V, lo, hi, key, position, Inv.member(Map.keys(&2, Maybe<&2, V>, hi), key), {==}, left_route, right_route, left_populated, right_populated, left_member)
