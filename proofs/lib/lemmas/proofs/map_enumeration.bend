import Base
import ./map_lookup.bend as L
import ./map_routing.bend as Routing
import ./map_insert.bend as I
import ./invariants.bend as R

# Native accumulator enumeration can return only a real tree binding or a
# binding already present in its explicit accumulator.
def partition(-V: Data, tree: Map<&2, Maybe<&2, V>>, acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>, key: String, value: V) -> Type:
  Either<&1, &1, L.leaf(V, tree, key, value), L.listed(V, acc, key, value)>

law lift_high:
  for -V: Data
  for lo: Map<&2, Maybe<&2, V>>
  for hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for key: String
  for value: V
  for proof: partition(V, hi, acc, key, value)
  partition(V, MNode{p, lo, hi}, acc, key, value)
def lift_high(V, lo, hi, p, acc, key, value, proof):
  match proof:
    case Inl{member}:
      Inl{Inr{member}}
    case Inr{member}:
      Inr{member}

law lift_node:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for p: Nat
  for acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for key: String
  for value: V
  for high: @member: L.listed(V, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value) -> partition(V, hi, acc, key, value)
  for proof: partition(V, lo, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value)
  partition(V, MNode{p, lo, hi}, acc, key, value)
def lift_node(V, lo, hi, p, acc, key, value, high, proof):
  match proof:
    case Inl{member}:
      Inl{Inl{member}}
    case Inr{member}:
      lift_high(V, lo, hi, p, acc, key, value, high(member))

law enumeration_partition:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +acc: List<&2, Sigma<&2, &2, String, _ => Maybe<&2, V>>>
  for +key: String
  for +value: V
  for member: L.listed(V, Map.to_list.go(&2, Maybe<&2, V>, tree, acc), key, value)
  partition(V, tree, acc, key, value)
def enumeration_partition(V, tree, acc, key, value, member):
  match tree:
    case MTip{}:
      Inr{member}
    case MLeaf{stored, item}:
      match member:
        case Inl{at_head}:
          Inl{at_head}
        case Inr{in_acc}:
          Inr{in_acc}
    case MNode{p, +lo, +hi}:
      lift_node(V, lo, hi, p, acc, key, value, in_high => enumeration_partition(V, hi, acc, key, value, in_high), enumeration_partition(V, lo, Map.to_list.go(&2, Maybe<&2, V>, hi, acc), key, value, member))

law empty_accumulator:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for key: String
  for value: V
  for proof: partition(V, tree, Nil{}, key, value)
  L.leaf(V, tree, key, value)
def empty_accumulator(V, tree, key, value, proof):
  match proof:
    case Inl{member}:
      member
    case Inr{impossible}:
      Empty.absurd(L.leaf(V, tree, key, value), impossible)

law enumerated_is_leaf:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for member: L.listed(V, Map.to_list(&2, Maybe<&2, V>, tree), key, value)
  L.leaf(V, tree, key, value)
def enumerated_is_leaf(V, tree, key, value, member):
  empty_accumulator(V, tree, key, value, enumeration_partition(V, tree, Nil{}, key, value, member))

# Together with returned_value_enumerated this gives both directions against
# actual native enumeration on trees satisfying the existing critbit predicate.
law enumerated_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +value: V
  for invariant: {R.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for member: L.listed(V, Map.to_list(&2, Maybe<&2, V>, tree), key, value)
  {I.lookup(Maybe<&2, V>, None{}, tree, key) == Some{value} : Maybe<&2, V>}
def enumerated_lookup(V, tree, key, value, invariant, member):
  Routing.critbit_member_lookup(V, tree, key, value, invariant, enumerated_is_leaf(V, tree, key, value, member))
