import Base
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

# A fixed query prefix predicate over actual native leaves.
def prefix(-V: Data, tree: Map<&2, V>, limit: Nat, query: String) -> Bool:
  Inv.prefix_against(V, query, tree, limit)

law splice_bit:
  for -V: Data
  for +key: String
  for value: V
  for +rest: Map<&2, V>
  for discriminator: Nat
  for bit: Bool
  for +position: Nat
  for +side: String
  for fresh: {prefix(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for existing: {prefix(V, rest, position, side) == True{} : Bool}
  {prefix(V, Map.ins.splice.bit(&2, V, value, rest, discriminator, (key, bit)), position, side) == True{} : Bool}
def splice_bit(V, key, value, rest, discriminator, bit, position, side, fresh, existing):
  match bit:
    case False{}:
      P.conjunction(prefix(V, MLeaf{key, value}, position, side), prefix(V, rest, position, side), fresh, existing)
    case True{}:
      P.conjunction(prefix(V, rest, position, side), prefix(V, MLeaf{key, value}, position, side), existing, fresh)

law splice:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +discriminator: Nat
  for +position: Nat
  for +side: String
  for fresh: {prefix(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for existing: {prefix(V, rest, position, side) == True{} : Bool}
  {prefix(V, Map.ins.splice(&2, V, discriminator, key, value, rest), position, side) == True{} : Bool}
def splice(V, key, value, rest, discriminator, position, side, fresh, existing):
  %Equal.sym(String & Bool, Map.bit(key, discriminator), (key, I.route_bit(Map.bit(key, discriminator))), I.route_shape(key, discriminator)) : {prefix(V, Map.ins.splice.bit(&2, V, value, rest, discriminator, _), position, side) == True{} : Bool}
  splice_bit(V, key, value, rest, discriminator, I.route_bit(Map.bit(key, discriminator)), position, side, fresh, existing)

law deep_bit:
  for -V: Data
  for +key: String
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +discriminator: Nat
  for parent: Nat
  for bit: Bool
  for +position: Nat
  for +side: String
  for left: {prefix(V, lo, position, side) == True{} : Bool}
  for right: {prefix(V, hi, position, side) == True{} : Bool}
  for changed_left: {prefix(V, Map.ins(&2, V, lo, key, value, discriminator), position, side) == True{} : Bool}
  for changed_right: {prefix(V, Map.ins(&2, V, hi, key, value, discriminator), position, side) == True{} : Bool}
  {prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, parent, (key, bit)), position, side) == True{} : Bool}
def deep_bit(V, key, value, lo, hi, discriminator, parent, bit, position, side, left, right, changed_left, changed_right):
  match bit:
    case False{}:
      P.conjunction(prefix(V, Map.ins(&2, V, lo, key, value, discriminator), position, side), prefix(V, hi, position, side), changed_left, right)
    case True{}:
      P.conjunction(prefix(V, lo, position, side), prefix(V, Map.ins(&2, V, hi, key, value, discriminator), position, side), left, changed_right)

law branch:
  for -V: Data
  for +key: String
  for +value: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +discriminator: Nat
  for +parent: Nat
  for descend: Bool
  for +position: Nat
  for +side: String
  for fresh: {prefix(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for left: {prefix(V, lo, position, side) == True{} : Bool}
  for right: {prefix(V, hi, position, side) == True{} : Bool}
  for changed_left: {prefix(V, Map.ins(&2, V, lo, key, value, discriminator), position, side) == True{} : Bool}
  for changed_right: {prefix(V, Map.ins(&2, V, hi, key, value, discriminator), position, side) == True{} : Bool}
  {prefix(V, Map.ins.if(&2, V, key, value, lo, hi, parent, discriminator, descend), position, side) == True{} : Bool}
def branch(V, key, value, lo, hi, discriminator, parent, descend, position, side, fresh, left, right, changed_left, changed_right):
  match descend:
    case False{}:
      splice(V, key, value, MNode{parent, lo, hi}, discriminator, position, side, fresh, P.conjunction(prefix(V, lo, position, side), prefix(V, hi, position, side), left, right))
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, parent), (key, I.route_bit(Map.bit(key, parent))), I.route_shape(key, parent)) : {prefix(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, parent, _), position, side) == True{} : Bool}
      deep_bit(V, key, value, lo, hi, discriminator, parent, I.route_bit(Map.bit(key, parent)), position, side, left, right, changed_left, changed_right)

# Insertion preserves a prefix constraint when the new key satisfies it.
# This covers actual native splice and descent, without tree-validity premises.
law preserves_prefix:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +value: V
  for +discriminator: Nat
  for +position: Nat
  for +side: String
  for +fresh: {prefix(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for +existing: {prefix(V, tree, position, side) == True{} : Bool}
  {prefix(V, Map.ins(&2, V, tree, key, value, discriminator), position, side) == True{} : Bool}
def preserves_prefix(V, tree, key, value, discriminator, position, side, fresh, existing):
  match tree:
    case MTip{}: fresh
    case MLeaf{stored, old}:
      splice(V, key, value, MLeaf{stored, old}, discriminator, position, side, fresh, existing)
    case MNode{+parent, +lo, +hi}:
      +left = R.and_left(prefix(V, lo, position, side), prefix(V, hi, position, side), existing)
      +right = R.and_right(prefix(V, lo, position, side), prefix(V, hi, position, side), existing)
      branch(V, key, value, lo, hi, discriminator, parent, Nat.is_lt(parent, discriminator), position, side, fresh, left, right,
        preserves_prefix(V, lo, key, value, discriminator, position, side, fresh, left),
        preserves_prefix(V, hi, key, value, discriminator, position, side, fresh, right))
