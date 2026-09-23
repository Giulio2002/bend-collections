import Base
import ./map_insert_prefix.bend as Prefix
import ./map_prefix_algebra.bend as Algebra
import ./invariants.bend as Inv
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

def rows(-V: Data, tree: Map<&2, V>, limit: Nat, whole: Map<&2, V>) -> Bool:
  Inv.common_prefix(V, tree, whole, limit)

law splice_bit:
  for -V: Data
  for +key: String
  for value: V
  for +rest: Map<&2, V>
  for discriminator: Nat
  for bit: Bool
  for +position: Nat
  for +side: Map<&2, V>
  for fresh: {rows(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for existing: {rows(V, rest, position, side) == True{} : Bool}
  {rows(V, Map.ins.splice.bit(&2, V, value, rest, discriminator, (key, bit)), position, side) == True{} : Bool}
def splice_bit(V, key, value, rest, discriminator, bit, position, side, fresh, existing):
  match bit:
    case False{}:
      P.conjunction(rows(V, MLeaf{key, value}, position, side), rows(V, rest, position, side), fresh, existing)
    case True{}:
      P.conjunction(rows(V, rest, position, side), rows(V, MLeaf{key, value}, position, side), existing, fresh)

law splice:
  for -V: Data
  for +key: String
  for +value: V
  for +rest: Map<&2, V>
  for +discriminator: Nat
  for +position: Nat
  for +side: Map<&2, V>
  for fresh: {rows(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for existing: {rows(V, rest, position, side) == True{} : Bool}
  {rows(V, Map.ins.splice(&2, V, discriminator, key, value, rest), position, side) == True{} : Bool}
def splice(V, key, value, rest, discriminator, position, side, fresh, existing):
  %Equal.sym(String & Bool, Map.bit(key, discriminator), (key, I.route_bit(Map.bit(key, discriminator))), I.route_shape(key, discriminator)) : {rows(V, Map.ins.splice.bit(&2, V, value, rest, discriminator, _), position, side) == True{} : Bool}
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
  for +side: Map<&2, V>
  for left: {rows(V, lo, position, side) == True{} : Bool}
  for right: {rows(V, hi, position, side) == True{} : Bool}
  for changed_left: {rows(V, Map.ins(&2, V, lo, key, value, discriminator), position, side) == True{} : Bool}
  for changed_right: {rows(V, Map.ins(&2, V, hi, key, value, discriminator), position, side) == True{} : Bool}
  {rows(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, parent, (key, bit)), position, side) == True{} : Bool}
def deep_bit(V, key, value, lo, hi, discriminator, parent, bit, position, side, left, right, changed_left, changed_right):
  match bit:
    case False{}:
      P.conjunction(rows(V, Map.ins(&2, V, lo, key, value, discriminator), position, side), rows(V, hi, position, side), changed_left, right)
    case True{}:
      P.conjunction(rows(V, lo, position, side), rows(V, Map.ins(&2, V, hi, key, value, discriminator), position, side), left, changed_right)

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
  for +side: Map<&2, V>
  for fresh: {rows(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for left: {rows(V, lo, position, side) == True{} : Bool}
  for right: {rows(V, hi, position, side) == True{} : Bool}
  for changed_left: {rows(V, Map.ins(&2, V, lo, key, value, discriminator), position, side) == True{} : Bool}
  for changed_right: {rows(V, Map.ins(&2, V, hi, key, value, discriminator), position, side) == True{} : Bool}
  {rows(V, Map.ins.if(&2, V, key, value, lo, hi, parent, discriminator, descend), position, side) == True{} : Bool}
def branch(V, key, value, lo, hi, discriminator, parent, descend, position, side, fresh, left, right, changed_left, changed_right):
  match descend:
    case False{}:
      splice(V, key, value, MNode{parent, lo, hi}, discriminator, position, side, fresh, P.conjunction(rows(V, lo, position, side), rows(V, hi, position, side), left, right))
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, parent), (key, I.route_bit(Map.bit(key, parent))), I.route_shape(key, parent)) : {rows(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, parent, _), position, side) == True{} : Bool}
      deep_bit(V, key, value, lo, hi, discriminator, parent, I.route_bit(Map.bit(key, parent)), position, side, left, right, changed_left, changed_right)

# Insertion preserves all existing rows and adds the new key row when that
# key agrees with every leaf in the other domain. No input validity assumed.
law preserves_rows:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +value: V
  for +discriminator: Nat
  for +position: Nat
  for +side: Map<&2, V>
  for +fresh: {rows(V, MLeaf{key, value}, position, side) == True{} : Bool}
  for +existing: {rows(V, tree, position, side) == True{} : Bool}
  {rows(V, Map.ins(&2, V, tree, key, value, discriminator), position, side) == True{} : Bool}
def preserves_rows(V, tree, key, value, discriminator, position, side, fresh, existing):
  match tree:
    case MTip{}: fresh
    case MLeaf{stored, old}:
      splice(V, key, value, MLeaf{stored, old}, discriminator, position, side, fresh, existing)
    case MNode{+parent, +lo, +hi}:
      +left = R.and_left(rows(V, lo, position, side), rows(V, hi, position, side), existing)
      +right = R.and_right(rows(V, lo, position, side), rows(V, hi, position, side), existing)
      branch(V, key, value, lo, hi, discriminator, parent, Nat.is_lt(parent, discriminator), position, side, fresh, left, right,
        preserves_rows(V, lo, key, value, discriminator, position, side, fresh, left),
        preserves_rows(V, hi, key, value, discriminator, position, side, fresh, right))

law preserves_columns:
  for -V: Data
  for tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +key: String
  for +value: V
  for +discriminator: Nat
  for +limit: Nat
  for +fresh: {Inv.prefix_against(V, key, tree, limit) == True{} : Bool}
  for +existing: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, tree, Map.ins(&2, V, whole, key, value, discriminator), limit) == True{} : Bool}
def preserves_columns(V, tree, whole, key, value, discriminator, limit, fresh, existing):
  match tree:
    case MTip{}: {==}
    case MLeaf{+stored, old}:
      Prefix.preserves_prefix(V, whole, key, value, discriminator, limit, stored, Algebra.symmetric(key, stored, limit, fresh), existing)
    case MNode{p, +lo, +hi}:
      P.conjunction(Inv.common_prefix(V, lo, Map.ins(&2, V, whole, key, value, discriminator), limit), Inv.common_prefix(V, hi, Map.ins(&2, V, whole, key, value, discriminator), limit),
        preserves_columns(V, lo, whole, key, value, discriminator, limit, R.and_left(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), fresh), R.and_left(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), existing)),
        preserves_columns(V, hi, whole, key, value, discriminator, limit, R.and_right(Inv.prefix_against(V, key, lo, limit), Inv.prefix_against(V, key, hi, limit), fresh), R.and_right(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), existing)))

# Both domains include the new key, so self-agreement and reversed old/new
# pairs are derived, not assumed as an output invariant.
law preserves_common_prefix:
  for -V: Data
  for +tree: Map<&2, V>
  for +key: String
  for +value: V
  for +discriminator: Nat
  for +limit: Nat
  for +fresh: {Inv.prefix_against(V, key, tree, limit) == True{} : Bool}
  for existing: {Inv.common_prefix(V, tree, tree, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.ins(&2, V, tree, key, value, discriminator), Map.ins(&2, V, tree, key, value, discriminator), limit) == True{} : Bool}
def preserves_common_prefix(V, tree, key, value, discriminator, limit, fresh, existing):
  preserves_rows(V, tree, key, value, discriminator, limit, Map.ins(&2, V, tree, key, value, discriminator),
    Prefix.preserves_prefix(V, tree, key, value, discriminator, limit, key, Algebra.reflexive(key, limit), fresh),
    preserves_columns(V, tree, tree, key, value, discriminator, limit, fresh, existing))
