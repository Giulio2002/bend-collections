import Base
import ./invariants.bend as Inv

law splice_bit:
  for -V: Data
  for value: V
  for rest: Map<&2, V>
  for +discriminator: Nat
  for route: String & Bool
  for +parent: Nat
  for ordered: {Nat.is_lt(parent, discriminator) == True{} : Bool}
  {Inv.below(V, Map.ins.splice.bit(&2, V, value, rest, discriminator, route), parent) == True{} : Bool}
def splice_bit(V, value, rest, discriminator, route, parent, ordered):
  match route:
    case Tuple{key, False{}}: ordered
    case Tuple{key, True{}}: ordered

law deep_bit:
  for -V: Data
  for value: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for discriminator: Nat
  for +position: Nat
  for route: String & Bool
  for +parent: Nat
  for ordered: {Nat.is_lt(parent, position) == True{} : Bool}
  {Inv.below(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, route), parent) == True{} : Bool}
def deep_bit(V, value, lo, hi, discriminator, position, route, parent, ordered):
  match route:
    case Tuple{key, False{}}: ordered
    case Tuple{key, True{}}: ordered

law branch:
  for -V: Data
  for +key: String
  for value: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for descend: Bool
  for +parent: Nat
  for fresh: {Nat.is_lt(parent, discriminator) == True{} : Bool}
  for existing: {Nat.is_lt(parent, position) == True{} : Bool}
  {Inv.below(V, Map.ins.if(&2, V, key, value, lo, hi, position, discriminator, descend), parent) == True{} : Bool}
def branch(V, key, value, lo, hi, position, discriminator, descend, parent, fresh, existing):
  match descend:
    case False{}:
      splice_bit(V, value, MNode{position, lo, hi}, discriminator, Map.bit(key, discriminator), parent, fresh)
    case True{}:
      deep_bit(V, value, lo, hi, discriminator, position, Map.bit(key, position), parent, existing)

# Insertion may retain the old root or introduce the new discriminator. Both
# bounds are input facts; no bound on an output tree is assumed.
law preserves_below:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for value: V
  for +discriminator: Nat
  for +parent: Nat
  for fresh: {Nat.is_lt(parent, discriminator) == True{} : Bool}
  for existing: {Inv.below(V, tree, parent) == True{} : Bool}
  {Inv.below(V, Map.ins(&2, V, tree, key, value, discriminator), parent) == True{} : Bool}
def preserves_below(V, tree, key, value, discriminator, parent, fresh, existing):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, old}:
      splice_bit(V, value, MLeaf{stored, old}, discriminator, Map.bit(key, discriminator), parent, fresh)
    case MNode{+position, lo, hi}:
      branch(V, key, value, lo, hi, position, discriminator, Nat.is_lt(position, discriminator), parent, fresh, existing)
