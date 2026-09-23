import Base
import ./invariants.bend as Inv

law splice_nonempty:
  for -V: Data
  for value: V
  for rest: Map<&2, V>
  for position: Nat
  for route: String & Bool
  {Inv.nonempty(V, Map.ins.splice.bit(&2, V, value, rest, position, route)) == True{} : Bool}
def splice_nonempty(V, value, rest, position, route):
  match route:
    case Tuple{key, False{}}: {==}
    case Tuple{key, True{}}: {==}

law deep_nonempty:
  for -V: Data
  for value: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for discriminator: Nat
  for position: Nat
  for route: String & Bool
  {Inv.nonempty(V, Map.ins.deep(&2, V, value, lo, hi, discriminator, position, route)) == True{} : Bool}
def deep_nonempty(V, value, lo, hi, discriminator, position, route):
  match route:
    case Tuple{key, False{}}: {==}
    case Tuple{key, True{}}: {==}

law branch_nonempty:
  for -V: Data
  for +key: String
  for value: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for +position: Nat
  for +discriminator: Nat
  for descend: Bool
  {Inv.nonempty(V, Map.ins.if(&2, V, key, value, lo, hi, position, discriminator, descend)) == True{} : Bool}
def branch_nonempty(V, key, value, lo, hi, position, discriminator, descend):
  match descend:
    case False{}:
      splice_nonempty(V, value, MNode{position, lo, hi}, discriminator, Map.bit(key, discriminator))
    case True{}:
      deep_nonempty(V, value, lo, hi, discriminator, position, Map.bit(key, position))

# All native insertion results are nonempty; no input validity premise.
law insertion_nonempty:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for value: V
  for +discriminator: Nat
  {Inv.nonempty(V, Map.ins(&2, V, tree, key, value, discriminator)) == True{} : Bool}
def insertion_nonempty(V, tree, key, value, discriminator):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, old}:
      splice_nonempty(V, value, MLeaf{stored, old}, discriminator, Map.bit(key, discriminator))
    case MNode{+position, lo, hi}:
      branch_nonempty(V, key, value, lo, hi, position, discriminator, Nat.is_lt(position, discriminator))
