import Base
import ./map_lookup.bend as L
import ./map_insert.bend as I
import ./map_insert_critbit.bend as Valid

# Structural inverse membership: insertion introduces no binding at other keys.
law fresh_impossible:
  for -V: Data
  for key: String
  for item: Maybe<&2, V>
  for query: String
  for value: V
  for unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, MLeaf{key, item}, query, value)
  Empty
def fresh_impossible(V, key, item, query, value, unequal, member):
  (same, item_equal) = member
  Valid.unequal_distinct(query, key, unequal, same)

law splice_bit:
  for -V: Data
  for key: String
  for item: Maybe<&2, V>
  for rest: Map<&2, Maybe<&2, V>>
  for discriminator: Nat
  for bit: Bool
  for query: String
  for value: V
  for +unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, Map.ins.splice.bit(&2, Maybe<&2, V>, item, rest, discriminator, (key, bit)), query, value)
  L.leaf(V, rest, query, value)
def splice_bit(V, key, item, rest, discriminator, bit, query, value, unequal, member):
  match bit:
    case False{}:
      match member:
        case Inl{fresh}: Empty.absurd(L.leaf(V, rest, query, value), fresh_impossible(V, key, item, query, value, unequal, fresh))
        case Inr{old}: old
    case True{}:
      match member:
        case Inl{old}: old
        case Inr{fresh}: Empty.absurd(L.leaf(V, rest, query, value), fresh_impossible(V, key, item, query, value, unequal, fresh))

law splice:
  for -V: Data
  for +key: String
  for item: Maybe<&2, V>
  for rest: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for query: String
  for value: V
  for +unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, Map.ins.splice(&2, Maybe<&2, V>, discriminator, key, item, rest), query, value)
  L.leaf(V, rest, query, value)
def splice(V, key, item, rest, discriminator, query, value, unequal, member):
  splice_bit(V, key, item, rest, discriminator, I.route_bit(Map.bit(key, discriminator)), query, value, unequal, %I.route_shape(key, discriminator) : L.leaf(V, Map.ins.splice.bit(&2, Maybe<&2, V>, item, rest, discriminator, _), query, value) member)

law deep:
  for -V: Data
  for +key: String
  for +item: Maybe<&2, V>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for parent: Nat
  for bit: Bool
  for +query: String
  for +value: V
  for lp: L.leaf(V, Map.ins(&2, Maybe<&2, V>, lo, key, item, discriminator), query, value) -> L.leaf(V, lo, query, value)
  for hp: L.leaf(V, Map.ins(&2, Maybe<&2, V>, hi, key, item, discriminator), query, value) -> L.leaf(V, hi, query, value)
  for +unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, Map.ins.deep(&2, Maybe<&2, V>, item, lo, hi, discriminator, parent, (key, bit)), query, value)
  L.leaf(V, MNode{parent, lo, hi}, query, value)
def deep(V, key, item, lo, hi, discriminator, parent, bit, query, value, lp, hp, unequal, member):
  match bit:
    case False{}:
      match member:
        case Inl{old}: Inl{lp(old)}
        case Inr{old}: Inr{old}
    case True{}:
      match member:
        case Inl{old}: Inl{old}
        case Inr{old}: Inr{hp(old)}

law branch:
  for -V: Data
  for +key: String
  for +item: Maybe<&2, V>
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for +parent: Nat
  for descend: Bool
  for +query: String
  for +value: V
  for lp: L.leaf(V, Map.ins(&2, Maybe<&2, V>, lo, key, item, discriminator), query, value) -> L.leaf(V, lo, query, value)
  for hp: L.leaf(V, Map.ins(&2, Maybe<&2, V>, hi, key, item, discriminator), query, value) -> L.leaf(V, hi, query, value)
  for +unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, Map.ins.if(&2, Maybe<&2, V>, key, item, lo, hi, parent, discriminator, descend), query, value)
  L.leaf(V, MNode{parent, lo, hi}, query, value)
def branch(V, key, item, lo, hi, discriminator, parent, descend, query, value, lp, hp, unequal, member):
  match descend:
    case False{}: splice(V, key, item, MNode{parent, lo, hi}, discriminator, query, value, unequal, member)
    case True{}:
      deep(V, key, item, lo, hi, discriminator, parent, I.route_bit(Map.bit(key, parent)), query, value, lp, hp, unequal, %I.route_shape(key, parent) : L.leaf(V, Map.ins.deep(&2, Maybe<&2, V>, item, lo, hi, discriminator, parent, _), query, value) member)

law no_new_other_binding:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +discriminator: Nat
  for +query: String
  for +value: V
  for +unequal: {String.eq(query, key) == False{} : Bool}
  for member: L.leaf(V, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query, value)
  L.leaf(V, tree, query, value)
def no_new_other_binding(V, tree, key, item, discriminator, query, value, unequal, member):
  match tree:
    case MTip{}: fresh_impossible(V, key, item, query, value, unequal, member)
    case MLeaf{stored, old}:
      splice(V, key, item, MLeaf{stored, old}, discriminator, query, value, unequal, member)
    case MNode{+parent, +lo, +hi}:
      branch(V, key, item, lo, hi, discriminator, parent, Nat.is_lt(parent, discriminator), query, value,
        m => no_new_other_binding(V, lo, key, item, discriminator, query, value, unequal, m),
        m => no_new_other_binding(V, hi, key, item, discriminator, query, value, unequal, m), unequal, member)

