import Base
import ./invariants.bend as Inv
import ./map_insert_critbit.bend as Valid
import ./map_routing.bend as R
import ./map_lookup.bend as L
import ./map_insert.bend as I

law splice_bit:
  for -V: Data
  for key: String
  for item: Maybe<&2, V>
  for rest: Map<&2, Maybe<&2, V>>
  for discriminator: Nat
  for bit: Bool
  for query: String
  for value: V
  for member: L.leaf(V, rest, query, value)
  L.leaf(V, Map.ins.splice.bit(&2, Maybe<&2, V>, item, rest, discriminator, (key, bit)), query, value)
def splice_bit(V, key, item, rest, discriminator, bit, query, value, member):
  match bit:
    case False{}: Inr{member}
    case True{}: Inl{member}

law splice:
  for -V: Data
  for +key: String
  for item: Maybe<&2, V>
  for rest: Map<&2, Maybe<&2, V>>
  for +discriminator: Nat
  for query: String
  for value: V
  for member: L.leaf(V, rest, query, value)
  L.leaf(V, Map.ins.splice(&2, Maybe<&2, V>, discriminator, key, item, rest), query, value)
def splice(V, key, item, rest, discriminator, query, value, member):
  %Equal.sym(String & Bool, Map.bit(key, discriminator), (key, I.route_bit(Map.bit(key, discriminator))), I.route_shape(key, discriminator)) : L.leaf(V, Map.ins.splice.bit(&2, Maybe<&2, V>, item, rest, discriminator, _), query, value)
  splice_bit(V, key, item, rest, discriminator, I.route_bit(Map.bit(key, discriminator)), query, value, member)

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
  for lp: L.leaf(V, lo, query, value) -> L.leaf(V, Map.ins(&2, Maybe<&2, V>, lo, key, item, discriminator), query, value)
  for hp: L.leaf(V, hi, query, value) -> L.leaf(V, Map.ins(&2, Maybe<&2, V>, hi, key, item, discriminator), query, value)
  for member: L.leaf(V, MNode{parent, lo, hi}, query, value)
  L.leaf(V, Map.ins.deep(&2, Maybe<&2, V>, item, lo, hi, discriminator, parent, (key, bit)), query, value)
def deep(V, key, item, lo, hi, discriminator, parent, bit, query, value, lp, hp, member):
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
  for lp: L.leaf(V, lo, query, value) -> L.leaf(V, Map.ins(&2, Maybe<&2, V>, lo, key, item, discriminator), query, value)
  for hp: L.leaf(V, hi, query, value) -> L.leaf(V, Map.ins(&2, Maybe<&2, V>, hi, key, item, discriminator), query, value)
  for member: L.leaf(V, MNode{parent, lo, hi}, query, value)
  L.leaf(V, Map.ins.if(&2, Maybe<&2, V>, key, item, lo, hi, parent, discriminator, descend), query, value)
def branch(V, key, item, lo, hi, discriminator, parent, descend, query, value, lp, hp, member):
  match descend:
    case False{}: splice(V, key, item, MNode{parent, lo, hi}, discriminator, query, value, member)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, parent), (key, I.route_bit(Map.bit(key, parent))), I.route_shape(key, parent)) : L.leaf(V, Map.ins.deep(&2, Maybe<&2, V>, item, lo, hi, discriminator, parent, _), query, value)
      deep(V, key, item, lo, hi, discriminator, parent, I.route_bit(Map.bit(key, parent)), query, value, lp, hp, member)

# Native insertion retains every existing exact key/value leaf, independently
# of discriminator validity. Lookup framing additionally needs tree validity.
law preserves_binding:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +item: Maybe<&2, V>
  for +discriminator: Nat
  for +query: String
  for +value: V
  for member: L.leaf(V, tree, query, value)
  L.leaf(V, Map.ins(&2, Maybe<&2, V>, tree, key, item, discriminator), query, value)
def preserves_binding(V, tree, key, item, discriminator, query, value, member):
  match tree:
    case MTip{}:
      Empty.absurd(L.leaf(V, MLeaf{key, item}, query, value), member)
    case MLeaf{stored, old}:
      splice(V, key, item, MLeaf{stored, old}, discriminator, query, value, member)
    case MNode{+parent, +lo, +hi}:
      branch(V, key, item, lo, hi, discriminator, parent, Nat.is_lt(parent, discriminator), query, value,
        m => preserves_binding(V, lo, key, item, discriminator, query, value, m),
        m => preserves_binding(V, hi, key, item, discriminator, query, value, m), member)


# Combine exact old binding preservation with the full native insertion
# validity theorem. All successful old lookups survive a genuine new-key insert.
law preserves_present_lookup:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +stored: String
  for +item: Maybe<&2, V>
  for +query: String
  for +value: V
  for unequal: {String.eq(key, stored) == False{} : Bool}
  for selected: {I.seek_found(Maybe<&2, V>, Map.seek(&2, Maybe<&2, V>, tree, key)) == Some{stored} : Maybe<&2, String>}
  for valid: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  for found: {I.lookup(Maybe<&2, V>, None{}, tree, query) == Some{value} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.ins(&2, Maybe<&2, V>, tree, key, item, Map.diff(key, stored)), query) == Some{value} : Maybe<&2, V>}
def preserves_present_lookup(V, tree, key, stored, item, query, value, unequal, selected, valid, found):
  R.critbit_member_lookup(V, Map.ins(&2, Maybe<&2, V>, tree, key, item, Map.diff(key, stored)), query, value,
    Valid.insertion_at_seek(Maybe<&2, V>, tree, key, stored, item, unequal, selected, valid),
    preserves_binding(V, tree, key, item, Map.diff(key, stored), query, value, L.returned_value_is_stored(V, tree, query, value, found)))
