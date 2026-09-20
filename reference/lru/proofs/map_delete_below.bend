import Base
import ./invariants.bend as Inv
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_difference_order.bend as O
import ./map_string_prefix.bend as Prefix
import ./recency_bounds.bend as Bounds
import ./map_critbit_parts.bend as Parts

law strict_transitive:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}
def strict_transitive(a, b, c, ab, bc):
  Prefix.predecessor_less(a, c, Bounds.le_transitive(1n+a, b, c, O.strict_successor(a, b, ab), O.less_is_le(b, c, bc)))

law lower_parent:
  for -V: Data
  for tree: Map<&2, V>
  for +parent: Nat
  for +p: Nat
  for lower: {Nat.is_lt(parent, p) == True{} : Bool}
  for below: {Inv.below(V, tree, p) == True{} : Bool}
  {Inv.below(V, tree, parent) == True{} : Bool}
def lower_parent(V, tree, parent, p, lower, below):
  match tree:
    case MTip{}: {==}
    case MLeaf{k, v}: {==}
    case MNode{q, lo, hi}: strict_transitive(parent, p, q, lower, below)

law low:
  for -V: Data
  for +p: Nat
  for +parent: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for lower: {Nat.is_lt(parent, p) == True{} : Bool}
  for below: {Inv.below(V, hi, p) == True{} : Bool}
  {Inv.below(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), parent) == True{} : Bool}
def low(V, p, parent, hi, r, lower, below):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}: lower_parent(V, hi, parent, p, lower, below)
        case MLeaf{k, v}: lower
        case MNode{q, lo, other}: lower

law high:
  for -V: Data
  for +p: Nat
  for +parent: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for lower: {Nat.is_lt(parent, p) == True{} : Bool}
  for below: {Inv.below(V, lo, p) == True{} : Bool}
  {Inv.below(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), parent) == True{} : Bool}
def high(V, p, parent, lo, r, lower, below):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}: lower_parent(V, lo, parent, p, lower, below)
        case MLeaf{k, v}: lower
        case MNode{q, other, hi}: lower

law leaf:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for tag: Cmp
  for parent: Nat
  {Inv.below(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), tag))), parent) == True{} : Bool}
def leaf(V, value, key, stored, tag, parent):
  match tag:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law branch:
  for -V: Data
  for +p: Nat
  for +parent: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for bit: Bool
  for route: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lower: {Nat.is_lt(parent, p) == True{} : Bool}
  for left: {Inv.below(V, lo, p) == True{} : Bool}
  for right: {Inv.below(V, hi, p) == True{} : Bool}
  {Inv.below(V, Map.del(&2, V, MNode{p, lo, hi}, key), parent) == True{} : Bool}
def branch(V, p, parent, lo, hi, key, bit, route, lower, left, right):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), route) : {Inv.below(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), parent) == True{} : Bool}
      low(V, p, parent, hi, Map.pop(&2, V, lo, key), lower, right)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), route) : {Inv.below(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), parent) == True{} : Bool}
      high(V, p, parent, lo, Map.pop(&2, V, hi, key), lower, left)

law from_parts:
  for -V: Data
  for +p: Nat
  for +parent: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for below: {Nat.is_lt(parent, p) == True{} : Bool}
  for parts: Parts.NodeFacts(V, p, lo, hi)
  {Inv.below(V, Map.del(&2, V, MNode{p, lo, hi}, key), parent) == True{} : Bool}
def from_parts(V, p, parent, lo, hi, key, below, parts):
  (prefix, ln, hn, lb, hb, lr, hr, lv, hv) = parts
  branch(V, p, parent, lo, hi, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), below, lb, hb)

# Native deletion either retains the root discriminator or promotes the untouched
# sibling. The sibling's ordering is derived from the actual critbit predicate.
law preserves_below:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +parent: Nat
  for valid: {Inv.critbit(V, tree) == True{} : Bool}
  for below: {Inv.below(V, tree, parent) == True{} : Bool}
  {Inv.below(V, Map.del(&2, V, tree, key), parent) == True{} : Bool}
def preserves_below(V, tree, key, parent, valid, below):
  match tree:
    case MTip{}: {==}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Inv.below(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _)), parent) == True{} : Bool}
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)), parent)
    case MNode{+p, +lo, +hi}:
      from_parts(V, p, parent, lo, hi, key, below, Parts.node_parts(V, p, lo, hi, valid))
