import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./invariants.bend as Inv
import ./map_delete_prefix.bend as P

# Deletion preserves every existing all-pairs row constraint.
# This law unfolds native pop, including collapsing an empty child.
law conjunction:
  for a: Bool
  for b: Bool
  for left: {a == True{} : Bool}
  for right: {b == True{} : Bool}
  {a && b == True{} : Bool}
def conjunction(a, b, left, right):
  %Equal.sym(Bool, a, True{}, left) : {_ && b == True{} : Bool}
  right

law low:
  for -V: Data
  for p: Nat
  for +hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for +whole: Map<&2, V>
  for +limit: Nat
  for left: {Inv.common_prefix(V, Map.del.fin(&2, V, r), whole, limit) == True{} : Bool}
  for right: {Inv.common_prefix(V, hi, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), whole, limit) == True{} : Bool}
def low(V, p, hi, r, whole, limit, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          right
        case MLeaf{+k, +v}:
          conjunction(Inv.prefix_against(V, k, whole, limit), Inv.common_prefix(V, hi, whole, limit), left, right)
        case MNode{+q, +lo, +other}:
          conjunction(Inv.common_prefix(V, MNode{q, lo, other}, whole, limit), Inv.common_prefix(V, hi, whole, limit), left, right)

law high:
  for -V: Data
  for p: Nat
  for +lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for +whole: Map<&2, V>
  for +limit: Nat
  for left: {Inv.common_prefix(V, lo, whole, limit) == True{} : Bool}
  for right: {Inv.common_prefix(V, Map.del.fin(&2, V, r), whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), whole, limit) == True{} : Bool}
def high(V, p, lo, r, whole, limit, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          left
        case MLeaf{+k, +v}:
          conjunction(Inv.common_prefix(V, lo, whole, limit), Inv.prefix_against(V, k, whole, limit), left, right)
        case MNode{+q, +other, +hi}:
          conjunction(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, MNode{q, other, hi}, whole, limit), left, right)

law leaf:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for c: Cmp
  for whole: Map<&2, V>
  for limit: Nat
  for route: {Inv.prefix_against(V, stored, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), c))), whole, limit) == True{} : Bool}
def leaf(V, value, key, stored, c, whole, limit, route):
  match c:
    case LT{}:
      route
    case EQ{}:
      {==}
    case GT{}:
      route

law branch:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for +whole: Map<&2, V>
  for +limit: Nat
  for left: {Inv.common_prefix(V, lo, whole, limit) == True{} : Bool}
  for right: {Inv.common_prefix(V, hi, whole, limit) == True{} : Bool}
  for lp: {Inv.common_prefix(V, lo, whole, limit) == True{} : Bool} -> {Inv.common_prefix(V, Map.del(&2, V, lo, key), whole, limit) == True{} : Bool}
  for hp: {Inv.common_prefix(V, hi, whole, limit) == True{} : Bool} -> {Inv.common_prefix(V, Map.del(&2, V, hi, key), whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del(&2, V, MNode{p, lo, hi}, key), whole, limit) == True{} : Bool}
def branch(V, lo, hi, p, key, bit, e, whole, limit, left, right, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), whole, limit) == True{} : Bool}
      low(V, p, hi, Map.pop(&2, V, lo, key), whole, limit, lp(left), right)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), whole, limit) == True{} : Bool}
      high(V, p, lo, Map.pop(&2, V, hi, key), whole, limit, left, hp(right))

law preserves_rows:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +whole: Map<&2, V>
  for +limit: Nat
  for +routes: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del(&2, V, tree, key), whole, limit) == True{} : Bool}
def preserves_rows(V, tree, key, whole, limit, routes):
  match tree:
    case MTip{}:
      {==}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Inv.common_prefix(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _)), whole, limit) == True{} : Bool}
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)), whole, limit, routes)
    case MNode{+p, +lo, +hi}:
      left = R.and_left(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), routes)
      right = R.and_right(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), routes)
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), whole, limit, left, right, r => preserves_rows(V, lo, key, whole, limit, r), r => preserves_rows(V, hi, key, whole, limit, r))


law preserves_columns:
  for -V: Data
  for tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +key: String
  for +limit: Nat
  for +proof: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, tree, Map.del(&2, V, whole, key), limit) == True{} : Bool}
def preserves_columns(V, tree, whole, key, limit, proof):
  match tree:
    case MTip{}: {==}
    case MLeaf{stored, value}:
      P.preserves_prefix_against(V, whole, key, stored, limit, proof)
    case MNode{p, +lo, +hi}:
      conjunction(Inv.common_prefix(V, lo, Map.del(&2, V, whole, key), limit), Inv.common_prefix(V, hi, Map.del(&2, V, whole, key), limit), preserves_columns(V, lo, whole, key, limit, R.and_left(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), proof)), preserves_columns(V, hi, whole, key, limit, R.and_right(Inv.common_prefix(V, lo, whole, limit), Inv.common_prefix(V, hi, whole, limit), proof)))

# Both quantified leaf domains shrink under actual Base.pop/del. No relation
# between the two input trees, and no validity premise, is needed for this fact.
law preserves_common_prefix:
  for -V: Data
  for +tree: Map<&2, V>
  for +whole: Map<&2, V>
  for +key: String
  for +limit: Nat
  for proof: {Inv.common_prefix(V, tree, whole, limit) == True{} : Bool}
  {Inv.common_prefix(V, Map.del(&2, V, tree, key), Map.del(&2, V, whole, key), limit) == True{} : Bool}
def preserves_common_prefix(V, tree, whole, key, limit, proof):
  preserves_rows(V, tree, key, Map.del(&2, V, whole, key), limit, preserves_columns(V, tree, whole, key, limit, proof))
