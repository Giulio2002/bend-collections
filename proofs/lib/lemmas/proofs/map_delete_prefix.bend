import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./invariants.bend as Inv

# Deletion preserves every existing query/prefix constraint.
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
  for +query: String
  for +limit: Nat
  for left: {Inv.prefix_against(V, query, Map.del.fin(&2, V, r), limit) == True{} : Bool}
  for right: {Inv.prefix_against(V, query, hi, limit) == True{} : Bool}
  {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), limit) == True{} : Bool}
def low(V, p, hi, r, query, limit, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          right
        case MLeaf{+k, +v}:
          conjunction(Inv.same_prefix(query, k, limit), Inv.prefix_against(V, query, hi, limit), left, right)
        case MNode{+q, +lo, +other}:
          conjunction(Inv.prefix_against(V, query, MNode{q, lo, other}, limit), Inv.prefix_against(V, query, hi, limit), left, right)

law high:
  for -V: Data
  for p: Nat
  for +lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for +query: String
  for +limit: Nat
  for left: {Inv.prefix_against(V, query, lo, limit) == True{} : Bool}
  for right: {Inv.prefix_against(V, query, Map.del.fin(&2, V, r), limit) == True{} : Bool}
  {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), limit) == True{} : Bool}
def high(V, p, lo, r, query, limit, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          left
        case MLeaf{+k, +v}:
          conjunction(Inv.prefix_against(V, query, lo, limit), Inv.same_prefix(query, k, limit), left, right)
        case MNode{+q, +other, +hi}:
          conjunction(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, MNode{q, other, hi}, limit), left, right)

law leaf:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for c: Cmp
  for query: String
  for limit: Nat
  for route: {Inv.same_prefix(query, stored, limit) == True{} : Bool}
  {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), c))), limit) == True{} : Bool}
def leaf(V, value, key, stored, c, query, limit, route):
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
  for +query: String
  for +limit: Nat
  for left: {Inv.prefix_against(V, query, lo, limit) == True{} : Bool}
  for right: {Inv.prefix_against(V, query, hi, limit) == True{} : Bool}
  for lp: {Inv.prefix_against(V, query, lo, limit) == True{} : Bool} -> {Inv.prefix_against(V, query, Map.del(&2, V, lo, key), limit) == True{} : Bool}
  for hp: {Inv.prefix_against(V, query, hi, limit) == True{} : Bool} -> {Inv.prefix_against(V, query, Map.del(&2, V, hi, key), limit) == True{} : Bool}
  {Inv.prefix_against(V, query, Map.del(&2, V, MNode{p, lo, hi}, key), limit) == True{} : Bool}
def branch(V, lo, hi, p, key, bit, e, query, limit, left, right, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), limit) == True{} : Bool}
      low(V, p, hi, Map.pop(&2, V, lo, key), query, limit, lp(left), right)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), limit) == True{} : Bool}
      high(V, p, lo, Map.pop(&2, V, hi, key), query, limit, left, hp(right))

law preserves_prefix_against:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +query: String
  for +limit: Nat
  for +routes: {Inv.prefix_against(V, query, tree, limit) == True{} : Bool}
  {Inv.prefix_against(V, query, Map.del(&2, V, tree, key), limit) == True{} : Bool}
def preserves_prefix_against(V, tree, key, query, limit, routes):
  match tree:
    case MTip{}:
      {==}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Inv.prefix_against(V, query, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _)), limit) == True{} : Bool}
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)), query, limit, routes)
    case MNode{+p, +lo, +hi}:
      left = R.and_left(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), routes)
      right = R.and_right(Inv.prefix_against(V, query, lo, limit), Inv.prefix_against(V, query, hi, limit), routes)
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), query, limit, left, right, r => preserves_prefix_against(V, lo, key, query, limit, r), r => preserves_prefix_against(V, hi, key, query, limit, r))

