import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as R

# Deletion never introduces a key on the other side of ANY discriminator.
# This law unfolds native pop, including collapsing an empty child.
law low:
  for -V: Data
  for p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for +position: Nat
  for +side: Bool
  for left: R.routed(V, Map.del.fin(&2, V, r), position, side)
  for right: R.routed(V, hi, position, side)
  R.routed(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)), position, side)
def low(V, p, hi, r, position, side, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          right
        case MLeaf{k, v}:
          (left, right)
        case MNode{q, lo, other}:
          (left, right)

law high:
  for -V: Data
  for p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for +position: Nat
  for +side: Bool
  for left: R.routed(V, lo, position, side)
  for right: R.routed(V, Map.del.fin(&2, V, r), position, side)
  R.routed(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)), position, side)
def high(V, p, lo, r, position, side, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          left
        case MLeaf{k, v}:
          (left, right)
        case MNode{q, other, hi}:
          (left, right)

law leaf:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for c: Cmp
  for position: Nat
  for side: Bool
  for route: {Map.bit(stored, position) == (stored, side) : String & Bool}
  R.routed(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), c))), position, side)
def leaf(V, value, key, stored, c, position, side, route):
  match c:
    case LT{}:
      route
    case EQ{}:
      Unit{}
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
  for +position: Nat
  for +side: Bool
  for left: R.routed(V, lo, position, side)
  for right: R.routed(V, hi, position, side)
  for lp: R.routed(V, lo, position, side) -> R.routed(V, Map.del(&2, V, lo, key), position, side)
  for hp: R.routed(V, hi, position, side) -> R.routed(V, Map.del(&2, V, hi, key), position, side)
  R.routed(V, Map.del(&2, V, MNode{p, lo, hi}, key), position, side)
def branch(V, lo, hi, p, key, bit, e, position, side, left, right, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : R.routed(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), position, side)
      low(V, p, hi, Map.pop(&2, V, lo, key), position, side, lp(left), right)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : R.routed(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)), position, side)
      high(V, p, lo, Map.pop(&2, V, hi, key), position, side, left, hp(right))

law preserves_routing:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for +position: Nat
  for +side: Bool
  for routes: R.routed(V, tree, position, side)
  R.routed(V, Map.del(&2, V, tree, key), position, side)
def preserves_routing(V, tree, key, position, side, routes):
  match tree:
    case MTip{}:
      Unit{}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : R.routed(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _)), position, side)
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)), position, side, routes)
    case MNode{+p, +lo, +hi}:
      (left, right) = routes
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), position, side, left, right, r => preserves_routing(V, lo, key, position, side, r), r => preserves_routing(V, hi, key, position, side, r))

law low_valid:
  for -V: Data
  for +p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for lr: R.routed(V, Map.del.fin(&2, V, r), p, False{})
  for hr: R.routed(V, hi, p, True{})
  for lv: R.valid(V, Map.del.fin(&2, V, r))
  for hv: R.valid(V, hi)
  R.valid(V, Map.del.fin(&2, V, Map.pop.lo(&2, V, p, hi, r)))
def low_valid(V, p, hi, r, lr, hr, lv, hv):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          hv
        case MLeaf{k, v}:
          (lr, hr, lv, hv)
        case MNode{q, lo, other}:
          (lr, hr, lv, hv)

law high_valid:
  for -V: Data
  for +p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  for lr: R.routed(V, lo, p, False{})
  for hr: R.routed(V, Map.del.fin(&2, V, r), p, True{})
  for lv: R.valid(V, lo)
  for hv: R.valid(V, Map.del.fin(&2, V, r))
  R.valid(V, Map.del.fin(&2, V, Map.pop.hi(&2, V, p, lo, r)))
def high_valid(V, p, lo, r, lr, hr, lv, hv):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          lv
        case MLeaf{k, v}:
          (lr, hr, lv, hv)
        case MNode{q, other, hi}:
          (lr, hr, lv, hv)

law leaf_valid:
  for -V: Data
  for value: V
  for key: String
  for stored: String
  for c: Cmp
  R.valid(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, ((key, stored), c))))
def leaf_valid(V, value, key, stored, c):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Unit{}
    case GT{}:
      Unit{}

law branch_valid:
  for -V: Data
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lr: R.routed(V, lo, p, False{})
  for hr: R.routed(V, hi, p, True{})
  for lv: R.valid(V, lo)
  for hv: R.valid(V, hi)
  for lp: R.valid(V, lo) -> R.valid(V, Map.del(&2, V, lo, key))
  for hp: R.valid(V, hi) -> R.valid(V, Map.del(&2, V, hi, key))
  R.valid(V, Map.del(&2, V, MNode{p, lo, hi}, key))
def branch_valid(V, lo, hi, p, key, bit, e, lr, hr, lv, hv, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : R.valid(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)))
      low_valid(V, p, hi, Map.pop(&2, V, lo, key), preserves_routing(V, lo, key, p, False{}, lr), hr, lp(lv), hv)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : R.valid(V, Map.del.fin(&2, V, Map.pop.bit(&2, V, lo, hi, p, _)))
      high_valid(V, p, lo, Map.pop(&2, V, hi, key), lr, preserves_routing(V, hi, key, p, True{}, hr), lv, hp(hv))

# This preserves R.valid (the lookup-routing component), not the stronger
# Inv.critbit discriminator/prefix predicate. No insertion law is assumed.
law preserves_valid:
  for -V: Data
  for tree: Map<&2, V>
  for +key: String
  for valid: R.valid(V, tree)
  R.valid(V, Map.del(&2, V, tree, key))
def preserves_valid(V, tree, key, valid):
  match tree:
    case MTip{}:
      Unit{}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : R.valid(V, Map.del.fin(&2, V, Map.pop.leaf(&2, V, value, _)))
      leaf_valid(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)))
    case MNode{+p, +lo, +hi}:
      (lr, hr, lv, hv) = valid
      branch_valid(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), lr, hr, lv, hv, v => preserves_valid(V, lo, key, v), v => preserves_valid(V, hi, key, v))
