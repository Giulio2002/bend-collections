import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P
import ./map_populated.bend as Pop

# Deletion preserves the absence of stored None, including child collapse.
law low:
  for -V: Data
  for p: Nat
  for +hi: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for left: {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, r)) == True{} : Bool}
  for right: {Pop.populated(V, hi) == True{} : Bool}
  {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.lo(&2, Maybe<&2, V>, p, hi, r))) == True{} : Bool}
def low(V, p, hi, r, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          right
        case MLeaf{+k, +v}:
          P.conjunction(Maybe.is_some(&2, V, v), Pop.populated(V, hi), left, right)
        case MNode{+q, +lo, +other}:
          P.conjunction(Pop.populated(V, MNode{q, lo, other}), Pop.populated(V, hi), left, right)

law high:
  for -V: Data
  for p: Nat
  for +lo: Map<&2, Maybe<&2, V>>
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for left: {Pop.populated(V, lo) == True{} : Bool}
  for right: {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, r)) == True{} : Bool}
  {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.hi(&2, Maybe<&2, V>, p, lo, r))) == True{} : Bool}
def high(V, p, lo, r, left, right):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          left
        case MLeaf{+k, +v}:
          P.conjunction(Pop.populated(V, lo), Maybe.is_some(&2, V, v), left, right)
        case MNode{+q, +other, +hi}:
          P.conjunction(Pop.populated(V, lo), Pop.populated(V, MNode{q, other, hi}), left, right)

law leaf:
  for -V: Data
  for value: Maybe<&2, V>
  for key: String
  for stored: String
  for c: Cmp
  for route: {Maybe.is_some(&2, V, value) == True{} : Bool}
  {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, value, ((key, stored), c)))) == True{} : Bool}
def leaf(V, value, key, stored, c, route):
  match c:
    case LT{}:
      route
    case EQ{}:
      {==}
    case GT{}:
      route

law branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: Bool
  for e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for left: {Pop.populated(V, lo) == True{} : Bool}
  for right: {Pop.populated(V, hi) == True{} : Bool}
  for lp: {Pop.populated(V, lo) == True{} : Bool} -> {Pop.populated(V, Map.del(&2, Maybe<&2, V>, lo, key)) == True{} : Bool}
  for hp: {Pop.populated(V, hi) == True{} : Bool} -> {Pop.populated(V, Map.del(&2, Maybe<&2, V>, hi, key)) == True{} : Bool}
  {Pop.populated(V, Map.del(&2, Maybe<&2, V>, MNode{p, lo, hi}, key)) == True{} : Bool}
def branch(V, lo, hi, p, key, bit, e, left, right, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _))) == True{} : Bool}
      low(V, p, hi, Map.pop(&2, Maybe<&2, V>, lo, key), lp(left), right)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _))) == True{} : Bool}
      high(V, p, lo, Map.pop(&2, Maybe<&2, V>, hi, key), left, hp(right))

law preserves_populated:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +routes: {Pop.populated(V, tree) == True{} : Bool}
  {Pop.populated(V, Map.del(&2, Maybe<&2, V>, tree, key)) == True{} : Bool}
def preserves_populated(V, tree, key, routes):
  match tree:
    case MTip{}:
      {==}
    case MLeaf{+stored, +value}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {Pop.populated(V, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, value, _))) == True{} : Bool}
      leaf(V, value, key, stored, N.comparison_tag(String, String.cmp(key, stored)), routes)
    case MNode{+p, +lo, +hi}:
      left = R.and_left(Pop.populated(V, lo), Pop.populated(V, hi), routes)
      right = R.and_right(Pop.populated(V, lo), Pop.populated(V, hi), routes)
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), left, right, r => preserves_populated(V, lo, key, r), r => preserves_populated(V, hi, key, r))

