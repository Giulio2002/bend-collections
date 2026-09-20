import Base
import ./map_insert.bend as I
import ./native_map.bend as N

# Observe the actual native deletion result, with the same explicit default as
# native get. No replacement deletion algorithm is defined here.
def result(-V: Data, r: Map<&2, V> & Maybe<&2, V>) -> Maybe<&2, V>:
  (tree, found) = r
  found

def observed(-V: Data, d: V, r: Map<&2, V> & Maybe<&2, V>) -> V:
  Maybe.default(&2, V, result(V, r), d)

law pop_low_value:
  for -V: Data
  for d: V
  for p: Nat
  for hi: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  {observed(V, d, Map.pop.lo(&2, V, p, hi, r)) == observed(V, d, r) : V}
def pop_low_value(V, d, p, hi, r):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          {==}
        case MLeaf{k, v}:
          {==}
        case MNode{q, lo, hi}:
          {==}

law pop_high_value:
  for -V: Data
  for d: V
  for p: Nat
  for lo: Map<&2, V>
  for r: Map<&2, V> & Maybe<&2, V>
  {observed(V, d, Map.pop.hi(&2, V, p, lo, r)) == observed(V, d, r) : V}
def pop_high_value(V, d, p, lo, r):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          {==}
        case MLeaf{k, v}:
          {==}
        case MNode{q, lo, hi}:
          {==}

law pop_left:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, False{}) : String & Bool}
  {observed(V, d, Map.pop(&2, V, MNode{p, lo, hi}, key)) == observed(V, d, Map.pop(&2, V, lo, key)) : V}
def pop_left(V, d, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {observed(V, d, Map.pop.bit(&2, V, lo, hi, p, _)) == observed(V, d, Map.pop(&2, V, lo, key)) : V}
  pop_low_value(V, d, p, hi, Map.pop(&2, V, lo, key))

law pop_right:
  for -V: Data
  for d: V
  for lo: Map<&2, V>
  for hi: Map<&2, V>
  for p: Nat
  for key: String
  for e: {Map.bit(key, p) == (key, True{}) : String & Bool}
  {observed(V, d, Map.pop(&2, V, MNode{p, lo, hi}, key)) == observed(V, d, Map.pop(&2, V, hi, key)) : V}
def pop_right(V, d, lo, hi, p, key, e):
  %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {observed(V, d, Map.pop.bit(&2, V, lo, hi, p, _)) == observed(V, d, Map.pop(&2, V, hi, key)) : V}
  pop_high_value(V, d, p, lo, Map.pop(&2, V, hi, key))

law leaf_result:
  for -V: Data
  for d: V
  for item: V
  for key: String
  for stored: String
  for cmp: Cmp
  {observed(V, d, Map.pop.leaf(&2, V, item, ((key, stored), cmp))) == I.value(V, Map.get.leaf(V, d, item, ((key, stored), cmp))) : V}
def leaf_result(V, d, item, key, stored, cmp):
  match cmp:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law leaf_lookup:
  for -V: Data
  for d: V
  for item: V
  for +key: String
  for +stored: String
  {observed(V, d, Map.pop(&2, V, MLeaf{stored, item}, key)) == I.lookup(V, d, MLeaf{stored, item}, key) : V}
def leaf_lookup(V, d, item, key, stored):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {observed(V, d, Map.pop.leaf(&2, V, item, _)) == I.value(V, Map.get.leaf(V, d, item, _)) : V}
  leaf_result(V, d, item, key, stored, N.comparison_tag(String, String.cmp(key, stored)))

law branch:
  for -V: Data
  for +d: V
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +p: Nat
  for +key: String
  for bit: Bool
  for +e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lp: {observed(V, d, Map.pop(&2, V, lo, key)) == I.lookup(V, d, lo, key) : V}
  for hp: {observed(V, d, Map.pop(&2, V, hi, key)) == I.lookup(V, d, hi, key) : V}
  {observed(V, d, Map.pop(&2, V, MNode{p, lo, hi}, key)) == I.lookup(V, d, MNode{p, lo, hi}, key) : V}
def branch(V, d, lo, hi, p, key, bit, e, lp, hp):
  match bit:
    case False{}:
      Equal.trans(V, observed(V, d, Map.pop(&2, V, MNode{p, lo, hi}, key)), observed(V, d, Map.pop(&2, V, lo, key)), I.lookup(V, d, MNode{p, lo, hi}, key), pop_left(V, d, lo, hi, p, key, e), Equal.trans(V, observed(V, d, Map.pop(&2, V, lo, key)), I.lookup(V, d, lo, key), I.lookup(V, d, MNode{p, lo, hi}, key), lp, Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, key), I.lookup(V, d, lo, key), I.node_left(V, d, lo, hi, p, key, e))))
    case True{}:
      Equal.trans(V, observed(V, d, Map.pop(&2, V, MNode{p, lo, hi}, key)), observed(V, d, Map.pop(&2, V, hi, key)), I.lookup(V, d, MNode{p, lo, hi}, key), pop_right(V, d, lo, hi, p, key, e), Equal.trans(V, observed(V, d, Map.pop(&2, V, hi, key)), I.lookup(V, d, hi, key), I.lookup(V, d, MNode{p, lo, hi}, key), hp, Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, key), I.lookup(V, d, hi, key), I.node_right(V, d, lo, hi, p, key, e))))

# Exact returned-value correspondence for arbitrary native trees. Remaining-tree
# deletion and frame properties are separate obligations, not conclusions here.
law popped_value_matches_lookup:
  for -V: Data
  for +d: V
  for tree: Map<&2, V>
  for +key: String
  {observed(V, d, Map.pop(&2, V, tree, key)) == I.lookup(V, d, tree, key) : V}
def popped_value_matches_lookup(V, d, tree, key):
  match tree:
    case MTip{}:
      {==}
    case MLeaf{stored, item}:
      leaf_lookup(V, d, item, key, stored)
    case MNode{+p, +lo, +hi}:
      branch(V, d, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), popped_value_matches_lookup(V, d, lo, key), popped_value_matches_lookup(V, d, hi, key))
