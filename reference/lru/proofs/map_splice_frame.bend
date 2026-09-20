import Base
import ./native_map.bend as N
import ./map_insert.bend as I
import ./map_difference.bend as D
import ./map_routing.bend as Logic

# Frame law for the actual insertion splice. The query can be present or absent
# in an arbitrary rest tree. No alternative lookup is defined here.
law opposite_branch:
  for -V: Data
  for +fallback: V
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for +key: String
  for +query: String
  for inserted: Bool
  for queried: Bool
  for different: {Bool.xor(inserted, queried) == True{} : Bool}
  for route: {Map.bit(query, position) == (query, queried) : String & Bool}
  {I.lookup(V, fallback, Map.ins.splice.bit(&2, V, value, rest, position, (key, inserted)), query) == I.lookup(V, fallback, rest, query) : V}
def opposite_branch(V, fallback, value, rest, position, key, query, inserted, queried, different, route):
  match inserted queried:
    case False{} False{}:
      Empty.absurd({I.lookup(V, fallback, MNode{position, MLeaf{key, value}, rest}, query) == I.lookup(V, fallback, rest, query) : V}, Logic.false_true(different))
    case False{} True{}:
      I.node_right(V, fallback, MLeaf{key, value}, rest, position, query, route)
    case True{} False{}:
      I.node_left(V, fallback, rest, MLeaf{key, value}, position, query, route)
    case True{} True{}:
      Empty.absurd({I.lookup(V, fallback, MNode{position, rest, MLeaf{key, value}}, query) == I.lookup(V, fallback, rest, query) : V}, Logic.false_true(different))

law splice_frame:
  for -V: Data
  for +fallback: V
  for +value: V
  for +rest: Map<&2, V>
  for +position: Nat
  for +key: String
  for +query: String
  for different: {Bool.xor(I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(query, position))) == True{} : Bool}
  {I.lookup(V, fallback, Map.ins.splice(&2, V, position, key, value, rest), query) == I.lookup(V, fallback, rest, query) : V}
def splice_frame(V, fallback, value, rest, position, key, query, different):
  %Equal.sym(String & Bool, Map.bit(key, position), (key, I.route_bit(Map.bit(key, position))), I.route_shape(key, position)) : {I.lookup(V, fallback, Map.ins.splice.bit(&2, V, value, rest, position, _), query) == I.lookup(V, fallback, rest, query) : V}
  opposite_branch(V, fallback, value, rest, position, key, query, I.route_bit(Map.bit(key, position)), I.route_bit(Map.bit(query, position)), different, I.route_shape(query, position))

# Discharge the discriminator premise from native Map.diff, rather than assuming
# the desired frame result. This is splice correctness, not full Map.set framing.
law difference_splice_frame:
  for -V: Data
  for fallback: V
  for value: V
  for rest: Map<&2, V>
  for +key: String
  for +query: String
  for different: D.different(key, query)
  {I.lookup(V, fallback, Map.ins.splice(&2, V, Map.diff(key, query), key, value, rest), query) == I.lookup(V, fallback, rest, query) : V}
def difference_splice_frame(V, fallback, value, rest, key, query, different):
  splice_frame(V, fallback, value, rest, Map.diff(key, query), key, query, D.native_difference(key, query, different))

# The first nontrivial public update frame: insert a distinct key into a
# singleton and retain the old value. Comparison and discriminator premises
# are discharged against Base, with no finite key-domain restriction.
law singleton_comparison:
  for -V: Data
  for +fallback: V
  for +old: V
  for +value: V
  for +key: String
  for +query: String
  for tag: Cmp
  for compared: {N.comparison_tag(String, String.cmp(key, query)) == tag : Cmp}
  for distinct: D.different(key, query)
  {I.lookup(V, fallback, Map.set.fin.go(&2, V, MLeaf{query, old}, key, value, ((key, query), tag)), query) == old : V}
def singleton_comparison(V, fallback, old, value, key, query, tag, compared, distinct):
  match tag:
    case EQ{}:
      Empty.absurd({I.lookup(V, fallback, Map.put(&2, V, MLeaf{query, old}, key, value), query) == old : V}, distinct(N.string_equal_from_comparison(key, query, compared)))
    case LT{}:
      Equal.trans(V, I.lookup(V, fallback, Map.ins.splice(&2, V, Map.diff(key, query), key, value, MLeaf{query, old}), query), I.lookup(V, fallback, MLeaf{query, old}, query), old, difference_splice_frame(V, fallback, value, MLeaf{query, old}, key, query, distinct), I.leaf_same(V, fallback, query, old))
    case GT{}:
      Equal.trans(V, I.lookup(V, fallback, Map.ins.splice(&2, V, Map.diff(key, query), key, value, MLeaf{query, old}), query), I.lookup(V, fallback, MLeaf{query, old}, query), old, difference_splice_frame(V, fallback, value, MLeaf{query, old}, key, query, distinct), I.leaf_same(V, fallback, query, old))

law singleton_set_other:
  for -V: Data
  for fallback: V
  for +old: V
  for value: V
  for +key: String
  for +query: String
  for distinct: D.different(key, query)
  {I.lookup(V, fallback, Map.set(&2, V, MLeaf{query, old}, key, value), query) == old : V}
def singleton_set_other(V, fallback, old, value, key, query, distinct):
  %Equal.sym((String & String) & Cmp, String.cmp(key, query), ((key, query), N.comparison_tag(String, String.cmp(key, query))), N.string_comparison_shape(key, query)) : {I.lookup(V, fallback, Map.set.fin.go(&2, V, MLeaf{query, old}, key, value, _), query) == old : V}
  singleton_comparison(V, fallback, old, value, key, query, N.comparison_tag(String, String.cmp(key, query)), {==}, distinct)
