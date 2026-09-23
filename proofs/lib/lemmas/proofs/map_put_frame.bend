import Base
import ./map_insert.bend as I
import ./native_map.bend as N
import ./map_set_critbit.bend as Set
import ./map_routing.bend as R

law leaf_cmp:
  for -V: Data
  for +d: V
  for +query: String
  for +stored: String
  for old: V
  for item: V
  for c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(query, stored)) == c : Cmp}
  for unequal: {String.eq(query, stored) == False{} : Bool}
  {I.value(V, Map.get.leaf(V, d, item, ((query, stored), c))) == I.value(V, Map.get.leaf(V, d, old, ((query, stored), c))) : V}
def leaf_cmp(V, d, query, stored, old, item, c, compared, unequal):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      Empty.absurd({item == old : V}, R.false_true(Equal.trans(Bool, False{}, String.eq(query, stored), True{}, Equal.sym(Bool, String.eq(query, stored), False{}, unequal), Set.comparison_boolean(query, stored, EQ{}, compared))))

law leaf_frame:
  for -V: Data
  for +d: V
  for +query: String
  for +stored: String
  for +old: V
  for +item: V
  for unequal: {String.eq(query, stored) == False{} : Bool}
  {I.lookup(V, d, MLeaf{stored, item}, query) == I.lookup(V, d, MLeaf{stored, old}, query) : V}
def leaf_frame(V, d, query, stored, old, item, unequal):
  %Equal.sym((String & String) & Cmp, String.cmp(query, stored), ((query, stored), N.comparison_tag(String, String.cmp(query, stored))), N.string_comparison_shape(query, stored)) : {I.value(V, Map.get.leaf(V, d, item, _)) == I.value(V, Map.get.leaf(V, d, old, _)) : V}
  leaf_cmp(V, d, query, stored, old, item, N.comparison_tag(String, String.cmp(query, stored)), {==}, unequal)

law branch:
  for -V: Data
  for +d: V
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +key: String
  for +stored: String
  for +item: V
  for +query: String
  for kb: Bool
  for qb: Bool
  for +kr: {Map.bit(key, p) == (key, kb) : String & Bool}
  for +qr: {Map.bit(query, p) == (query, qb) : String & Bool}
  for selected: {I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)) == Some{stored} : Maybe<&2, String>}
  for left: {I.seek_found(V, Map.seek(&2, V, lo, key)) == Some{stored} : Maybe<&2, String>} -> {I.lookup(V, d, Map.put(&2, V, lo, key, item), query) == I.lookup(V, d, lo, query) : V}
  for right: {I.seek_found(V, Map.seek(&2, V, hi, key)) == Some{stored} : Maybe<&2, String>} -> {I.lookup(V, d, Map.put(&2, V, hi, key, item), query) == I.lookup(V, d, hi, query) : V}
  {I.lookup(V, d, Map.put(&2, V, MNode{p, lo, hi}, key, item), query) == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
def branch(V, d, p, lo, hi, key, stored, item, query, kb, qb, kr, qr, selected, left, right):
  match kb qb:
    case False{} False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), kr) : {I.lookup(V, d, Map.put.bit(&2, V, item, p, lo, hi, _), query) == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, Map.put(&2, V, lo, key, item), hi}, query), I.lookup(V, d, Map.put(&2, V, lo, key, item), query), I.node_left(V, d, Map.put(&2, V, lo, key, item), hi, p, query, qr)) : {_ == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, query), I.lookup(V, d, lo, query), I.node_left(V, d, lo, hi, p, query, qr)) : {I.lookup(V, d, Map.put(&2, V, lo, key, item), query) == _ : V}
      left(Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, lo, key)), I.seek_left(V, lo, hi, p, key, kr)), selected))
    case False{} True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), kr) : {I.lookup(V, d, Map.put.bit(&2, V, item, p, lo, hi, _), query) == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, Map.put(&2, V, lo, key, item), hi}, query), I.lookup(V, d, hi, query), I.node_right(V, d, Map.put(&2, V, lo, key, item), hi, p, query, qr)) : {_ == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, query), I.lookup(V, d, hi, query), I.node_right(V, d, lo, hi, p, query, qr)) : {I.lookup(V, d, hi, query) == _ : V}
      {==}
    case True{} False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), kr) : {I.lookup(V, d, Map.put.bit(&2, V, item, p, lo, hi, _), query) == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, Map.put(&2, V, hi, key, item)}, query), I.lookup(V, d, lo, query), I.node_left(V, d, lo, Map.put(&2, V, hi, key, item), p, query, qr)) : {_ == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, query), I.lookup(V, d, lo, query), I.node_left(V, d, lo, hi, p, query, qr)) : {I.lookup(V, d, lo, query) == _ : V}
      {==}
    case True{} True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), kr) : {I.lookup(V, d, Map.put.bit(&2, V, item, p, lo, hi, _), query) == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, Map.put(&2, V, hi, key, item)}, query), I.lookup(V, d, Map.put(&2, V, hi, key, item), query), I.node_right(V, d, lo, Map.put(&2, V, hi, key, item), p, query, qr)) : {_ == I.lookup(V, d, MNode{p, lo, hi}, query) : V}
      %Equal.sym(V, I.lookup(V, d, MNode{p, lo, hi}, query), I.lookup(V, d, hi, query), I.node_right(V, d, lo, hi, p, query, qr)) : {I.lookup(V, d, Map.put(&2, V, hi, key, item), query) == _ : V}
      right(Equal.trans(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), Some{stored}, Equal.sym(Maybe<&2, String>, I.seek_found(V, Map.seek(&2, V, MNode{p, lo, hi}, key)), I.seek_found(V, Map.seek(&2, V, hi, key)), I.seek_right(V, lo, hi, p, key, kr)), selected))

# The seek premise identifies the replaced leaf; no validity premise is needed.
law other_lookup_unchanged:
  for -V: Data
  for tree: Map<&2, V>
  for +d: V
  for +key: String
  for +stored: String
  for +item: V
  for +query: String
  for +unequal: {String.eq(query, stored) == False{} : Bool}
  for selected: {I.seek_found(V, Map.seek(&2, V, tree, key)) == Some{stored} : Maybe<&2, String>}
  {I.lookup(V, d, Map.put(&2, V, tree, key, item), query) == I.lookup(V, d, tree, query) : V}
def other_lookup_unchanged(V, tree, d, key, stored, item, query, unequal, selected):
  match tree:
    case MTip{}:
      Empty.absurd({I.lookup(V, d, MLeaf{key, item}, query) == d : V}, R.false_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{stored}, selected)))
    case MLeaf{+oldkey, +old}:
      same = Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, ""), Some{oldkey}, Some{stored}, selected)
      leaf_frame(V, d, query, oldkey, old, item, %Equal.sym(String, oldkey, stored, same) : {String.eq(query, _) == False{} : Bool} unequal)
    case MNode{+p, +lo, +hi}:
      branch(V, d, p, lo, hi, key, stored, item, query, I.route_bit(Map.bit(key, p)), I.route_bit(Map.bit(query, p)), I.route_shape(key, p), I.route_shape(query, p), selected, found => other_lookup_unchanged(V, lo, d, key, stored, item, query, unequal, found), found => other_lookup_unchanged(V, hi, d, key, stored, item, query, unequal, found))

law leaf_miss_cmp:
  for -V: Data
  for +d: V
  for +query: String
  for +stored: String
  for item: V
  for c: Cmp
  for compared: {N.comparison_tag(String, String.cmp(query, stored)) == c : Cmp}
  for unequal: {String.eq(query, stored) == False{} : Bool}
  {I.value(V, Map.get.leaf(V, d, item, ((query, stored), c))) == d : V}
def leaf_miss_cmp(V, d, query, stored, item, c, compared, unequal):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      Empty.absurd({item == d : V}, R.false_true(Equal.trans(Bool, False{}, String.eq(query, stored), True{}, Equal.sym(Bool, String.eq(query, stored), False{}, unequal), Set.comparison_boolean(query, stored, EQ{}, compared))))

law leaf_miss:
  for -V: Data
  for +d: V
  for +query: String
  for +stored: String
  for +item: V
  for unequal: {String.eq(query, stored) == False{} : Bool}
  {I.lookup(V, d, MLeaf{stored, item}, query) == d : V}
def leaf_miss(V, d, query, stored, item, unequal):
  %Equal.sym((String & String) & Cmp, String.cmp(query, stored), ((query, stored), N.comparison_tag(String, String.cmp(query, stored))), N.string_comparison_shape(query, stored)) : {I.value(V, Map.get.leaf(V, d, item, _)) == d : V}
  leaf_miss_cmp(V, d, query, stored, item, N.comparison_tag(String, String.cmp(query, stored)), {==}, unequal)
