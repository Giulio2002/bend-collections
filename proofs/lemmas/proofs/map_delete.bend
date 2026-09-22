import Base
import ./map_insert.bend as I
import ./map_lookup.bend as L
import ./map_routing.bend as R
import ./invariants.bend as Inv
import ./native_map.bend as N

law different_sides:
  for side: Bool
  for e: {side == Bool.not(side) : Bool}
  Empty
def different_sides(side, e):
  match side:
    case False{}:
      R.false_true(e)
    case True{}:
      R.false_true(Equal.sym(Bool, True{}, False{}, e))

law opposite_routes:
  for +key: String
  for +pos: Nat
  for +side: Bool
  for a: {Map.bit(key, pos) == (key, side) : String & Bool}
  for b: {Map.bit(key, pos) == (key, Bool.not(side)) : String & Bool}
  Empty
def opposite_routes(key, pos, side, a, b):
  different_sides(side, Equal.trans(Bool, side, I.route_bit(Map.bit(key, pos)), Bool.not(side), Equal.sym(Bool, I.route_bit(Map.bit(key, pos)), side, Equal.cong(String & Bool, Bool, I.route_bit, Map.bit(key, pos), (key, side), a)), Equal.cong(String & Bool, Bool, I.route_bit, Map.bit(key, pos), (key, Bool.not(side)), b)))

law opposite_case:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for +pos: Nat
  for +side: Bool
  for routes: R.routed(Maybe<&2, V>, tree, pos, Bool.not(side))
  for bit: {Map.bit(key, pos) == (key, side) : String & Bool}
  for found: Maybe<&2, V>
  for result: {I.lookup(Maybe<&2, V>, None{}, tree, key) == found : Maybe<&2, V>}
  for member: L.certificate(V, tree, key, found)
  {I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}
def opposite_case(V, tree, key, pos, side, routes, bit, found, result, member):
  match found:
    case None{}:
      result
    case Some{value}:
      Empty.absurd({I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}, opposite_routes(key, pos, side, bit, R.member_routed(V, tree, key, value, pos, Bool.not(side), routes, member)))

law opposite_missing:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for pos: Nat
  for side: Bool
  for routes: R.routed(Maybe<&2, V>, tree, pos, Bool.not(side))
  for bit: {Map.bit(key, pos) == (key, side) : String & Bool}
  {I.lookup(Maybe<&2, V>, None{}, tree, key) == None{} : Maybe<&2, V>}
def opposite_missing(V, tree, key, pos, side, routes, bit):
  opposite_case(V, tree, key, pos, side, routes, bit, I.lookup(Maybe<&2, V>, None{}, tree, key), {==}, L.lookup_certificate(V, tree, key))

law collapse_low:
  for -V: Data
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: {Map.bit(key, p) == (key, False{}) : String & Bool}
  for routes: R.routed(Maybe<&2, V>, hi, p, True{})
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for absent: {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, r), key) == None{} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.lo(&2, Maybe<&2, V>, p, hi, r)), key) == None{} : Maybe<&2, V>}
def collapse_low(V, hi, p, key, bit, routes, r, absent):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          opposite_missing(V, hi, key, p, False{}, routes, bit)
        case MLeaf{+stored, +item}:
          Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, MLeaf{stored, item}, hi}, key), I.lookup(Maybe<&2, V>, None{}, MLeaf{stored, item}, key), None{}, I.node_left(Maybe<&2, V>, None{}, MLeaf{stored, item}, hi, p, key, bit), absent)
        case MNode{+q, +lo, +other}:
          Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, MNode{q, lo, other}, hi}, key), I.lookup(Maybe<&2, V>, None{}, MNode{q, lo, other}, key), None{}, I.node_left(Maybe<&2, V>, None{}, MNode{q, lo, other}, hi, p, key, bit), absent)

law collapse_high:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: {Map.bit(key, p) == (key, True{}) : String & Bool}
  for routes: R.routed(Maybe<&2, V>, lo, p, False{})
  for r: Map<&2, Maybe<&2, V>> & Maybe<&2, Maybe<&2, V>>
  for absent: {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, r), key) == None{} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.hi(&2, Maybe<&2, V>, p, lo, r)), key) == None{} : Maybe<&2, V>}
def collapse_high(V, lo, p, key, bit, routes, r, absent):
  match r:
    case Tuple{tree, found}:
      match tree:
        case MTip{}:
          opposite_missing(V, lo, key, p, True{}, routes, bit)
        case MLeaf{+stored, +item}:
          Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, MLeaf{stored, item}}, key), I.lookup(Maybe<&2, V>, None{}, MLeaf{stored, item}, key), None{}, I.node_right(Maybe<&2, V>, None{}, lo, MLeaf{stored, item}, p, key, bit), absent)
        case MNode{+q, +other, +hi}:
          Equal.trans(Maybe<&2, V>, I.lookup(Maybe<&2, V>, None{}, MNode{p, lo, MNode{q, other, hi}}, key), I.lookup(Maybe<&2, V>, None{}, MNode{q, other, hi}, key), None{}, I.node_right(Maybe<&2, V>, None{}, lo, MNode{q, other, hi}, p, key, bit), absent)

law leaf_case:
  for -V: Data
  for +item: Maybe<&2, V>
  for +key: String
  for +stored: String
  for cmp: Cmp
  for e: {String.cmp(key, stored) == ((key, stored), cmp) : (String & String) & Cmp}
  {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, ((key, stored), cmp))), key) == None{} : Maybe<&2, V>}
def leaf_case(V, item, key, stored, cmp, e):
  match cmp:
    case LT{}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), LT{}), e) : {I.value(Maybe<&2, V>, Map.get.leaf(Maybe<&2, V>, None{}, item, _)) == None{} : Maybe<&2, V>}
      {==}
    case EQ{}:
      {==}
    case GT{}:
      %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), GT{}), e) : {I.value(Maybe<&2, V>, Map.get.leaf(Maybe<&2, V>, None{}, item, _)) == None{} : Maybe<&2, V>}
      {==}

law leaf_delete:
  for -V: Data
  for +item: Maybe<&2, V>
  for +key: String
  for +stored: String
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, MLeaf{stored, item}, key), key) == None{} : Maybe<&2, V>}
def leaf_delete(V, item, key, stored):
  %Equal.sym((String & String) & Cmp, String.cmp(key, stored), ((key, stored), N.comparison_tag(String, String.cmp(key, stored))), N.string_comparison_shape(key, stored)) : {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.leaf(&2, Maybe<&2, V>, item, _)), key) == None{} : Maybe<&2, V>}
  leaf_case(V, item, key, stored, N.comparison_tag(String, String.cmp(key, stored)), N.string_comparison_shape(key, stored))

law branch:
  for -V: Data
  for +lo: Map<&2, Maybe<&2, V>>
  for +hi: Map<&2, Maybe<&2, V>>
  for +p: Nat
  for +key: String
  for bit: Bool
  for +e: {Map.bit(key, p) == (key, bit) : String & Bool}
  for lr: R.routed(Maybe<&2, V>, lo, p, False{})
  for hr: R.routed(Maybe<&2, V>, hi, p, True{})
  for lp: {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, lo, key), key) == None{} : Maybe<&2, V>}
  for hp: {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, hi, key), key) == None{} : Maybe<&2, V>}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, MNode{p, lo, hi}, key), key) == None{} : Maybe<&2, V>}
def branch(V, lo, hi, p, key, bit, e, lr, hr, lp, hp):
  match bit:
    case False{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, False{}), e) : {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key) == None{} : Maybe<&2, V>}
      collapse_low(V, hi, p, key, e, hr, Map.pop(&2, Maybe<&2, V>, lo, key), lp)
    case True{}:
      %Equal.sym(String & Bool, Map.bit(key, p), (key, True{}), e) : {I.lookup(Maybe<&2, V>, None{}, Map.del.fin(&2, Maybe<&2, V>, Map.pop.bit(&2, Maybe<&2, V>, lo, hi, p, _)), key) == None{} : Maybe<&2, V>}
      collapse_high(V, lo, p, key, e, lr, Map.pop(&2, Maybe<&2, V>, hi, key), hp)

law delete_same:
  for -V: Data
  for tree: Map<&2, Maybe<&2, V>>
  for +key: String
  for invariant: R.valid(Maybe<&2, V>, tree)
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, key), key) == None{} : Maybe<&2, V>}
def delete_same(V, tree, key, invariant):
  match tree:
    case MTip{}:
      {==}
    case MLeaf{stored, item}:
      leaf_delete(V, item, key, stored)
    case MNode{+p, +lo, +hi}:
      (lr, hr, lv, hv) = invariant
      branch(V, lo, hi, p, key, I.route_bit(Map.bit(key, p)), I.route_shape(key, p), lr, hr, delete_same(V, lo, key, lv), delete_same(V, hi, key, hv))

law critbit_delete_same:
  for -V: Data
  for +tree: Map<&2, Maybe<&2, V>>
  for key: String
  for invariant: {Inv.critbit(Maybe<&2, V>, tree) == True{} : Bool}
  {I.lookup(Maybe<&2, V>, None{}, Map.del(&2, Maybe<&2, V>, tree, key), key) == None{} : Maybe<&2, V>}
def critbit_delete_same(V, tree, key, invariant):
  delete_same(V, tree, key, R.critbit_certificate(Maybe<&2, V>, tree, invariant))
